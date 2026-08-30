#!/usr/bin/env python3
"""
Site audit tool for WordPress / Elementor sites.

Crawls internal pages starting from the homepage (respecting robots.txt,
rate-limited to ~1 request/second, capped at MAX_PAGES), inspects each page
for performance, SEO, structural, mobile/UX, booking/conversion, tracking and
passive security-hygiene issues, pulls real-world Core Web Vitals from
Google's PageSpeed Insights API, and renders a color-coded PDF report with a
"Fix These First" quick-wins page and an Impact x Effort matrix.

Two modes:

    report  Deep single-site audit - crawl, PageSpeed, PDF report.
            python audit.py report --url https://example.com [--out PATH]

    screen  Fast triage across many sites - homepage only, no crawl, no PDF.
            Writes one CSV row per business, ranked by finding count, for
            cold outreach prioritization.
            python audit.py screen --csv prospects.csv [--out results.csv] [--psi]
            python audit.py screen --url https://example.com

A URL is always required - there is no default site. Reports are written to
site_audit_report_<domain>_<YYYY-MM-DD>.pdf unless an explicit output path is
given, so re-running for a client never overwrites a report already sent.

Environment variables:
    PAGESPEED_API_KEY - optional. Without one, PageSpeed Insights runs on
        Google's free unauthenticated tier, which is heavily rate-limited.
        Register a free key at:
        https://developers.google.com/speed/docs/insights/v5/get-started
    PLACES_API_KEY - optional, for screen mode's website lookup of businesses
        with a blank website column. Falls back to PAGESPEED_API_KEY. Billed
        per request, so lookups are cached and capped by --max-lookups.
"""

import argparse
import csv
import hashlib
import json
import logging
import os
import pickle
import re
import shutil
import socket
import ssl
import sys
import threading
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from urllib.parse import urljoin, urlparse, urldefrag
from urllib.robotparser import RobotFileParser

import requests
from bs4 import BeautifulSoup
from fpdf import FPDF

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

MAX_PAGES = 50
RATE_LIMIT_SECONDS = 1.0
REQUEST_TIMEOUT = 15
MAX_LINK_CHECKS = 150          # cap on total broken-link HEAD/GET checks
MAX_IMAGE_CHECKS_PER_PAGE = 4  # cap on per-page image size checks
OUTPUT_PDF_TEMPLATE = "site_audit_report_{domain}_{date}.pdf"
                                 # per-domain and dated, so re-auditing a client
                                 # never silently overwrites a report already sent

# Screen mode (fast multi-site triage)
SCREEN_TIMEOUT = 10            # per-request cap, keeps the per-site budget under 10s
MAX_PLACES_LOOKUPS = 250       # guardrail: Places Text Search is billed per request
PLACES_CACHE_FILE = "places_cache.json"
PLACES_CACHE_TTL_SECONDS = 60 * 60 * 24 * 30  # 30 days
PLACES_API_URL = "https://places.googleapis.com/v1/places:searchText"
PLACES_API_KEY = (os.environ.get("PLACES_API_KEY", "").strip()
                   or os.environ.get("PAGESPEED_API_KEY", "").strip())
SCREEN_CSV_COLUMNS = [
    "name", "website", "platform", "page_builder", "findings_count", "findings",
    "psi_mobile_score", "psi_mobile_lcp", "error",
    # blank columns filled in by hand during outreach
    "contacted", "channel", "replied", "call_booked", "closed", "objection",
]
SCREEN_MANUAL_COLUMNS = ["contacted", "channel", "replied", "call_booked", "closed", "objection"]
# host[:port] - permissive enough for IDNs and odd TLDs, strict enough to
# reject the free-text junk that ends up in a scraped prospect list
HOSTNAME_RE = re.compile(r"^[^\s/?#@:]+(:\d+)?$")
STATE_FILE_TEMPLATE = "audit_state_{domain}.pkl"
                                 # checkpoint of crawl_data + auto-detected issues,
                                 # so the PDF can be rebuilt (e.g. to add manual
                                 # findings) without re-crawling or re-hitting PSI.
                                 # Named per-domain, and the audited base_url is
                                 # stored inside and re-checked on load, so a
                                 # checkpoint can never be applied to another site.
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) SiteAuditBot/1.0 "
    "(+https://github.com/; automated site health audit)"
)

BOOKING_KEYWORDS = ["momence", "vagaro"]
CHECKOUT_DOMAINS = ["momence.com", "vagaro.com", "checkout.stripe.com", "square.site", "squareup.com"]
CTA_KEYWORDS = [
    "book now", "book a", "schedule", "sign up", "signup", "join now",
    "get started", "buy now", "register", "reserve", "enroll", "purchase",
    "shop now", "learn more", "contact us",
]

SEVERITY_ORDER = {"High": 0, "Medium": 1, "Low": 2}
SEVERITY_COLOR = {
    "High": (198, 40, 40),
    "Medium": (239, 108, 0),
    "Low": (46, 125, 50),
}
SEVERITY_COLOR_LIGHT = {
    "High": (253, 226, 226),
    "Medium": (255, 235, 205),
    "Low": (223, 240, 224),
}

# --- Effort tagging / quick-wins scoring ----------------------------------
EFFORT_ORDER = {"Quick": 0, "Moderate": 1, "Involved": 2}
# Rough hour ranges used only to produce a scoping estimate, per issue TYPE
# (not per page instance) - fixing one issue type once usually covers every
# affected page in a single pass (a template/plugin-level change).
EFFORT_HOURS = {"Quick": (0.1, 0.3), "Moderate": (0.5, 1.5), "Involved": (3, 10)}
IMPACT_WEIGHT = {"High": 3, "Medium": 2, "Low": 1}
EFFORT_WEIGHT = {"Quick": 1, "Moderate": 2.5, "Involved": 6}

# --- Real Core Web Vitals via Google PageSpeed Insights v5 ----------------
PAGESPEED_API_URL = "https://www.googleapis.com/pagespeedonline/v5/runPagespeed"
PAGESPEED_API_KEY = os.environ.get("PAGESPEED_API_KEY", "").strip()
PAGESPEED_CACHE_FILE = "pagespeed_cache.json"
PAGESPEED_CACHE_TTL_SECONDS = 7 * 24 * 3600  # don't re-hit the API every run
PAGESPEED_STRATEGIES = ("mobile", "desktop")
# A full Lighthouse run through this API commonly takes 30-60+ seconds per
# call (mobile especially, since it simulates network/CPU throttling) - a
# short timeout here reads as a "failure" and falsely trips the circuit
# breaker even though the API is working fine, just slow.
PAGESPEED_TIMEOUT = 150
PAGESPEED_CONCURRENCY = 6                # concurrent in-flight PSI requests
PAGESPEED_MAX_CONSECUTIVE_FAILURES = 4   # circuit breaker for genuine failures (bad key, quota, etc.)
PAGESPEED_MAX_PAGES = 25                 # safety cap, separate from MAX_PAGES
PAGESPEED_MAX_TOTAL_SECONDS = 900        # overall wall-clock budget (15 min)

# --- Passive security hygiene ----------------------------------------------
SECURITY_HEADERS = {
    "Strict-Transport-Security": "HSTS",
    "X-Content-Type-Options": "X-Content-Type-Options",
    "X-Frame-Options": "X-Frame-Options",
    "Content-Security-Policy": "CSP",
}
SSL_EXPIRY_WARN_DAYS = 30

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("audit")


# --------------------------------------------------------------------------
# Data structures
# --------------------------------------------------------------------------

@dataclass
class Issue:
    category: str
    issue: str
    severity: str
    effort: str
    why: str
    solutions: list
    pages: list = field(default_factory=list)


@dataclass
class PageSpeedResult:
    strategy: str
    performance_score: float = None
    lcp_ms: float = None
    lcp_display: str = ""
    cls: float = None
    inp_ms: float = None
    used_inp: bool = False
    tbt_ms: float = None
    opportunities: list = field(default_factory=list)
    error: str = ""


@dataclass
class PageData:
    url: str
    status_code: int = 0
    ok: bool = False
    load_time: float = 0.0
    size_bytes: int = 0
    title: str = ""
    meta_description: str = ""
    h1_count: int = 0
    h1_texts: list = field(default_factory=list)
    images_total: int = 0
    images_missing_alt: int = 0
    images_missing_dims: int = 0
    images_missing_lazy: int = 0
    image_srcs: list = field(default_factory=list)
    script_srcs: list = field(default_factory=list)
    render_blocking_scripts: int = 0
    total_scripts: int = 0
    internal_links: set = field(default_factory=set)
    external_links: set = field(default_factory=set)
    inline_style_chars: int = 0
    style_tag_chars: int = 0
    has_viewport: bool = False
    header_count: int = 0
    nav_count: int = 0
    footer_count: int = 0
    duplicate_nav_blocks: int = 0
    content_hash: str = ""
    text_len: int = 0
    has_gtm: bool = False
    gtm_count: int = 0
    has_meta_pixel: bool = False
    pixel_count: int = 0
    has_ga4: bool = False
    momence_hits: int = 0
    vagaro_hits: int = 0
    offsite_checkout_links: set = field(default_factory=set)
    has_cta: bool = False
    fixed_width_inline_count: int = 0
    headers: dict = field(default_factory=dict)
    version_disclosure: dict = field(default_factory=dict)
    psi: dict = field(default_factory=dict)  # strategy -> PageSpeedResult


# --------------------------------------------------------------------------
# Rate-limited HTTP session
# --------------------------------------------------------------------------

class RateLimiter:
    """Ensures every request made through this process is spaced at least
    `delay` seconds apart, regardless of destination."""

    def __init__(self, delay):
        self.delay = delay
        self._last = 0.0

    def wait(self):
        elapsed = time.monotonic() - self._last
        remaining = self.delay - elapsed
        if remaining > 0:
            time.sleep(remaining)
        self._last = time.monotonic()


limiter = RateLimiter(RATE_LIMIT_SECONDS)
session = requests.Session()
session.headers.update({"User-Agent": USER_AGENT})


def classify_request_error(exc):
    """Map a requests exception to a short, human-readable cause.

    Screen mode reports these verbatim in its CSV across hundreds of sites, so
    "DNS did not resolve" and "connection timed out" need to stay distinct
    rather than collapsing into one generic failure string."""
    if isinstance(exc, requests.exceptions.ConnectTimeout):
        return "connection timed out"
    if isinstance(exc, requests.exceptions.ReadTimeout):
        return "server accepted the connection but never responded"
    if isinstance(exc, requests.exceptions.Timeout):
        return "timed out"
    if isinstance(exc, requests.exceptions.SSLError):
        return "SSL/TLS error (bad or expired certificate)"
    if isinstance(exc, requests.exceptions.TooManyRedirects):
        return "redirect loop"
    if isinstance(exc, requests.exceptions.InvalidURL):
        return "malformed URL"
    if isinstance(exc, requests.exceptions.ConnectionError):
        text = str(exc)
        if "NameResolutionError" in text or "getaddrinfo failed" in text or "Name or service not known" in text:
            return "domain does not resolve (DNS)"
        if "ConnectTimeoutError" in text or "timed out" in text:
            return "connection timed out"
        if "RemoteDisconnected" in text or "ConnectionResetError" in text or "reset by peer" in text:
            return "connection reset by server"
        if "refused" in text:
            return "connection refused"
        return "could not connect"
    return f"{type(exc).__name__}"


def safe_get(url, method="GET", return_error=False, **kwargs):
    """Rate-limited, exception-safe HTTP request.

    Returns a Response or None. With return_error=True returns
    (response_or_None, error_string) so callers that surface failures to a
    human can say why; the default single-value contract is unchanged."""
    limiter.wait()
    try:
        kwargs.setdefault("timeout", REQUEST_TIMEOUT)
        kwargs.setdefault("allow_redirects", True)
        if method == "HEAD":
            resp = session.head(url, **kwargs)
            # Some servers don't implement HEAD properly; fall back to GET.
            if resp.status_code >= 400 or "content-length" not in resp.headers:
                limiter.wait()
                resp = session.get(url, stream=True, **kwargs)
        else:
            resp = session.get(url, **kwargs)
        return (resp, "") if return_error else resp
    except requests.exceptions.RequestException as exc:
        log.warning("Request failed for %s: %s", url, exc)
        return (None, classify_request_error(exc)) if return_error else None


# --------------------------------------------------------------------------
# Crawler
# --------------------------------------------------------------------------

def normalize_url(url):
    url, _frag = urldefrag(url)
    parsed = urlparse(url)
    path = parsed.path or "/"
    if len(path) > 1 and path.endswith("/"):
        path = path.rstrip("/")
    normalized = parsed._replace(path=path, fragment="").geturl()
    return normalized


def same_domain(url, base_netloc):
    try:
        return urlparse(url).netloc.replace("www.", "") == base_netloc.replace("www.", "")
    except ValueError:
        return False


def domain_key(url):
    """Stable per-site key used to name state checkpoints and to look up
    manual findings - the netloc, www-insensitive and lowercased, matching
    same_domain() above. Keeps one site's cached crawl and hand-written
    findings from ever being applied to another site."""
    key = urlparse(url).netloc.replace("www.", "").lower()
    return re.sub(r"[^a-z0-9.\-]", "_", key)


SKIP_EXTENSIONS = (
    ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".pdf", ".zip",
    ".mp4", ".mp3", ".doc", ".docx", ".xls", ".xlsx", ".css", ".js",
    ".woff", ".woff2", ".ttf", ".ico", ".xml",
)


def is_crawlable(url):
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https"):
        return False
    lower = parsed.path.lower()
    if lower.endswith(SKIP_EXTENSIONS):
        return False
    return True


def load_robots(base_url):
    parsed = urlparse(base_url)
    robots_url = f"{parsed.scheme}://{parsed.netloc}/robots.txt"
    rp = RobotFileParser()
    resp = safe_get(robots_url)
    if resp is not None and resp.status_code == 200:
        rp.parse(resp.text.splitlines())
        log.info("Loaded robots.txt (%d rules parsed)", len(resp.text.splitlines()))
        return rp, True
    log.info("No robots.txt found (or failed to fetch) - proceeding without restrictions")
    rp.parse([])
    return rp, False


def check_sitemap(base_url):
    parsed = urlparse(base_url)
    candidates = [
        f"{parsed.scheme}://{parsed.netloc}/sitemap.xml",
        f"{parsed.scheme}://{parsed.netloc}/sitemap_index.xml",
    ]
    for candidate in candidates:
        resp = safe_get(candidate)
        if resp is not None and resp.status_code == 200 and "xml" in resp.headers.get("content-type", "").lower() + resp.text[:200].lower():
            return True, candidate
    return False, candidates[0]


def extract_hash(tag):
    if tag is None:
        return None
    return hashlib.sha1(str(tag).encode("utf-8", "ignore")).hexdigest()


GENERATOR_VERSION_RE = re.compile(r"WordPress\s+([\d.]+)", re.I)
PLUGIN_VER_RE = re.compile(r"/(?:plugins|themes)/([\w-]+)/.*?\?ver=([\d.]+)(?:&|$)", re.I)


def detect_version_disclosure(soup):
    """Passive check only: does the page reveal WP core / plugin / theme
    version numbers that make it trivial for a scanner to look up known
    CVEs? This does not test for any actual vulnerability."""
    findings = {"wordpress": None, "components": {}}
    generator = soup.find("meta", attrs={"name": re.compile("^generator$", re.I)})
    if generator and generator.get("content"):
        m = GENERATOR_VERSION_RE.search(generator["content"])
        if m:
            findings["wordpress"] = m.group(1)

    for tag in soup.find_all(["script", "link"]):
        src = tag.get("src") or tag.get("href") or ""
        m = PLUGIN_VER_RE.search(src)
        if m:
            name, ver = m.group(1), m.group(2)
            findings["components"].setdefault(name, ver)

    return findings


def fetch_page(url):
    start = time.monotonic()
    resp = safe_get(url)
    elapsed = time.monotonic() - start
    if resp is None:
        pd = PageData(url=url, ok=False)
        return pd, None
    pd = PageData(url=url, status_code=resp.status_code, load_time=elapsed)
    pd.size_bytes = len(resp.content)
    pd.ok = resp.status_code < 400
    pd.headers = dict(resp.headers)
    if not pd.ok or "text/html" not in resp.headers.get("content-type", "text/html"):
        return pd, None
    soup = BeautifulSoup(resp.text, "html.parser")
    return pd, soup


def analyze_page(pd, soup, base_netloc):
    # Title / meta description
    title_tag = soup.find("title")
    pd.title = title_tag.get_text(strip=True) if title_tag else ""
    desc_tag = soup.find("meta", attrs={"name": re.compile("^description$", re.I)})
    pd.meta_description = desc_tag.get("content", "").strip() if desc_tag and desc_tag.get("content") else ""

    pd.version_disclosure = detect_version_disclosure(soup)

    # Headings
    h1s = soup.find_all("h1")
    pd.h1_count = len(h1s)
    pd.h1_texts = [h.get_text(strip=True)[:80] for h in h1s]

    # Viewport
    viewport = soup.find("meta", attrs={"name": re.compile("^viewport$", re.I)})
    pd.has_viewport = viewport is not None

    # Images
    imgs = soup.find_all("img")
    pd.images_total = len(imgs)
    for i, img in enumerate(imgs):
        alt = img.get("alt")
        if alt is None or not alt.strip():
            pd.images_missing_alt += 1
        if not (img.get("width") and img.get("height")):
            pd.images_missing_dims += 1
        loading = (img.get("loading") or "").lower()
        if i >= 2 and loading != "lazy":
            pd.images_missing_lazy += 1
        real_src = img.get("data-src") or img.get("data-lazy-src") or img.get("src")
        if real_src and not real_src.startswith("data:"):
            width = img.get("width")
            height = img.get("height")
            is_tiny_icon = False
            try:
                if width and height and int(width) <= 48 and int(height) <= 48:
                    is_tiny_icon = True
            except ValueError:
                pass
            if not is_tiny_icon:
                pd.image_srcs.append(urljoin(pd.url, real_src))

    # Scripts
    scripts = soup.find_all("script")
    pd.total_scripts = len(scripts)
    head = soup.find("head")
    head_scripts = head.find_all("script", src=True) if head else []
    for s in head_scripts:
        if not (s.has_attr("async") or s.has_attr("defer") or s.get("type") == "module"):
            pd.render_blocking_scripts += 1
    for s in scripts:
        src = s.get("src")
        if src:
            pd.script_srcs.append(src)

    # Inline style bloat
    inline_styled = soup.find_all(style=True)
    pd.inline_style_chars = sum(len(t.get("style", "")) for t in inline_styled)
    style_tags = soup.find_all("style")
    pd.style_tag_chars = sum(len(t.get_text()) for t in style_tags)

    # Fixed-width inline styles (mobile responsiveness risk)
    fixed_width_re = re.compile(r"width\s*:\s*(\d{3,5})px", re.I)
    for t in inline_styled:
        style_val = t.get("style", "")
        m = fixed_width_re.search(style_val)
        if m and int(m.group(1)) > 480 and "max-width" not in style_val.lower():
            pd.fixed_width_inline_count += 1

    # Structural duplication: header/nav/footer tags
    pd.header_count = len(soup.find_all("header"))
    pd.nav_count = len(soup.find_all("nav"))
    pd.footer_count = len(soup.find_all("footer"))

    nav_hashes = [extract_hash(n) for n in soup.find_all("nav")]
    dupes = [h for h, c in Counter(nav_hashes).items() if c > 1]
    pd.duplicate_nav_blocks = len(dupes)

    # Links
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if not href or href.startswith(("#", "mailto:", "tel:", "javascript:")):
            continue
        full = urljoin(pd.url, href)
        full_norm = normalize_url(full)
        if same_domain(full_norm, base_netloc):
            pd.internal_links.add(full_norm)
        else:
            pd.external_links.add(full_norm)

    # Booking platform mentions (search hrefs + inline script text + visible text)
    haystacks = []
    for a in soup.find_all("a", href=True):
        haystacks.append(a["href"])
    for s in scripts:
        if s.string:
            haystacks.append(s.string)
        src = s.get("src")
        if src:
            haystacks.append(src)
    haystacks.append(soup.get_text(" ", strip=True))
    joined = " ".join(haystacks).lower()
    pd.momence_hits = joined.count("momence")
    pd.vagaro_hits = joined.count("vagaro")

    for a in soup.find_all("a", href=True):
        href_l = a["href"].lower()
        if any(dom in href_l for dom in CHECKOUT_DOMAINS):
            pd.offsite_checkout_links.add(a["href"])

    # CTA detection
    clickable_texts = []
    for tag in soup.find_all(["a", "button"]):
        clickable_texts.append(tag.get_text(" ", strip=True).lower())
    combined_cta_text = " | ".join(clickable_texts)
    pd.has_cta = any(kw in combined_cta_text for kw in CTA_KEYWORDS)

    # Tracking scripts
    all_script_text = " ".join([s.string or "" for s in scripts]) + " ".join(pd.script_srcs)
    pd.gtm_count = len(re.findall(r"googletagmanager\.com/gtm\.js|GTM-[A-Z0-9]+", all_script_text))
    pd.has_gtm = pd.gtm_count > 0
    pd.pixel_count = len(re.findall(r"connect\.facebook\.net|fbq\(\s*['\"]init['\"]", all_script_text))
    pd.has_meta_pixel = pd.pixel_count > 0
    pd.has_ga4 = bool(re.search(r"gtag\(\s*['\"]config['\"]|googletagmanager\.com/gtag/js", all_script_text))

    # Content hash for duplicate-content detection (main content region only)
    main = soup.find("main") or soup.find("article") or soup.find(id=re.compile("content", re.I))
    if main is None:
        main = soup.body or soup
    for tag_name in ("header", "nav", "footer"):
        for t in main.find_all(tag_name):
            t.decompose()
    text = re.sub(r"\s+", " ", main.get_text(" ", strip=True)).lower()
    pd.text_len = len(text)
    pd.content_hash = hashlib.sha1(text.encode("utf-8", "ignore")).hexdigest() if text else ""


def crawl(base_url):
    base_url = normalize_url(base_url)
    base_netloc = urlparse(base_url).netloc
    rp, has_robots = load_robots(base_url)

    sitemap_found, sitemap_url = check_sitemap(base_url)

    queue = [base_url]
    visited = set()
    pages = {}
    incoming_links = defaultdict(set)  # url -> set of pages linking to it
    all_internal_links_seen = set()
    platform = PlatformInfo()

    while queue and len(visited) < MAX_PAGES:
        url = queue.pop(0)
        if url in visited:
            continue
        if has_robots and not rp.can_fetch(USER_AGENT, url):
            log.info("Skipping (robots.txt disallow): %s", url)
            continue
        visited.add(url)
        log.info("Fetching (%d/%d): %s", len(visited), MAX_PAGES, url)
        pd, soup = fetch_page(url)
        if soup is not None:
            try:
                analyze_page(pd, soup, base_netloc)
            except Exception as exc:  # noqa: BLE001 - never let one page crash the crawl
                log.warning("Failed to analyze %s: %s", url, exc)
            if url == base_url:
                # Detected here because it needs the parsed homepage, which is
                # not retained past the crawl.
                try:
                    platform = detect_platform(pd, soup)
                    log.info("Platform: %s%s (%s confidence)", platform.platform,
                              f" + {platform.page_builder}" if platform.page_builder else "",
                              platform.confidence)
                except Exception as exc:  # noqa: BLE001
                    log.warning("Platform detection failed: %s", exc)
        pages[url] = pd

        if soup is not None:
            for link in pd.internal_links:
                all_internal_links_seen.add(link)
                incoming_links[link].add(url)
                if link not in visited and link not in queue and is_crawlable(link):
                    queue.append(link)

    return {
        "base_url": base_url,
        "pages": pages,
        "incoming_links": incoming_links,
        "has_robots": has_robots,
        "sitemap_found": sitemap_found,
        "sitemap_url": sitemap_url,
        "all_internal_links_seen": all_internal_links_seen,
        "platform": platform,
    }


# --------------------------------------------------------------------------
# Link checking (broken internal / external links)
# --------------------------------------------------------------------------

def check_links(crawl_data):
    pages = crawl_data["pages"]
    checked = {}
    to_check = set()
    for pd in pages.values():
        to_check.update(pd.external_links)
    for link in crawl_data["all_internal_links_seen"]:
        if link not in pages:
            to_check.add(link)

    to_check = list(to_check)[:MAX_LINK_CHECKS]
    log.info("Checking %d unique links for broken status...", len(to_check))
    for link in to_check:
        resp = safe_get(link, method="HEAD")
        if resp is None:
            checked[link] = (None, "request failed / timed out")
        else:
            checked[link] = (resp.status_code, "")
    return checked


def get_image_size_kb(url, cache):
    if url in cache:
        return cache[url]
    resp = safe_get(url, method="HEAD")
    size_kb = None
    if resp is not None:
        cl = resp.headers.get("content-length")
        if cl and cl.isdigit():
            size_kb = int(cl) / 1024
        try:
            resp.close()
        except Exception:  # noqa: BLE001
            pass
    cache[url] = size_kb
    return size_kb


def check_image_sizes(crawl_data):
    """Sample a few images per page (shared cache across pages) and record sizes."""
    findings = defaultdict(list)  # page_url -> [(img_url, size_kb)]
    cache = {}
    for url, pd in crawl_data["pages"].items():
        if not pd.ok or not pd.image_srcs:
            continue
        sample = pd.image_srcs[:MAX_IMAGE_CHECKS_PER_PAGE]
        for img_url in sample:
            size_kb = get_image_size_kb(img_url, cache)
            if size_kb is not None:
                findings[url].append((img_url, size_kb))
    return findings


# --------------------------------------------------------------------------
# Real Core Web Vitals via Google PageSpeed Insights v5
# --------------------------------------------------------------------------

_psi_lock = threading.Lock()
_psi_consecutive_failures = 0
_psi_disabled = False


def load_json_cache(path, label):
    """Read a JSON cache file, returning {} if it is missing or unreadable."""
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError) as exc:
            log.warning("Could not read %s cache (%s) - starting fresh", label, exc)
    return {}


def save_json_cache(path, cache, label):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(cache, f)
    except OSError as exc:
        log.warning("Could not write %s cache: %s", label, exc)


def load_pagespeed_cache():
    return load_json_cache(PAGESPEED_CACHE_FILE, "PageSpeed")


def save_pagespeed_cache(cache):
    save_json_cache(PAGESPEED_CACHE_FILE, cache, "PageSpeed")


def parse_pagespeed_response(data, strategy):
    result = PageSpeedResult(strategy=strategy)
    try:
        lighthouse = data.get("lighthouseResult", {}) or {}
        perf = (lighthouse.get("categories", {}) or {}).get("performance", {}) or {}
        if perf.get("score") is not None:
            result.performance_score = round(perf["score"] * 100)
        audits = lighthouse.get("audits", {}) or {}

        lcp = audits.get("largest-contentful-paint", {}) or {}
        result.lcp_ms = lcp.get("numericValue")
        result.lcp_display = lcp.get("displayValue", "")

        cls_audit = audits.get("cumulative-layout-shift", {}) or {}
        result.cls = cls_audit.get("numericValue")

        # Prefer real-world field data (CrUX) for INP if available; else a lab
        # audit; else fall back to Total Blocking Time (TBT).
        field_metrics = (data.get("loadingExperience") or {}).get("metrics", {}) or {}
        inp_field = field_metrics.get("INTERACTION_TO_NEXT_PAINT")
        if inp_field and inp_field.get("percentile") is not None:
            result.inp_ms = inp_field["percentile"]
            result.used_inp = True
        else:
            inp_audit = audits.get("interaction-to-next-paint") or audits.get("experimental-interaction-to-next-paint")
            if inp_audit and inp_audit.get("numericValue") is not None:
                result.inp_ms = inp_audit["numericValue"]
                result.used_inp = True
            else:
                tbt_audit = audits.get("total-blocking-time", {}) or {}
                result.tbt_ms = tbt_audit.get("numericValue")

        opportunities = []
        for audit_id, audit in audits.items():
            details = audit.get("details") or {}
            score = audit.get("score")
            if details.get("type") == "opportunity" and score is not None and score < 1:
                savings_ms = details.get("overallSavingsMs", 0) or 0
                savings_bytes = details.get("overallSavingsBytes", 0) or 0
                if savings_ms > 0 or savings_bytes > 0:
                    opportunities.append((audit.get("title", audit_id), savings_ms, savings_bytes))
        opportunities.sort(key=lambda x: (x[1], x[2]), reverse=True)
        result.opportunities = [title for title, _, _ in opportunities[:3]]
    except (KeyError, TypeError, AttributeError) as exc:
        result.error = f"parse error: {exc}"
    return result


def fetch_pagespeed(url, strategy, cache):
    """Thread-safe: called concurrently from a ThreadPoolExecutor, so all
    shared mutable state (the cache dict, the failure counter, the disabled
    flag) is guarded by _psi_lock."""
    global _psi_consecutive_failures, _psi_disabled

    key = f"{strategy}:{url}"
    with _psi_lock:
        cached = cache.get(key)
        disabled = _psi_disabled
    if cached:
        age = time.time() - cached.get("_fetched_at", 0)
        if age < PAGESPEED_CACHE_TTL_SECONDS:
            payload = {k: v for k, v in cached.items() if k != "_fetched_at"}
            try:
                return PageSpeedResult(**payload)
            except TypeError:
                pass  # incompatible cache entry from an older run - refetch

    if disabled:
        return PageSpeedResult(strategy=strategy, error="skipped (PageSpeed disabled after repeated failures)")

    params = {"url": url, "strategy": strategy, "category": "performance"}
    if PAGESPEED_API_KEY:
        params["key"] = PAGESPEED_API_KEY

    try:
        resp = requests.get(PAGESPEED_API_URL, params=params, timeout=PAGESPEED_TIMEOUT)
    except requests.exceptions.RequestException as exc:
        result = PageSpeedResult(strategy=strategy, error=f"request failed: {exc}")
        log.warning("PageSpeed API request failed for %s [%s]: %s", url, strategy, exc)
        failed = True
    else:
        if resp.status_code == 200:
            try:
                result = parse_pagespeed_response(resp.json(), strategy)
                failed = False
            except ValueError as exc:
                result = PageSpeedResult(strategy=strategy, error=f"invalid JSON response: {exc}")
                failed = True
        else:
            reason = "rate-limited/quota exceeded" if resp.status_code in (429, 403) else f"HTTP {resp.status_code}"
            result = PageSpeedResult(strategy=strategy, error=reason)
            log.warning("PageSpeed API %s for %s [%s]", reason, url, strategy)
            failed = True

    with _psi_lock:
        if failed:
            _psi_consecutive_failures += 1
        else:
            _psi_consecutive_failures = 0
        if _psi_consecutive_failures >= PAGESPEED_MAX_CONSECUTIVE_FAILURES and not _psi_disabled:
            _psi_disabled = True
            log.warning(
                "PageSpeed API failed %d times in a row - disabling further calls this run. "
                "Set PAGESPEED_API_KEY for a higher quota: "
                "https://developers.google.com/speed/docs/insights/v5/get-started",
                _psi_consecutive_failures,
            )
        entry = asdict(result)
        entry["_fetched_at"] = time.time()
        cache[key] = entry

    return result


def run_pagespeed_checks(crawl_data):
    cache = load_pagespeed_cache()
    pages = crawl_data["pages"]
    ok_urls = [u for u, pd in pages.items() if pd.ok][:PAGESPEED_MAX_PAGES]
    tasks = [(url, strategy) for url in ok_urls for strategy in PAGESPEED_STRATEGIES]
    log.info("Running PageSpeed Insights for %d pages x %d strategies (%d concurrent, slow API - please be patient)...",
              len(ok_urls), len(PAGESPEED_STRATEGIES), PAGESPEED_CONCURRENCY)
    if not PAGESPEED_API_KEY:
        log.info("No PAGESPEED_API_KEY set - using the free unauthenticated tier, which is heavily rate-limited.")

    start = time.monotonic()
    completed = 0
    executor = ThreadPoolExecutor(max_workers=PAGESPEED_CONCURRENCY)
    future_map = {executor.submit(fetch_pagespeed, url, strategy, cache): (url, strategy) for url, strategy in tasks}
    try:
        for future in as_completed(future_map):
            url, strategy = future_map[future]
            try:
                result = future.result()
            except Exception as exc:  # noqa: BLE001 - never let one PSI call crash the whole run
                result = PageSpeedResult(strategy=strategy, error=f"unexpected error: {exc}")
            pages[url].psi[strategy] = result
            completed += 1
            log.info("PageSpeed (%d/%d): %s [%s]", completed, len(tasks), url, strategy)
            if completed % 6 == 0:
                save_pagespeed_cache(cache)
            if time.monotonic() - start > PAGESPEED_MAX_TOTAL_SECONDS:
                log.warning("PageSpeed checks exceeded the %ds time budget - cancelling remaining requests.",
                            PAGESPEED_MAX_TOTAL_SECONDS)
                executor.shutdown(wait=False, cancel_futures=True)
                break
    finally:
        executor.shutdown(wait=True)
    save_pagespeed_cache(cache)
    return cache


# --------------------------------------------------------------------------
# Passive security hygiene (no active exploitation / vulnerability testing)
# --------------------------------------------------------------------------

def check_ssl_cert(hostname, port=443, timeout=10):
    try:
        ctx = ssl.create_default_context()
        with socket.create_connection((hostname, port), timeout=timeout) as sock:
            with ctx.wrap_socket(sock, server_hostname=hostname) as ssock:
                cert = ssock.getpeercert()
        not_after = cert.get("notAfter")
        expiry = datetime.strptime(not_after, "%b %d %H:%M:%S %Y %Z").replace(tzinfo=timezone.utc)
        days_left = (expiry - datetime.now(timezone.utc)).days
        return {"ok": True, "expiry": expiry, "days_left": days_left}
    except Exception as exc:  # noqa: BLE001 - any SSL/socket failure just means "couldn't verify"
        return {"ok": False, "error": str(exc)}


def check_security(crawl_data):
    issues = []
    base_url = crawl_data["base_url"]
    parsed = urlparse(base_url)
    homepage = crawl_data["pages"].get(base_url)

    if parsed.scheme != "https":
        add_issue(issues, "Security", "Site is not served over HTTPS", "High", "Quick",
                   "Without HTTPS, all traffic (including any forms) travels unencrypted, browsers show "
                   "'Not Secure' warnings, and Google uses HTTPS as a ranking signal.",
                   ["Install an SSL certificate (Let's Encrypt is free) via your host's control panel.",
                    "Force HTTPS site-wide via WordPress settings or a redirect plugin."],
                   page_url=base_url)
    else:
        cert_info = check_ssl_cert(parsed.hostname)
        if not cert_info["ok"]:
            add_issue(issues, "Security", "Could not verify SSL certificate", "Low", "Quick",
                       f"Automated SSL verification failed ({cert_info['error']}). This may just mean our checker "
                       "couldn't connect, but it's worth confirming the certificate is valid in a browser.",
                       ["Open the site in a browser and check for a valid padlock/certificate.",
                        "If invalid/expired, renew the SSL certificate through your host or Let's Encrypt."],
                       page_url=base_url)
        elif cert_info["days_left"] < 0:
            add_issue(issues, "Security", "SSL certificate has expired", "High", "Involved",
                       "An expired certificate causes browsers to show a hard security warning to every visitor, "
                       "which will crater trust and conversions immediately.",
                       ["Renew the SSL certificate immediately through your host or Let's Encrypt.",
                        "Set up auto-renewal so this doesn't happen again."],
                       page_url=base_url)
        elif cert_info["days_left"] < SSL_EXPIRY_WARN_DAYS:
            add_issue(issues, "Security", f"SSL certificate expiring soon ({cert_info['days_left']} days)",
                       "Medium", "Quick",
                       "A soon-to-expire certificate risks an unplanned outage/browser warning if renewal is missed.",
                       ["Renew the certificate now or confirm auto-renewal is configured (common with Let's Encrypt)."],
                       page_url=base_url)

    if homepage is not None and homepage.headers:
        present_lower = {k.lower() for k in homepage.headers}
        missing = [label for header, label in SECURITY_HEADERS.items() if header.lower() not in present_lower]
        if missing:
            non_csp_missing = [m for m in missing if m != "CSP"]
            severity = "Medium" if non_csp_missing else "Low"
            effort = "Moderate" if len(missing) >= 3 else "Quick"
            add_issue(issues, "Security", "Missing recommended security headers", severity, effort,
                       f"The site is missing: {', '.join(missing)}. These headers are defense-in-depth measures "
                       "against clickjacking, MIME-sniffing, and content injection - they don't fix a specific "
                       "vulnerability but are considered baseline hygiene.",
                       ["Add missing headers via a security plugin (Really Simple SSL, Wordfence) or host/CDN config (e.g. Cloudflare).",
                        "Start with X-Content-Type-Options and X-Frame-Options (low risk of breaking anything); "
                        "test Content-Security-Policy carefully since a strict policy can break embedded widgets/scripts if misconfigured."],
                       page_url=base_url, page_detail=", ".join(missing))

    agg_wp = None
    agg_components = {}
    for pd in crawl_data["pages"].values():
        vd = pd.version_disclosure
        if not vd:
            continue
        if vd.get("wordpress") and not agg_wp:
            agg_wp = vd["wordpress"]
        for name, ver in vd.get("components", {}).items():
            agg_components.setdefault(name, ver)

    if agg_wp:
        add_issue(issues, "Security", "WordPress version publicly exposed", "Low", "Quick",
                   f"The site discloses WordPress version {agg_wp} via the generator meta tag. This isn't a "
                   "vulnerability by itself, but it makes it trivial for automated scanners to check whether "
                   "that version has known CVEs.",
                   ["Remove the generator meta tag (many security plugins offer a one-click toggle for this).",
                    "Keep WordPress core updated regardless - hiding the version is obscurity, not real protection."],
                   page_url=base_url)

    if agg_components:
        examples = ", ".join(f"{name} {ver}" for name, ver in list(agg_components.items())[:3])
        add_issue(issues, "Security", "Plugin/theme versions exposed via asset URLs", "Low", "Quick",
                   f"Asset query strings reveal exact plugin/theme versions (e.g. {examples}), letting automated "
                   "scanners quickly check for known vulnerabilities in those specific versions.",
                   ["Use a security plugin to strip version query strings from asset URLs.",
                    "Keep all plugins/themes updated regardless - this is a disclosure risk, not a vulnerability test."],
                   page_url=base_url)

    return issues


# --------------------------------------------------------------------------
# Issue detection
# --------------------------------------------------------------------------

def add_issue(issues, category, issue_text, severity, effort, why, solutions, page_url=None, page_detail=None):
    """Add (or merge into an existing) issue. page_detail is a short per-page
    annotation (e.g. "68 scripts") shown alongside the URL, so pages with
    slightly different numbers still collapse into one grouped finding
    instead of fragmenting into near-duplicate entries."""
    key = (category, issue_text, severity)
    entry = f"{page_url} ({page_detail})" if (page_url and page_detail) else page_url
    for existing in issues:
        if (existing.category, existing.issue, existing.severity) == key:
            if entry and entry not in existing.pages:
                existing.pages.append(entry)
            return
    new_issue = Issue(category=category, issue=issue_text, severity=severity, effort=effort, why=why,
                       solutions=solutions, pages=[entry] if entry else [])
    issues.append(new_issue)


def short_label(url, max_len=60):
    """Shorten a URL for embedding inline in prose so a single long token
    (e.g. a media-library filename) doesn't blow out line wrapping."""
    if len(url) <= max_len:
        return url
    tail = url.rsplit("/", 1)[-1]
    if len(tail) > max_len - 10:
        tail = tail[: max_len - 13] + "..."
    return f".../{tail}"


def detect_issues(crawl_data, link_status, image_findings, include_site_level=True):
    """Detect issues from crawl data.

    include_site_level=False restricts detection to checks that are decidable
    from a single fetched page, skipping the two blocks that need crawl
    context: the robots.txt/sitemap probes (screen mode never requests them,
    so their absence is unknown rather than false) and the cross-page
    aggregates at the end (duplicate titles/descriptions/content, orphan
    pages, broken links). Everything in the per-page loop runs either way, so
    screen mode and report mode share one detection implementation.

    Anything decidable from one page's HTML belongs in the per-page loop, not
    in the site-level blocks, or screen mode will silently lose it."""
    issues = []
    pages = crawl_data["pages"]
    base_url = crawl_data["base_url"]

    if include_site_level and not crawl_data["has_robots"]:
        add_issue(issues, "SEO", "robots.txt is missing or unreachable", "Medium", "Quick",
                   "Search engines use robots.txt to understand crawl permissions; without it, "
                   "crawl behavior is left entirely to default engine heuristics and you lose a "
                   "simple place to point crawlers at your sitemap.",
                   ["Add a minimal robots.txt allowing all crawlers and referencing the XML sitemap.",
                    "If using Yoast/RankMath/AIOSEO, enable their automatic robots.txt generation.",
                    "Verify the file is publicly accessible at /robots.txt with a 200 status."],
                   page_url=base_url)

    if include_site_level and not crawl_data["sitemap_found"]:
        add_issue(issues, "SEO", "XML sitemap not found at standard location", "Medium", "Quick",
                   "An XML sitemap helps search engines discover and prioritize pages, especially "
                   "on sites with dynamic Elementor-built pages that may have weak internal linking.",
                   ["Install/enable Yoast SEO, RankMath, or Google XML Sitemaps to auto-generate one.",
                    "Manually submit the correct sitemap URL in Google Search Console once available.",
                    "Ensure /sitemap.xml or /sitemap_index.xml returns valid XML with a 200 status."],
                   page_url=base_url)

    # --- Per-page checks -------------------------------------------------
    titles = defaultdict(list)
    descriptions = defaultdict(list)
    content_hashes = defaultdict(list)

    for url, pd in pages.items():
        if not pd.ok:
            add_issue(issues, "SEO", "Page returned an error status code", "High", "Moderate",
                       f"'{url}' returned HTTP {pd.status_code or 'no response'}. Broken pages hurt "
                       "SEO rankings and create dead-ends for visitors and search crawlers alike.",
                       ["If deleted intentionally, add a 301 redirect to the closest relevant page.",
                        "If unintentional, restore the page or fix the server/plugin error causing it.",
                        "Re-check the internal links pointing to this URL and update or remove them."],
                       page_url=url)
            continue

        # Performance
        if pd.load_time > 3.0:
            add_issue(issues, "Performance", "Slow page load time (>3s)", "High", "Involved",
                       f"'{url}' took {pd.load_time:.2f}s to respond. Pages over 3 seconds see "
                       "significantly higher bounce rates and are penalized in Google's Core Web Vitals ranking signal.",
                       ["Enable a caching plugin (WP Rocket, W3 Total Cache) and a CDN.",
                        "Audit and disable unused Elementor widgets/plugins adding server overhead.",
                        "Upgrade hosting tier or move to managed WordPress hosting optimized for Elementor."],
                       page_url=url)
        elif pd.load_time > 1.5:
            add_issue(issues, "Performance", "Moderately slow page load time (1.5-3s)", "Medium", "Moderate",
                       f"'{url}' took {pd.load_time:.2f}s to respond. This is above the ~1s target "
                       "for good perceived performance and may soft-cap conversion rates.",
                       ["Enable page/object caching and compress images site-wide.",
                        "Minify and combine CSS/JS via a performance plugin.",
                        "Review third-party scripts (booking widgets, chat, analytics) for load impact."],
                       page_url=url)

        if pd.size_bytes > 3_000_000:
            add_issue(issues, "Performance", "Very large page size (>3MB)", "High", "Involved",
                       f"'{url}' transferred {pd.size_bytes/1_000_000:.1f}MB. Large payloads slow load "
                       "time considerably, especially on mobile connections.",
                       ["Compress/resize hero and gallery images (use WebP where possible).",
                        "Lazy-load below-the-fold images and embeds.",
                        "Audit for unused CSS/JS bundles being loaded on every page."],
                       page_url=url)
        elif pd.size_bytes > 1_500_000:
            add_issue(issues, "Performance", "Large page size (1.5-3MB)", "Medium", "Moderate",
                       f"'{url}' transferred {pd.size_bytes/1_000_000:.1f}MB, above the ~1-1.5MB "
                       "guideline for fast-loading marketing pages.",
                       ["Run images through a compression tool (ShortPixel, Imagify, Squoosh).",
                        "Defer non-critical scripts and styles.",
                        "Remove unused Elementor widgets/sections that add hidden weight."],
                       page_url=url)

        if pd.render_blocking_scripts > 0:
            add_issue(issues, "Performance", "Render-blocking scripts in <head>", "Medium", "Moderate",
                       "Several pages load scripts in the <head> without async/defer, delaying the "
                       "browser's ability to render visible content (impacts First Contentful Paint).",
                       ["Add the 'defer' attribute to non-critical head scripts.",
                        "Move non-essential scripts to load just before </body>.",
                        "Use a performance plugin's 'delay JavaScript execution' feature."],
                       page_url=url, page_detail=f"{pd.render_blocking_scripts} found")

        if pd.total_scripts > 35:
            add_issue(issues, "Performance", "Excessive script count (over 35 <script> tags)", "High", "Involved",
                       "Pages with 35+ scripts show a strong sign of plugin/widget bloat typical of "
                       "heavily-extended Elementor sites. Each script adds parse/network overhead, "
                       "slowing down every visit.",
                       ["Audit installed plugins and disable/remove unused ones.",
                        "Consolidate tracking scripts through Google Tag Manager instead of individual plugin tags.",
                        "Use an asset-unloading plugin (Asset CleanUp, Perfmatters) to strip scripts per-page."],
                       page_url=url, page_detail=f"{pd.total_scripts} scripts")
        elif pd.total_scripts > 20:
            add_issue(issues, "Performance", "High script count (20-35 <script> tags)", "Medium", "Moderate",
                       "Pages in the 20-35 script range are on the high side and worth a plugin audit "
                       "before they become a bigger performance problem.",
                       ["Review the plugin list for redundant or unused tools.",
                        "Combine tracking pixels/tags into Google Tag Manager.",
                        "Consider a script-management plugin to conditionally load per-page."],
                       page_url=url, page_detail=f"{pd.total_scripts} scripts")

        if pd.images_missing_lazy > 0:
            add_issue(issues, "Performance", "Images missing lazy-loading", "Medium", "Quick",
                       "Below-the-fold images without loading=\"lazy\" force the browser to download "
                       "them immediately even if the visitor never scrolls that far.",
                       ["Enable Elementor's built-in native lazy-loading (Performance settings).",
                        "Use a lazy-load plugin (a3 Lazy Load, WP Rocket's LazyLoad) if not built-in.",
                        "Manually add loading=\"lazy\" to below-the-fold <img> tags."],
                       page_url=url, page_detail=f"{pd.images_missing_lazy} images")

        if pd.images_missing_dims > 0:
            add_issue(issues, "Performance", "Images missing explicit width/height", "Low", "Quick",
                       "Images without width/height attributes can cause layout shift (poor Cumulative "
                       "Layout Shift score) as they load in.",
                       ["Re-save/re-insert images through the Media Library so Elementor sets dimensions.",
                        "Add explicit width/height (or aspect-ratio CSS) to affected image tags."],
                       page_url=url, page_detail=f"{pd.images_missing_dims} images")

        for img_url, size_kb in image_findings.get(url, []):
            if size_kb > 1000:
                add_issue(issues, "Performance", "Oversized/uncompressed image (>1MB)", "High", "Quick",
                           "Uncompressed images are one of the most common causes of slow "
                           "WordPress/Elementor sites and directly hurt Core Web Vitals scores.",
                           ["Compress with ShortPixel/Imagify/Squoosh and re-upload.",
                            "Serve responsive sizes via srcset so mobile doesn't download desktop-size images.",
                            "Convert to WebP/AVIF for better compression at similar quality."],
                           page_url=url, page_detail=f"{short_label(img_url)}, {size_kb:.0f}KB")
            elif size_kb > 300:
                add_issue(issues, "Performance", "Moderately large image (300KB-1MB)", "Low", "Quick",
                           "These images are larger than the ~200-300KB guideline for web images.",
                           ["Run through an image compression plugin or tool before re-uploading.",
                            "Consider WebP format for better compression."],
                           page_url=url, page_detail=f"{short_label(img_url)}, {size_kb:.0f}KB")

        # Real-world performance (Google PageSpeed Insights)
        for strategy_label, strategy_key in (("Mobile", "mobile"), ("Desktop", "desktop")):
            psi = pd.psi.get(strategy_key)
            if psi is None or psi.error:
                continue

            if psi.performance_score is not None:
                if psi.performance_score < 50:
                    add_issue(issues, "Performance", f"Poor Google PageSpeed score ({strategy_label})", "High", "Involved",
                               f"Google's PageSpeed Insights scores real-world {strategy_label.lower()} performance "
                               "below 50/100 - the threshold Google itself labels 'poor'. This is the same lab used "
                               "to compute Core Web Vitals ranking signals in Google Search.",
                               [f"Address the top opportunities PageSpeed flags: "
                                f"{', '.join(psi.opportunities) if psi.opportunities else 'see the full report at pagespeed.web.dev'}.",
                                "Re-run PageSpeed Insights after each fix to confirm the score improves.",
                                "Prioritize mobile first - it's usually the stricter, ranking-determinant strategy."],
                               page_url=url, page_detail=f"{psi.performance_score}/100")
                elif psi.performance_score < 90:
                    add_issue(issues, "Performance", f"Moderate Google PageSpeed score ({strategy_label})", "Medium", "Moderate",
                               f"A {strategy_label.lower()} PageSpeed score under 90 leaves room for improvement "
                               "before hitting Google's 'good' performance threshold.",
                               [f"Address the top opportunities: "
                                f"{', '.join(psi.opportunities) if psi.opportunities else 'see the full PageSpeed report for specifics'}.",
                                "Re-test after fixes to track improvement over time."],
                               page_url=url, page_detail=f"{psi.performance_score}/100")

            if psi.lcp_ms is not None:
                if psi.lcp_ms > 4000:
                    add_issue(issues, "Performance", f"Slow Largest Contentful Paint - LCP ({strategy_label})", "High", "Involved",
                               "LCP over 4 seconds is rated 'poor' by Google and means visitors wait a long time to "
                               "see the main content, hurting both user experience and Core Web Vitals ranking.",
                               ["Compress and preload the hero image or largest above-the-fold element.",
                                "Remove render-blocking CSS/JS that delays first paint.",
                                "Upgrade hosting/caching so the server responds faster (Time to First Byte)."],
                               page_url=url, page_detail=psi.lcp_display or f"{psi.lcp_ms:.0f}ms")
                elif psi.lcp_ms > 2500:
                    add_issue(issues, "Performance", f"Moderate Largest Contentful Paint - LCP ({strategy_label})", "Medium", "Moderate",
                               "LCP between 2.5-4s is rated 'needs improvement' by Google.",
                               ["Compress the largest above-the-fold image and serve it in a modern format.",
                                "Preload critical resources and defer non-critical scripts."],
                               page_url=url, page_detail=psi.lcp_display or f"{psi.lcp_ms:.0f}ms")

            if psi.cls is not None:
                if psi.cls > 0.25:
                    add_issue(issues, "Performance", f"Poor visual stability - high CLS ({strategy_label})", "Medium", "Moderate",
                               "A Cumulative Layout Shift above 0.25 is rated 'poor' - visible content jumps around "
                               "as the page loads, which is jarring and can cause mis-clicks.",
                               ["Add explicit width/height to all images and embeds so space is reserved before they load.",
                                "Avoid injecting banners/ads above existing content after initial render."],
                               page_url=url, page_detail=f"{psi.cls:.2f}")
                elif psi.cls > 0.1:
                    add_issue(issues, "Performance", f"Moderate visual stability - CLS ({strategy_label})", "Low", "Quick",
                               "A CLS between 0.1-0.25 is rated 'needs improvement'.",
                               ["Add explicit width/height to images to reserve space before they load."],
                               page_url=url, page_detail=f"{psi.cls:.2f}")

            if psi.used_inp and psi.inp_ms is not None:
                if psi.inp_ms > 500:
                    add_issue(issues, "Performance", f"Poor responsiveness - high INP ({strategy_label})", "High", "Involved",
                               "Interaction to Next Paint over 500ms is rated 'poor' - clicks/taps feel sluggish to respond.",
                               ["Break up long JavaScript tasks (common with heavy plugin/script bloat).",
                                "Reduce the number of third-party scripts running on the main thread."],
                               page_url=url, page_detail=f"{psi.inp_ms:.0f}ms")
                elif psi.inp_ms > 200:
                    add_issue(issues, "Performance", f"Moderate responsiveness - INP ({strategy_label})", "Medium", "Moderate",
                               "INP between 200-500ms is rated 'needs improvement'.",
                               ["Reduce JavaScript execution time, especially from third-party scripts."],
                               page_url=url, page_detail=f"{psi.inp_ms:.0f}ms")
            elif psi.tbt_ms is not None:
                if psi.tbt_ms > 600:
                    add_issue(issues, "Performance", f"High Total Blocking Time - TBT ({strategy_label})", "High", "Involved",
                               "Total Blocking Time over 600ms (a lab proxy for responsiveness) means the main "
                               "thread is busy long enough to delay input response, typical of heavy script bloat.",
                               ["Reduce/defer third-party and plugin scripts blocking the main thread.",
                                "Break up long JavaScript tasks; audit plugins for unnecessary JS execution."],
                               page_url=url, page_detail=f"{psi.tbt_ms:.0f}ms")
                elif psi.tbt_ms > 200:
                    add_issue(issues, "Performance", f"Moderate Total Blocking Time - TBT ({strategy_label})", "Medium", "Moderate",
                               "TBT between 200-600ms leaves some room for improvement in perceived responsiveness.",
                               ["Defer non-critical scripts and reduce third-party script count."],
                               page_url=url, page_detail=f"{psi.tbt_ms:.0f}ms")

        # SEO
        if not pd.title:
            add_issue(issues, "SEO", "Missing page title", "High", "Quick",
                       f"'{url}' has no <title> tag content. Titles are the single most important "
                       "on-page SEO element and also what shows in browser tabs and search results.",
                       ["Set a unique, descriptive title in the page/post editor or Yoast/RankMath panel.",
                        "Keep titles to ~50-60 characters including brand name."],
                       page_url=url)
        else:
            titles[pd.title.lower().strip()].append(url)
            if len(pd.title) > 60:
                add_issue(issues, "SEO", "Page title too long (over 60 chars)", "Low", "Quick",
                           "Titles beyond ~60 characters will likely be truncated by Google in search results.",
                           ["Shorten to under ~60 characters, keeping the primary keyword near the front."],
                           page_url=url, page_detail=f"{len(pd.title)} chars")

        if not pd.meta_description:
            add_issue(issues, "SEO", "Missing meta description", "Medium", "Quick",
                       f"'{url}' has no meta description. Without one, Google auto-generates a snippet "
                       "from page content, which is often less compelling and hurts click-through rate.",
                       ["Write a unique 120-155 character description per page via Yoast/RankMath.",
                        "Prioritize the homepage and top service/landing pages first."],
                       page_url=url)
        else:
            descriptions[pd.meta_description.lower().strip()].append(url)
            if len(pd.meta_description) > 160:
                add_issue(issues, "SEO", "Meta description too long (over 160 chars)", "Low", "Quick",
                           "Descriptions beyond ~160 characters will be truncated in search results.",
                           ["Trim to ~155 characters while keeping the key value proposition."],
                           page_url=url, page_detail=f"{len(pd.meta_description)} chars")

        if pd.h1_count == 0:
            add_issue(issues, "SEO", "Missing H1 heading", "High", "Quick",
                       f"'{url}' has no H1 tag. The H1 is a primary relevance signal for search engines "
                       "and an accessibility landmark for screen reader users.",
                       ["Add a single, keyword-relevant H1 via the page/Elementor heading widget.",
                        "Check Elementor templates - sometimes the H1 is styled as a <div> or <span> "
                        "instead of a semantic heading tag."],
                       page_url=url)
        elif pd.h1_count > 1:
            add_issue(issues, "SEO", "Multiple H1 headings on one page", "Medium", "Quick",
                       "Multiple H1 tags dilute topical relevance signals and are commonly caused by "
                       "Elementor global headers/popups injecting an extra H1.",
                       ["Change secondary heading widgets to H2/H3.",
                        "Check whether the site header template itself contains an H1 (should be the logo/site name at most, not a full heading)."],
                       page_url=url, page_detail=f"{pd.h1_count} H1s")

        if pd.images_missing_alt > 0:
            severity = "Medium" if pd.images_missing_alt >= 3 else "Low"
            add_issue(issues, "SEO", "Images missing alt text", severity, "Moderate",
                       "Images without alt attributes hurt image SEO and accessibility (screen readers "
                       "cannot describe the image to visually impaired visitors).",
                       ["Add descriptive alt text to each image in the Media Library.",
                        "For purely decorative images, use alt=\"\" explicitly rather than omitting it."],
                       page_url=url, page_detail=f"{pd.images_missing_alt} of {pd.images_total} missing")

        content_hashes[pd.content_hash].append(url)

        # Structure/bloat
        if pd.header_count > 1 or pd.footer_count > 1 or pd.nav_count > 1:
            add_issue(issues, "Structure", "Duplicated header/nav/footer HTML on the same page", "High", "Involved",
                       f"'{url}' renders {pd.header_count} <header>, {pd.nav_count} <nav>, and "
                       f"{pd.footer_count} <footer> element(s). Duplicate structural markup is a known "
                       "issue on this site, likely from an Elementor global header/footer template "
                       "stacking on top of the theme's own header/footer, or a template being included twice.",
                       ["Check Elementor > Theme Builder for duplicate header/footer templates assigned to the same condition.",
                        "Inspect the page source for a theme-level header/footer plus an Elementor-inserted one and remove the redundant copy.",
                        "If intentional (e.g. a secondary mobile nav), mark the duplicate with aria-hidden or a distinct landmark role to avoid confusing assistive tech and site audits."],
                       page_url=url)

        if pd.duplicate_nav_blocks > 0:
            add_issue(issues, "Structure", "Identical navigation menu block repeated on the same page", "Medium", "Moderate",
                       f"'{url}' contains {pd.duplicate_nav_blocks} navigation block(s) with byte-identical "
                       "markup repeated elsewhere on the same page, adding DOM weight without user benefit.",
                       ["Remove the redundant nav instance (often a leftover from a duplicated Elementor section).",
                        "Consolidate to a single global nav template via Elementor Theme Builder."],
                       page_url=url)

        style_bloat = pd.inline_style_chars + pd.style_tag_chars
        if style_bloat > 8000:
            add_issue(issues, "Structure", "Heavy inline/embedded style bloat (over 8KB of CSS text)", "Medium", "Moderate",
                       "Large amounts of inline style=\"\" attributes and embedded <style> blocks are a "
                       "hallmark of Elementor's per-widget inline CSS generation at scale. This bloats "
                       "HTML weight and makes styling harder to maintain.",
                       ["Enable Elementor's 'Improved CSS Loading' / external file generation in Performance settings.",
                        "Regenerate Elementor CSS files (Elementor > Tools > Regenerate CSS).",
                        "Reduce the number of nested Elementor sections/columns on heavy pages."],
                       page_url=url, page_detail=f"~{style_bloat//1000}KB")
        elif style_bloat > 4000:
            add_issue(issues, "Structure", "Moderate inline/embedded style bloat (4-8KB of CSS text)", "Low", "Quick",
                       "A moderate amount of inline/embedded CSS text adds unnecessary HTML weight.",
                       ["Enable external CSS file generation in Elementor's performance settings.",
                        "Periodically regenerate Elementor CSS via Elementor > Tools."],
                       page_url=url, page_detail=f"~{style_bloat//1000}KB")

        if pd.fixed_width_inline_count > 0:
            add_issue(issues, "Mobile/UX", "Fixed pixel widths in inline styles", "Medium", "Moderate",
                       "Elements with a fixed pixel width over 480px and no max-width fallback can force "
                       "horizontal scrolling or clipped content on narrow mobile screens.",
                       ["Change fixed widths to percentage/max-width based sizing in Elementor's responsive settings.",
                        "Test the page at 375px and 414px viewport widths in Chrome DevTools and adjust column widths.",
                        "Use Elementor's built-in responsive width controls instead of custom CSS/inline widths."],
                       page_url=url, page_detail=f"{pd.fixed_width_inline_count} elements")

        # Mobile/UX
        if not pd.has_viewport:
            add_issue(issues, "Mobile/UX", "Missing viewport meta tag", "High", "Quick",
                       f"'{url}' has no <meta name=\"viewport\"> tag, which means mobile browsers will "
                       "render the desktop layout zoomed out instead of adapting to the screen size.",
                       ["Add <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"> to the theme header.",
                        "Confirm the active theme/template isn't stripping this tag via a caching or minification plugin."],
                       page_url=url)

        # Booking / conversion
        if pd.momence_hits > 0 and pd.vagaro_hits > 0:
            add_issue(issues, "Booking/Conversion",
                       "Both Momence and Vagaro referenced on the same page (possible incomplete migration)",
                       "High", "Involved",
                       f"'{url}' references both Momence ({pd.momence_hits}x) and Vagaro ({pd.vagaro_hits}x). "
                       "This strongly suggests an in-progress or incomplete platform migration, which can "
                       "confuse customers about where to book/pay and fragment booking data between two systems.",
                       ["Decide on a single booking platform and remove all references/links to the other.",
                        "Audit every 'Book Now' button and embedded widget site-wide to confirm they point to the correct platform.",
                        "Set up 301 redirects from any old platform's linked pages to the current one."],
                       page_url=url)
        elif pd.momence_hits > 0 or pd.vagaro_hits > 0:
            which = "Momence" if pd.momence_hits > 0 else "Vagaro"
            add_issue(issues, "Booking/Conversion", f"Booking platform reference: {which}", "Low", "Quick",
                       f"'{url}' references {which} {max(pd.momence_hits, pd.vagaro_hits)} time(s). Noted for "
                       "confirmation this is the current, intended booking platform.",
                       ["Confirm this is the sole active booking platform across the whole site."],
                       page_url=url)

        if pd.offsite_checkout_links:
            example = short_label(sorted(pd.offsite_checkout_links)[0], max_len=50)
            add_issue(issues, "Booking/Conversion", "Off-site checkout/booking redirect", "Medium", "Moderate",
                       "Links that send visitors straight to an external booking/checkout domain can lose "
                       "conversion tracking (GTM/Pixel events firing only on-site) and interrupt branded UX.",
                       ["Embed the booking widget in an iframe on-site instead of a raw external link where the platform supports it.",
                        "Fire a tracking event (GTM click trigger) on the outbound link so conversions aren't lost.",
                        "Verify the destination domain matches the currently intended booking platform (see migration note above)."],
                       page_url=url,
                       page_detail=f"{len(pd.offsite_checkout_links)} link(s), e.g. {example}")

        if url == base_url and not pd.has_cta:
            add_issue(issues, "Booking/Conversion", "No clear call-to-action detected on homepage", "Medium", "Moderate",
                       "The homepage has no button/link text matching common CTA phrasing (e.g. 'Book Now', "
                       "'Sign Up', 'Get Started'). The homepage is typically the highest-traffic page and "
                       "needs an unmistakable next step for visitors.",
                       ["Add a prominent, above-the-fold CTA button in the hero section (e.g. 'Book a Class').",
                        "A/B test CTA wording and placement once one is in place.",
                        "Make sure the CTA button style visually contrasts with the rest of the page."],
                       page_url=url)

        # Tracking
        if pd.gtm_count > 1:
            add_issue(issues, "Tracking", "Duplicate Google Tag Manager containers on one page", "High", "Moderate",
                       "Duplicate GTM containers cause double-firing of tags/events, inflating analytics "
                       "numbers and possibly double-counting ad conversions.",
                       ["Search the theme header/footer AND any SEO/analytics plugin settings for a hardcoded GTM snippet, then remove the duplicate.",
                        "Standardize on a single injection method (e.g. only via a plugin, not also hardcoded in theme files)."],
                       page_url=url, page_detail=f"loads {pd.gtm_count}x")
        if pd.pixel_count > 1:
            add_issue(issues, "Tracking", "Duplicate Meta (Facebook) Pixel on one page", "High", "Moderate",
                       "Duplicate Pixel initialization double-counts events like PageView and can distort "
                       "ad campaign optimization and reporting.",
                       ["Remove the duplicate pixel snippet from either the theme, a plugin, or GTM (pick one source of truth).",
                        "Use Meta's Events Manager 'Test Events' tool to confirm only one PageView fires per load."],
                       page_url=url, page_detail=f"loads {pd.pixel_count}x")
        if pd.has_gtm and pd.has_ga4:
            add_issue(issues, "Tracking", "GA4 loaded both directly and via GTM", "Low", "Quick",
                       f"'{url}' appears to load a direct gtag.js/GA4 snippet in addition to Google Tag Manager. "
                       "If GA4 is also configured as a tag inside GTM, this can double-count pageviews.",
                       ["Confirm whether GA4 is configured inside GTM; if so, remove the hardcoded gtag.js snippet.",
                        "Check GA4 Realtime reports for duplicate pageview events to confirm before removing anything."],
                       page_url=url)
        if not pd.has_gtm and not pd.has_ga4:
            add_issue(issues, "Tracking", "No Google Tag Manager or GA4 detected", "Low", "Moderate",
                       f"'{url}' shows no sign of Google Tag Manager or direct GA4 tracking. Without analytics, "
                       "conversion and traffic data for this page cannot be measured.",
                       ["Install Google Tag Manager site-wide via a plugin (Site Kit, GTM4WP) rather than theme edits.",
                        "Configure GA4 as a tag inside GTM rather than hardcoding it."],
                       page_url=url)

    # --- Site-wide checks -------------------------------------------------
    # Everything below needs more than one crawled page (cross-page duplicate
    # detection, orphan detection, link-check results), so screen mode skips it.
    if not include_site_level:
        return issues

    for title_text, urls in titles.items():
        if len(urls) > 1:
            add_issue(issues, "SEO", "Duplicate page titles across multiple pages", "Medium", "Quick",
                       f"{len(urls)} pages share the exact title \"{title_text[:70]}\": "
                       f"{', '.join(urls[:5])}{' ...' if len(urls) > 5 else ''}. Duplicate titles make it "
                       "harder for search engines to determine which page is most relevant for a query.",
                       ["Write a unique, page-specific title for each affected URL.",
                        "Check if these are auto-generated by an Elementor template applied identically across pages."])

    for desc_text, urls in descriptions.items():
        if len(urls) > 1:
            add_issue(issues, "SEO", "Duplicate meta descriptions across multiple pages", "Low", "Quick",
                       f"{len(urls)} pages share an identical meta description: "
                       f"{', '.join(urls[:5])}{' ...' if len(urls) > 5 else ''}.",
                       ["Write a unique meta description per page reflecting that page's specific content."])

    for content_hash, urls in content_hashes.items():
        if content_hash and len(urls) > 1:
            add_issue(issues, "SEO", "Duplicate/near-duplicate main content across multiple pages", "Medium", "Involved",
                       f"{len(urls)} pages have effectively identical main body content (ignoring shared "
                       f"header/nav/footer): {', '.join(urls[:5])}{' ...' if len(urls) > 5 else ''}. This can "
                       "trigger search engine duplicate-content filtering, causing only one page to rank.",
                       ["Differentiate the pages' content, or canonicalize the duplicates to a single primary page.",
                        "If pages are meant to be nearly identical (e.g. seasonal duplicates), consolidate into one page with a canonical tag."])

    # Orphan pages: crawled pages with zero incoming internal links from other crawled pages
    for url in pages:
        if url == base_url:
            continue
        incoming = crawl_data["incoming_links"].get(url, set())
        incoming_from_others = incoming - {url}
        if not incoming_from_others:
            add_issue(issues, "Structure", "Orphaned page (no internal links found pointing to it)", "Medium", "Quick",
                       f"'{url}' was only reachable because it was already known, but no crawled page links "
                       "to it. Orphaned pages are hard for users and search engines to discover organically.",
                       ["Add a link to this page from relevant navigation, related-content, or footer sections.",
                        "If the page is obsolete, redirect or remove it instead of leaving it orphaned."],
                       page_url=url)

    # Broken links
    # Statuses that typically mean bot-blocking/rate-limiting rather than an
    # actually broken destination (many social platforms 429/403 automated
    # requests even though the link works fine in a real browser).
    LIKELY_BOT_BLOCK = {401, 403, 429}
    for link, (status, err) in link_status.items():
        referring_pages = [u for u, pd in pages.items() if link in pd.internal_links or link in pd.external_links]
        is_internal = any(link in pd.internal_links for pd in pages.values())
        if status is None or status >= 400:
            reason = err or f"HTTP {status}"
            if status in LIKELY_BOT_BLOCK:
                sev, effort = "Low", "Quick"
                title = f"Link could not be auto-verified: {link} ({reason})"
                why = (f"This link returned {reason} to our automated checker, which is common for social "
                       "platforms (Instagram, LinkedIn, etc.) that block bots/rate-limit non-browser "
                       "requests. It may work fine for real visitors - verify manually before treating it as broken.")
                solutions = ["Open the link in a normal browser to confirm it actually works.",
                             "If it's genuinely broken, update or remove it; if it just blocks bots, no action needed."]
            else:
                sev = "High" if is_internal else "Medium"
                effort = "Quick"
                title = f"Broken {'internal' if is_internal else 'external'} link: {link} ({reason})"
                why = (f"The link to '{link}' failed ({reason}). Broken links hurt user trust, waste crawl "
                       "budget, and (for internal links) can orphan pages.")
                solutions = ["Update the link to the correct current URL.",
                             "Remove the link if the destination page/resource no longer exists.",
                             "If internal, set up a 301 redirect from the old path to a valid page."]
            for ref in (referring_pages[:5] or [base_url]):
                add_issue(issues, "SEO", title, sev, effort, why, solutions, page_url=ref)

    return issues


# --------------------------------------------------------------------------
# Quick-wins selection / impact-effort matrix / time estimate
# --------------------------------------------------------------------------

def select_quick_wins(issues, min_items=3, max_items=5):
    def score(issue):
        return IMPACT_WEIGHT[issue.severity] / EFFORT_WEIGHT[issue.effort]

    candidates = [i for i in issues if i.severity in ("High", "Medium") and i.effort in ("Quick", "Moderate")]
    candidates.sort(key=score, reverse=True)
    if len(candidates) < min_items:
        remaining = [i for i in issues if i not in candidates]
        remaining.sort(key=score, reverse=True)
        candidates = candidates + remaining
    return candidates[:max_items]


def compute_impact_effort_matrix(issues):
    matrix = {"high_quick": 0, "high_involved": 0, "low_quick": 0, "low_involved": 0}
    for i in issues:
        high_impact = i.severity in ("High", "Medium")
        quick = i.effort == "Quick"
        if high_impact and quick:
            matrix["high_quick"] += 1
        elif high_impact and not quick:
            matrix["high_involved"] += 1
        elif not high_impact and quick:
            matrix["low_quick"] += 1
        else:
            matrix["low_involved"] += 1
    return matrix


def estimate_total_hours(issues):
    lo = sum(EFFORT_HOURS[i.effort][0] for i in issues)
    hi = sum(EFFORT_HOURS[i.effort][1] for i in issues)
    return lo, hi


# --------------------------------------------------------------------------
# PDF report
# --------------------------------------------------------------------------

def sanitize(text):
    """Make arbitrary scraped text safe for fpdf2's core (latin-1) fonts."""
    if text is None:
        return ""
    text = str(text)
    replacements = {
        "‘": "'", "’": "'", "“": '"', "”": '"',
        "–": "-", "—": "-", "…": "...", " ": " ",
        "•": "-", "→": "->", "é": "e",
    }
    for src, dst in replacements.items():
        text = text.replace(src, dst)
    return text.encode("latin-1", "replace").decode("latin-1")


class ReportPDF(FPDF):
    def __init__(self, site_url):
        super().__init__(orientation="P", unit="mm", format="A4")
        self.site_url = site_url
        self.set_auto_page_break(auto=True, margin=18)

    def footer(self):
        if self.page_no() == 1:
            return
        self.set_y(-15)
        self.set_font("Helvetica", "I", 8)
        self.set_text_color(120, 120, 120)
        self.cell(0, 10, sanitize(f"Site Audit Report - {self.site_url} - Page {self.page_no()}"),
                   align="C")


def draw_title_page(pdf, site_url, generated_at, pages_crawled):
    pdf.add_page()
    pdf.set_fill_color(33, 37, 41)
    pdf.rect(0, 0, pdf.w, 80, style="F")
    pdf.set_y(28)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Helvetica", "B", 26)
    pdf.cell(0, 14, "Website Audit Report", align="C", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 14)
    pdf.cell(0, 10, sanitize(site_url), align="C", new_x="LMARGIN", new_y="NEXT")

    pdf.set_text_color(30, 30, 30)
    pdf.set_y(100)
    pdf.set_font("Helvetica", "", 11)
    pdf.cell(0, 8, f"Generated: {generated_at}", align="C", new_x="LMARGIN", new_y="NEXT")
    pdf.cell(0, 8, f"Pages crawled: {pages_crawled}", align="C", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(10)
    pdf.set_font("Helvetica", "I", 10)
    pdf.set_text_color(90, 90, 90)
    pdf.multi_cell(0, 6,
                    "Automated technical audit covering performance, real-world Core Web Vitals, SEO, page "
                    "structure, mobile/UX, booking & conversion setup, analytics tracking, and passive security "
                    "hygiene. Findings are based on a rate-limited crawl of publicly accessible pages and should "
                    "be used as a prioritized starting point, not an exhaustive guarantee.",
                    align="C", new_x="LMARGIN", new_y="NEXT")


def draw_narrative_intro(pdf, narrative):
    """A standalone editorial-brief page - deliberately styled unlike the
    findings pages (no severity badge, no issue-card layout) so it reads as
    prose to skim first, not another entry in the list.

    The copy is hand-written per site and read from the "narrative" key of
    manual_findings/<domain>.json. Sites without one skip this page entirely:
    nothing is drawn and no page is started, so pagination and the footer's
    page numbering simply close up around it."""
    if not narrative:
        return

    heading = narrative.get("heading")
    paragraphs = [p for p in narrative.get("paragraphs", []) if p]
    footnote = narrative.get("footnote")
    closing = narrative.get("closing")
    if not (heading or paragraphs or footnote or closing):
        return

    pdf.add_page()
    pdf.set_y(22)

    if heading:
        pdf.set_font("Helvetica", "B", 20)
        pdf.set_text_color(198, 40, 40)
        pdf.multi_cell(0, 9.5, sanitize(heading),
                        new_x="LMARGIN", new_y="NEXT", align="L")

        pdf.set_draw_color(198, 40, 40)
        pdf.set_line_width(0.8)
        pdf.line(10, pdf.get_y() + 1, 70, pdf.get_y() + 1)
        pdf.set_line_width(0.2)
        pdf.ln(9)

    pdf.set_font("Helvetica", "", 11.5)
    pdf.set_text_color(30, 30, 30)

    for p in paragraphs:
        pdf.multi_cell(0, 6.3, sanitize(p), new_x="LMARGIN", new_y="NEXT", align="L")
        pdf.ln(4)

    if footnote:
        pdf.set_font("Helvetica", "I", 9.5)
        pdf.set_text_color(90, 90, 90)
        pdf.multi_cell(0, 5.5, sanitize(footnote),
                        new_x="LMARGIN", new_y="NEXT", align="L")
        pdf.ln(6)

    if closing:
        pdf.set_font("Helvetica", "", 11.5)
        pdf.set_text_color(30, 30, 30)
        pdf.multi_cell(0, 6.3, sanitize(closing),
                        new_x="LMARGIN", new_y="NEXT", align="L")


def draw_quick_wins(pdf, quick_wins, hours_range):
    pdf.add_page()
    pdf.set_fill_color(232, 245, 233)
    pdf.rect(0, 0, pdf.w, 34, style="F")
    pdf.set_y(9)
    pdf.set_font("Helvetica", "B", 20)
    pdf.set_text_color(27, 94, 32)
    pdf.cell(0, 12, "Fix These First", align="C", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 10.5)
    pdf.set_text_color(60, 60, 60)
    pdf.cell(0, 7, "The best-value fixes: high impact, low-to-moderate effort", align="C", new_x="LMARGIN", new_y="NEXT")
    pdf.set_y(40)

    for idx, issue in enumerate(quick_wins, start=1):
        r, g, b = SEVERITY_COLOR[issue.severity]
        pdf.set_x(14)
        pdf.set_font("Helvetica", "B", 13)
        pdf.set_text_color(r, g, b)
        pdf.cell(9, 8, f"{idx}.")
        pdf.set_text_color(20, 20, 20)
        pdf.multi_cell(pdf.w - 33, 8, sanitize(issue.issue), new_x="LMARGIN", new_y="NEXT", align="L")

        pdf.set_x(23)
        pdf.set_font("Helvetica", "", 9)
        pdf.set_text_color(90, 90, 90)
        n_pages = len(issue.pages) if issue.pages else 0
        affected = f"{n_pages} page(s) affected" if n_pages else "site-wide"
        pdf.cell(0, 5.5, f"{issue.severity} impact  -  {issue.effort} fix  -  {affected}", new_x="LMARGIN", new_y="NEXT")
        pdf.ln(1)

        pdf.set_x(23)
        pdf.set_font("Helvetica", "", 10.5)
        pdf.set_text_color(40, 40, 40)
        one_liner = issue.why.split(". ")[0].strip().rstrip(".") + "."
        pdf.multi_cell(pdf.w - 33, 5.5, sanitize(one_liner), new_x="LMARGIN", new_y="NEXT", align="L")

        pdf.set_x(23)
        pdf.set_font("Helvetica", "B", 10)
        pdf.set_text_color(27, 94, 32)
        pdf.multi_cell(pdf.w - 33, 5.5, sanitize(f"Best fix: {issue.solutions[0]}"), new_x="LMARGIN", new_y="NEXT", align="L")
        pdf.ln(5)

    pdf.set_draw_color(220, 220, 220)
    pdf.line(10, pdf.get_y(), pdf.w - 10, pdf.get_y())
    pdf.ln(4)
    pdf.set_x(10)
    pdf.set_font("Helvetica", "I", 9.5)
    pdf.set_text_color(110, 110, 110)
    pdf.multi_cell(0, 5.5,
                    f"Estimated time to address every finding in this report: ~{hours_range[0]:.0f}-{hours_range[1]:.0f} "
                    "hours (a rough scoping estimate for someone familiar with the WordPress/Elementor stack - see "
                    "the Impact x Effort matrix on the next page for the full breakdown).",
                    new_x="LMARGIN", new_y="NEXT", align="L")


def draw_impact_matrix(pdf, matrix):
    pdf.set_font("Helvetica", "B", 13)
    pdf.set_text_color(20, 20, 20)
    pdf.cell(0, 9, "Impact x Effort Matrix", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 9)
    pdf.set_text_color(90, 90, 90)
    pdf.cell(0, 5, "(counts are distinct issue types found, not per-page instances)", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(3)

    label_w, col_w, row_h, header_h = 34, 45, 18, 7
    x0 = 20
    y0 = pdf.get_y()

    pdf.set_xy(x0 + label_w, y0)
    pdf.set_font("Helvetica", "B", 10)
    pdf.set_text_color(40, 40, 40)
    pdf.cell(col_w, header_h, "Quick Fix", align="C")
    pdf.cell(col_w, header_h, "Involved", align="C")

    def cell_block(x, y, w, h, count, bg):
        pdf.set_fill_color(*bg)
        pdf.rect(x, y, w, h, style="F")
        pdf.set_xy(x, y + h / 2 - 4.5)
        pdf.set_font("Helvetica", "B", 16)
        pdf.set_text_color(30, 30, 30)
        pdf.cell(w, 9, str(count), align="C")

    y1 = y0 + header_h
    pdf.set_xy(x0, y1 + row_h / 2 - 3)
    pdf.set_font("Helvetica", "B", 10)
    pdf.set_text_color(40, 40, 40)
    pdf.cell(label_w, 6, "High Impact", align="L")
    cell_block(x0 + label_w, y1, col_w, row_h, matrix["high_quick"], SEVERITY_COLOR_LIGHT["High"])
    cell_block(x0 + label_w + col_w, y1, col_w, row_h, matrix["high_involved"], SEVERITY_COLOR_LIGHT["Medium"])

    y2 = y1 + row_h
    pdf.set_xy(x0, y2 + row_h / 2 - 3)
    pdf.set_font("Helvetica", "B", 10)
    pdf.set_text_color(40, 40, 40)
    pdf.cell(label_w, 6, "Low Impact", align="L")
    cell_block(x0 + label_w, y2, col_w, row_h, matrix["low_quick"], SEVERITY_COLOR_LIGHT["Low"])
    cell_block(x0 + label_w + col_w, y2, col_w, row_h, matrix["low_involved"], (235, 235, 235))

    pdf.set_y(y2 + row_h + 6)


def draw_executive_summary(pdf, issues, matrix, hours_range):
    pdf.add_page()
    pdf.set_font("Helvetica", "B", 18)
    pdf.set_text_color(20, 20, 20)
    pdf.cell(0, 12, "Executive Summary", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(2)

    total = sum(len(i.pages) if i.pages else 1 for i in issues)
    by_sev = Counter()
    by_cat = Counter()
    for i in issues:
        n = len(i.pages) if i.pages else 1
        by_sev[i.severity] += n
        by_cat[i.category] += n

    pdf.set_font("Helvetica", "", 12)
    pdf.cell(0, 8, f"Total issue instances found: {total}", new_x="LMARGIN", new_y="NEXT")
    pdf.cell(0, 8, f"Distinct issue types: {len(issues)}", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(4)

    pdf.set_font("Helvetica", "B", 13)
    pdf.cell(0, 9, "By Severity", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 11)
    for sev in ("High", "Medium", "Low"):
        count = by_sev.get(sev, 0)
        r, g, b = SEVERITY_COLOR[sev]
        pdf.set_fill_color(r, g, b)
        pdf.rect(pdf.get_x(), pdf.get_y() + 1, 4, 4, style="F")
        pdf.set_x(pdf.get_x() + 7)
        pdf.cell(60, 7, f"{sev}: {count}", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(4)

    pdf.set_font("Helvetica", "B", 13)
    pdf.cell(0, 9, "By Category", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 11)
    for cat, count in sorted(by_cat.items(), key=lambda kv: -kv[1]):
        pdf.cell(0, 7, f"- {cat}: {count}", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(6)

    draw_impact_matrix(pdf, matrix)

    pdf.set_font("Helvetica", "I", 9.5)
    pdf.set_text_color(110, 110, 110)
    pdf.multi_cell(0, 5.5,
                    f"Estimated time to address every finding: ~{hours_range[0]:.0f}-{hours_range[1]:.0f} hours total, "
                    "based on effort tags per issue type. Useful as a rough scope for a fix-it engagement, not a "
                    "firm quote.",
                    new_x="LMARGIN", new_y="NEXT", align="L")


def draw_cwv_table(pdf, crawl_data):
    pages_with_psi = [(u, pd) for u, pd in crawl_data["pages"].items() if pd.ok and pd.psi]
    if not pages_with_psi:
        return

    any_success = any(
        (psi is not None and not psi.error)
        for _, pd in pages_with_psi
        for psi in pd.psi.values()
    )

    base_url = crawl_data["base_url"]
    pdf.add_page()
    pdf.set_font("Helvetica", "B", 18)
    pdf.set_text_color(20, 20, 20)
    pdf.cell(0, 12, "Core Web Vitals by Page", new_x="LMARGIN", new_y="NEXT")

    if not any_success:
        pdf.ln(4)
        pdf.set_font("Helvetica", "", 11)
        pdf.set_text_color(60, 60, 60)
        pdf.multi_cell(0, 6,
                        "Google PageSpeed Insights data could not be retrieved this run - the free, "
                        "unauthenticated API tier was rate-limited/quota-exceeded after only a handful of "
                        "requests.",
                        new_x="LMARGIN", new_y="NEXT", align="L")
        pdf.ln(3)
        pdf.set_font("Helvetica", "B", 11)
        pdf.set_text_color(20, 20, 20)
        pdf.cell(0, 7, "To get real Core Web Vitals data on the next run:", new_x="LMARGIN", new_y="NEXT")
        pdf.set_font("Helvetica", "", 10.5)
        pdf.set_text_color(60, 60, 60)
        pdf.set_x(14)
        pdf.multi_cell(0, 6, "1. Register a free key at developers.google.com/speed/docs/insights/v5/get-started",
                        new_x="LMARGIN", new_y="NEXT", align="L")
        pdf.set_x(14)
        pdf.multi_cell(0, 6, "2. Set it as the PAGESPEED_API_KEY environment variable before running audit.py",
                        new_x="LMARGIN", new_y="NEXT", align="L")
        pdf.set_x(14)
        pdf.multi_cell(0, 6, "3. Re-run - results are cached for 7 days, so repeat runs stay fast.",
                        new_x="LMARGIN", new_y="NEXT", align="L")
        return

    pdf.set_font("Helvetica", "", 9.5)
    pdf.set_text_color(90, 90, 90)
    pdf.multi_cell(0, 5,
                    "Real-world Google PageSpeed Insights results, Mobile / Desktop side by side ('-' means no "
                    "data - see the log for whether the API was rate-limited). Mobile is usually worse and more "
                    "important since it's what most visitors and Google's ranking algorithm primarily evaluate.",
                    new_x="LMARGIN", new_y="NEXT", align="L")
    pdf.ln(2)

    col_widths = [58, 31, 31, 33, 33]
    headers = ["Page", "Perf (M/D)", "LCP (M/D)", "CLS (M/D)", "INP/TBT (M/D)"]

    def draw_header():
        pdf.set_font("Helvetica", "B", 8.5)
        pdf.set_fill_color(235, 235, 235)
        pdf.set_text_color(30, 30, 30)
        for w, h in zip(col_widths, headers):
            pdf.cell(w, 7, h, align="C", fill=True)
        pdf.ln(7)

    draw_header()
    pdf.set_font("Helvetica", "", 8)

    def fmt_score(x):
        return str(x.performance_score) if x and x.performance_score is not None else "-"

    def fmt_lcp(x):
        return x.lcp_display if x and x.lcp_display else "-"

    def fmt_cls(x):
        return f"{x.cls:.2f}" if x and x.cls is not None else "-"

    def fmt_resp(x):
        if not x:
            return "-"
        if x.used_inp and x.inp_ms is not None:
            return f"{x.inp_ms:.0f}ms"
        if x.tbt_ms is not None:
            return f"{x.tbt_ms:.0f}ms"
        return "-"

    for i, (url, pd) in enumerate(pages_with_psi):
        if pdf.get_y() > pdf.h - 20:
            pdf.add_page()
            draw_header()
            pdf.set_font("Helvetica", "", 8)

        m = pd.psi.get("mobile")
        d = pd.psi.get("desktop")
        label = urlparse(url).path or "/"
        if label != "/" and label == urlparse(base_url).path:
            label = "/ (home)"
        if len(label) > 26:
            label = label[:23] + "..."

        fill = (i % 2 == 0)
        if fill:
            pdf.set_fill_color(248, 248, 248)
        pdf.set_text_color(30, 30, 30)
        pdf.cell(col_widths[0], 6, sanitize(label), fill=fill)
        pdf.cell(col_widths[1], 6, f"{fmt_score(m)} / {fmt_score(d)}", align="C", fill=fill)
        pdf.cell(col_widths[2], 6, f"{fmt_lcp(m)} / {fmt_lcp(d)}", align="C", fill=fill)
        pdf.cell(col_widths[3], 6, f"{fmt_cls(m)} / {fmt_cls(d)}", align="C", fill=fill)
        pdf.cell(col_widths[4], 6, f"{fmt_resp(m)} / {fmt_resp(d)}", align="C", fill=fill)
        pdf.ln(6)


def draw_findings(pdf, issues):
    pdf.add_page()
    pdf.set_font("Helvetica", "B", 18)
    pdf.set_text_color(20, 20, 20)
    pdf.cell(0, 12, "Detailed Findings", new_x="LMARGIN", new_y="NEXT")
    pdf.ln(2)

    ordered = sorted(issues, key=lambda i: (SEVERITY_ORDER[i.severity], i.category, i.issue))

    for idx, issue in enumerate(ordered, start=1):
        _draw_single_finding(pdf, idx, issue)


def _draw_single_finding(pdf, idx, issue):
    # Reserve roughly the space needed for the badge row; if too close to
    # bottom, start a fresh page so the badge doesn't get orphaned.
    if pdf.get_y() > pdf.h - 55:
        pdf.add_page()

    r, g, b = SEVERITY_COLOR[issue.severity]
    lr, lg, lb = SEVERITY_COLOR_LIGHT[issue.severity]

    pdf.set_fill_color(lr, lg, lb)
    start_y = pdf.get_y()
    pdf.rect(10, start_y, pdf.w - 20, 8, style="F")
    pdf.set_xy(12, start_y + 1)
    pdf.set_font("Helvetica", "B", 10)
    pdf.set_text_color(r, g, b)
    pdf.cell(32, 6, issue.severity.upper())
    pdf.set_font("Helvetica", "", 9)
    pdf.set_text_color(90, 90, 90)
    pdf.cell(38, 6, f"[{issue.effort}]")
    pdf.set_text_color(60, 60, 60)
    pdf.set_font("Helvetica", "", 10)
    pdf.cell(0, 6, sanitize(f"{issue.category}"), align="R")
    pdf.ln(9)

    pdf.set_x(10)
    pdf.set_font("Helvetica", "B", 12)
    pdf.set_text_color(20, 20, 20)
    pdf.multi_cell(0, 6.5, sanitize(f"{idx}. {issue.issue}"), new_x="LMARGIN", new_y="NEXT", align="L")

    pdf.set_font("Helvetica", "B", 9.5)
    pdf.set_text_color(80, 80, 80)
    if issue.pages:
        shown = issue.pages[:4]
        page_line = "Page(s): " + ", ".join(shown)
        if len(issue.pages) > 4:
            page_line += f" (+{len(issue.pages) - 4} more)"
    else:
        page_line = "Page(s): site-wide"
    pdf.set_font("Helvetica", "", 9.5)
    pdf.multi_cell(0, 5.5, sanitize(page_line), new_x="LMARGIN", new_y="NEXT", align="L")
    pdf.ln(1)

    pdf.set_font("Helvetica", "B", 10)
    pdf.set_text_color(20, 20, 20)
    pdf.cell(0, 6, "Why it matters:", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 10)
    pdf.multi_cell(0, 5.5, sanitize(issue.why), new_x="LMARGIN", new_y="NEXT", align="L")
    pdf.ln(1)

    pdf.set_font("Helvetica", "B", 10)
    pdf.cell(0, 6, "Possible solutions:", new_x="LMARGIN", new_y="NEXT")
    pdf.set_font("Helvetica", "", 10)
    for sol in issue.solutions:
        pdf.set_x(14)
        pdf.multi_cell(0, 5.5, sanitize(f"- {sol}"), new_x="LMARGIN", new_y="NEXT", align="L")
    pdf.ln(4)
    pdf.set_draw_color(220, 220, 220)
    pdf.line(10, pdf.get_y(), pdf.w - 10, pdf.get_y())
    pdf.ln(4)


def build_pdf(site_url, issues, crawl_data, output_path):
    pdf = ReportPDF(site_url)
    generated_at = datetime.now().strftime("%Y-%m-%d %H:%M")
    pages_crawled = len(crawl_data["pages"])
    draw_title_page(pdf, site_url, generated_at, pages_crawled)

    draw_narrative_intro(pdf, load_manual_data(site_url).get("narrative"))

    quick_wins = select_quick_wins(issues)
    hours_range = estimate_total_hours(issues)
    if quick_wins:
        draw_quick_wins(pdf, quick_wins, hours_range)

    matrix = compute_impact_effort_matrix(issues)
    draw_executive_summary(pdf, issues, matrix, hours_range)

    draw_cwv_table(pdf, crawl_data)

    draw_findings(pdf, issues)
    pdf.output(output_path)
    log.info("PDF report written to %s", output_path)


# --------------------------------------------------------------------------
# Checkpoint (lets the PDF be rebuilt - e.g. to add manual findings below -
# without re-crawling the site or re-hitting the PageSpeed API)
# --------------------------------------------------------------------------

def state_file_path(base_url):
    """Checkpoint filename for this specific site."""
    return STATE_FILE_TEMPLATE.format(domain=domain_key(base_url))


def output_pdf_path(base_url, override=None):
    """Report filename for this site and date, or override verbatim if given."""
    if override:
        return override
    return OUTPUT_PDF_TEMPLATE.format(domain=domain_key(base_url),
                                       date=datetime.now().strftime("%Y-%m-%d"))


def save_state(crawl_data, issues):
    base_url = crawl_data["base_url"]
    path = state_file_path(base_url)
    try:
        with open(path, "wb") as f:
            pickle.dump({"base_url": base_url, "crawl_data": crawl_data, "issues": issues}, f)
    except (OSError, pickle.PickleError) as exc:
        log.warning("Could not write state checkpoint: %s", exc)


def load_state(base_url):
    """Load the checkpoint for base_url, or (None, None) to force a fresh run.

    The checkpoint is only reused when the base_url stored inside it matches
    the site being audited. A mismatched or unlabelled checkpoint is ignored
    with a warning rather than silently producing a report about the wrong
    business."""
    path = state_file_path(base_url)
    if not os.path.exists(path):
        return None, None
    try:
        with open(path, "rb") as f:
            data = pickle.load(f)
        stored_url = data.get("base_url")
        crawl_data = data.get("crawl_data")
        if stored_url is None and isinstance(crawl_data, dict):
            stored_url = crawl_data.get("base_url")
        if not stored_url:
            log.warning("Checkpoint %s does not record which site it is for - ignoring it and "
                        "running the full pipeline fresh.", path)
            return None, None
        if normalize_url(stored_url) != normalize_url(base_url):
            log.warning("Checkpoint %s was built for %s but this run audits %s - ignoring the "
                        "checkpoint and running the full pipeline fresh.", path, stored_url, base_url)
            return None, None
        return crawl_data, data.get("issues")
    except (OSError, pickle.PickleError, EOFError, AttributeError) as exc:
        log.warning("Could not load state checkpoint (%s) - will rebuild from scratch", exc)
        return None, None


# --------------------------------------------------------------------------
# Manually-specified findings
#
# Confirmed by hand via Google's PageSpeed Insights web UI (pagespeed.web.dev)
# rather than pulled automatically by this script's PSI integration above -
# added as regular Issue entries so they sort, group, and appear in the
# quick-wins/matrix exactly like every auto-detected finding.
#
# Stored per-site in manual_findings/<domain>.json (paths in "pages" are
# relative to the base URL; "" means the base URL itself). A site with no
# file for its domain gets no manual findings at all.
# --------------------------------------------------------------------------

MANUAL_FINDINGS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "manual_findings")


def manual_findings_path(base_url):
    """Path to the per-site manual findings file for base_url."""
    return os.path.join(MANUAL_FINDINGS_DIR, f"{domain_key(base_url)}.json")


def load_manual_data(base_url):
    """Read manual_findings/<domain>.json, or return {} if there is nothing
    usable for this site.

    Accepts either a bare JSON list (findings only) or an object with
    "findings" and/or "narrative" keys. A missing file is normal and silent;
    an unreadable or malformed one logs a warning and is skipped."""
    path = manual_findings_path(base_url)
    if not os.path.exists(path):
        return {}

    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        if isinstance(data, list):
            data = {"findings": data}
        if not isinstance(data, dict):
            raise ValueError("expected a JSON object or list")
        findings = data.get("findings", [])
        if not isinstance(findings, list):
            raise ValueError("'findings' must be a list")
        data["findings"] = findings
        return data
    except (OSError, ValueError) as exc:  # ValueError covers JSONDecodeError
        log.warning("Skipping manual content - could not read %s: %s", path, exc)
        return {}


def add_manual_findings(issues, base_url):
    """Add hand-confirmed findings for this specific site, if any exist.

    Findings live in manual_findings/<domain>.json so they never leak across
    sites; a site with no file simply gets no manual findings."""
    path = manual_findings_path(base_url)
    findings = load_manual_data(base_url).get("findings", [])

    loaded = 0
    for idx, finding in enumerate(findings):
        try:
            category = finding["category"]
            issue_text = finding["issue"]
            severity = finding["severity"]
            effort = finding["effort"]
            why = finding["why"]
            solutions = list(finding["solutions"])
            page_detail = finding.get("page_detail")
            pages = finding.get("pages", [""])
            if not isinstance(pages, list):
                raise TypeError("'pages' must be a list")
        except (TypeError, KeyError, AttributeError) as exc:
            log.warning("Skipping malformed manual finding #%d in %s: %s", idx + 1, path, exc)
            continue

        for page_path in pages:
            page_url = f"{base_url.rstrip('/')}{page_path}" if page_path else base_url
            add_issue(issues, category, issue_text, severity, effort, why, solutions,
                       page_url=page_url, page_detail=page_detail)
        loaded += 1

    if loaded:
        log.info("Loaded %d manual finding(s) from %s", loaded, os.path.basename(path))


# --------------------------------------------------------------------------
# Platform detection
#
# This drives a commercial decision, not a cosmetic label, so it is tuned for
# precision over coverage: a platform is only claimed on a signal that no
# other stack realistically produces, and anything weaker returns "unknown".
# A wrong answer sends a pitch to someone who cannot act on it, or skips
# someone who can - both cost more than an honest "unknown".
#
# The distinction that matters commercially:
#   - Wix/Squarespace own the rendering pipeline. Their performance ceiling is
#     not the owner's to raise and not ours to sell.
#   - WordPress with a page builder is the opposite: the bloat belongs to the
#     site owner, is measurable, and is removable by us.
# --------------------------------------------------------------------------

PLATFORM_OWNS_PERFORMANCE = {"wix", "squarespace"}

# (label, [substrings matched against asset URLs / inline script text])
PLATFORM_ASSET_SIGNALS = [
    ("wordpress",   ["/wp-content/", "/wp-includes/", "/wp-json/"]),
    ("wix",         ["static.parastorage.com", "static.wixstatic.com", "wix-code", "wixsite.com"]),
    ("squarespace", ["static1.squarespace.com", "squarespace-cdn.com", "assets.squarespace.com"]),
    ("shopify",     ["cdn.shopify.com", "shopifycloud.com", "shopify.theme", "myshopify.com"]),
    ("webflow",     ["assets.website-files.com", "assets-global.website-files.com",
                      "cdn.prod.website-files.com", "webflow.js"]),
    ("framer",      ["framerusercontent.com", "framer.com/m/", "framer-motion"]),
]

# Page builders, checked only once WordPress is established. Ordered so that
# an explicit builder wins over Gutenberg, which ships with WordPress itself.
BUILDER_SIGNALS = [
    ("Elementor", ["/plugins/elementor/", "elementor-frontend", "elementor-page",
                    "elementor-widget", "elementor-section"]),
    ("Divi",      ["/themes/divi/", "et_pb_", "et-core", "divi-builder"]),
    ("WPBakery",  ["js_composer", "vc_row", "wpb_wrapper", "/js_composer/"]),
    ("Beaver",    ["/bb-plugin/", "fl-builder", "fl-node-"]),
    ("Gutenberg", ["wp-block-", "/block-library/", "wp-container-"]),
]

GENERATOR_SIGNALS = [
    ("wordpress", "wordpress"),
    ("wix", "wix.com"),
    ("squarespace", "squarespace"),
    ("shopify", "shopify"),
    ("webflow", "webflow"),
    ("framer", "framer"),
    ("drupal", "drupal"),
    ("joomla", "joomla"),
]

HEADER_SIGNALS = [
    ("wix", ["x-wix-request-id", "x-wix-published-version"]),
    ("squarespace", ["x-contextid"]),
    ("shopify", ["x-shopid", "x-shopify-stage"]),
]

# Frontend frameworks. Only reported when nothing above matched, and only as
# "react/custom" - the framework says who built it, not what the owner can change.
FRAMEWORK_SIGNALS = ["__next_data__", "/_next/static", "data-reactroot", "react-dom",
                      "__nuxt__", "ng-version", "data-svelte"]


@dataclass
class PlatformInfo:
    platform: str = "unknown"
    page_builder: str = ""
    confidence: str = "none"   # strong | weak | none
    signals: list = field(default_factory=list)

    @property
    def owns_performance(self):
        """True when the platform, not the site owner, controls the
        performance ceiling - so speed findings are not sellable work."""
        return self.platform in PLATFORM_OWNS_PERFORMANCE


def _platform_haystack(pd, soup):
    """Asset URLs plus a bounded slice of inline markup. Inline text is capped
    because homepages can carry megabytes of inline JSON, and every signal we
    look for appears early if it appears at all."""
    parts = list(pd.script_srcs or [])
    parts.extend(pd.image_srcs or [])
    for tag in soup.find_all("link", href=True):
        parts.append(tag["href"])
    body = str(soup)[:200_000]
    parts.append(body)
    return " ".join(parts).lower()


def detect_platform(pd, soup):
    """Identify the CMS/site builder and, for WordPress, the page builder.

    Returns PlatformInfo with confidence 'strong' when a generator tag, a
    platform-owned header, or two independent asset signals agree; 'weak' when
    a single asset signal matched; 'none' (platform 'unknown') otherwise.
    Weak matches still report the platform but are flagged, so a caller that
    needs certainty can require confidence == 'strong'."""
    signals = []
    haystack = _platform_haystack(pd, soup)

    generator = soup.find("meta", attrs={"name": re.compile("^generator$", re.I)})
    generator_content = (generator.get("content", "") or "").lower() if generator else ""

    headers_lower = {k.lower() for k in (pd.headers or {})}

    platform = ""
    confidence = "none"

    # 1. Generator meta tag - the site telling us directly.
    for label, needle in GENERATOR_SIGNALS:
        if needle in generator_content:
            platform, confidence = label, "strong"
            signals.append(f"generator:{needle}")
            break

    # 2. Platform-owned response headers - not forgeable by a theme.
    if not platform:
        for label, header_names in HEADER_SIGNALS:
            hit = [h for h in header_names if h in headers_lower]
            if hit:
                platform, confidence = label, "strong"
                signals.append(f"header:{hit[0]}")
                break

    # 3. Asset URL patterns. Two independent hits to claim strong, one is weak.
    if not platform:
        for label, needles in PLATFORM_ASSET_SIGNALS:
            hits = [n for n in needles if n in haystack]
            if hits:
                platform = label
                confidence = "strong" if len(hits) >= 2 else "weak"
                signals.extend(f"asset:{h}" for h in hits[:3])
                break

    # 4. Frontend framework, only when no CMS matched at all.
    if not platform:
        hits = [n for n in FRAMEWORK_SIGNALS if n in haystack]
        if hits:
            platform = "react/custom"
            confidence = "strong" if len(hits) >= 2 else "weak"
            signals.extend(f"framework:{h}" for h in hits[:3])

    if not platform:
        return PlatformInfo(platform="unknown", confidence="none", signals=[])

    builder = ""
    if platform == "wordpress":
        for label, needles in BUILDER_SIGNALS:
            hits = [n for n in needles if n in haystack]
            if hits:
                builder = label
                signals.extend(f"builder:{h}" for h in hits[:2])
                break

    return PlatformInfo(platform=platform, page_builder=builder,
                        confidence=confidence, signals=signals)


# --------------------------------------------------------------------------
# Platform-appropriate remediation advice
#
# Findings are detected identically on every platform - a 4MB page is a 4MB
# page. Only the fix text is platform-specific, so it is rewritten here at
# output time rather than branching inside every detector.
#
# Substitution over deletion: a bullet naming WordPress-only tooling is
# replaced with its generic equivalent, not dropped, because a finding with
# vaguer advice is more useful than a finding with no advice.
# --------------------------------------------------------------------------

# (regex matched against a solution bullet, generic replacement)
WORDPRESS_ADVICE_SUBSTITUTIONS = [
    (re.compile(r"enable elementor's built-in native lazy-loading[^.]*\.", re.I),
     "Enable lazy loading in your theme or site builder's performance settings."),
    (re.compile(r"use a lazy-load plugin[^.]*\.", re.I),
     "Enable lazy loading for below-the-fold images, or add loading=\"lazy\" to their <img> tags."),
    (re.compile(r"re-save/re-insert images through the media library[^.]*\.", re.I),
     "Re-insert the images through your site builder so width and height attributes are set."),
    (re.compile(r"(install/?e?n?a?b?l?e?|use) (yoast|rankmath|aioseo)[^.]*\.", re.I),
     "Use your platform's built-in SEO settings, or an SEO app/extension, to set this."),
    (re.compile(r"[^.]*\byoast/rankmath\b[^.]*\.", re.I),
     "Set this in your platform's page/SEO settings."),
    (re.compile(r"enable a caching plugin[^.]*\.", re.I),
     "Enable caching and a CDN through your platform or host."),
    (re.compile(r"audit and disable unused elementor widgets/plugins[^.]*\.", re.I),
     "Audit installed apps/extensions and remove any that load on every page without being used."),
    (re.compile(r"upgrade hosting tier or move to managed wordpress hosting[^.]*\.", re.I),
     "Upgrade to a faster hosting tier or plan."),
    (re.compile(r"remove unused elementor widgets/sections[^.]*\.", re.I),
     "Remove unused page sections and embedded widgets that add hidden weight."),
    (re.compile(r"reduce the number of nested elementor sections/columns[^.]*\.", re.I),
     "Reduce deeply nested page sections and columns."),
    (re.compile(r"use an asset-unloading plugin[^.]*\.", re.I),
     "Load scripts only on the pages that need them."),
    (re.compile(r"(minify and combine css/js via a performance plugin|use a performance plugin's[^.]*)\.", re.I),
     "Minify and combine CSS/JS, and defer non-critical JavaScript."),
    (re.compile(r"install google tag manager site-wide via a plugin[^.]*\.", re.I),
     "Install Google Tag Manager site-wide through your platform's integrations or header-code setting."),
    (re.compile(r"add missing headers via a security plugin[^.]*\.", re.I),
     "Add the missing headers through your host or CDN configuration (e.g. Cloudflare)."),
    (re.compile(r"force https site-wide via wordpress settings[^.]*\.", re.I),
     "Force HTTPS site-wide in your platform or host settings."),
    (re.compile(r"add a single, keyword-relevant h1 via the page/elementor heading widget\.", re.I),
     "Add a single, keyword-relevant H1 using your page editor's heading element."),
    (re.compile(r"check elementor templates[^.]*\.", re.I),
     "Check your page templates in case the H1 is styled as a plain text element."),
    (re.compile(r"use a security plugin to strip version query strings[^.]*\.", re.I),
     "Strip version query strings from asset URLs at the host or CDN level."),
    (re.compile(r"remove the generator meta tag \(many security plugins[^)]*\)\.", re.I),
     "Remove the generator meta tag if your platform allows it."),
    (re.compile(r"consider a script-management plugin[^.]*\.", re.I),
     "Load scripts conditionally so each page only requests what it uses."),
    (re.compile(r"add descriptive alt text to each image in the media library\.", re.I),
     "Add descriptive alt text to each image in your platform's media manager."),
]

# Residual platform-specific vocabulary in text we did not explicitly rewrite.
GENERIC_TERM_SUBSTITUTIONS = [
    (re.compile(r"\bElementor-built\b", re.I), "builder-built"),
    (re.compile(r"\bElementor\b"), "the page builder"),
    (re.compile(r"\bWordPress/Elementor\b", re.I), "site builder"),
    (re.compile(r"\bWordPress\b"), "the site platform"),
    (re.compile(r"\bplugins?\b"), "apps/extensions"),
]


def _genericize(text):
    for pattern, replacement in GENERIC_TERM_SUBSTITUTIONS:
        text = pattern.sub(replacement, text)
    return text


def apply_platform_advice(issues, platform_info):
    """Rewrite WordPress-specific remediation advice for non-WordPress sites.

    A complete no-op for WordPress and for unknown platforms - if we could not
    identify the stack we have no basis to rewrite its advice, and the existing
    wording is the more useful default. That also means this cannot perturb the
    existing WordPress report."""
    platform = getattr(platform_info, "platform", "unknown")
    if platform in ("wordpress", "unknown"):
        return issues

    for issue in issues:
        rewritten = []
        for bullet in issue.solutions:
            new_bullet = bullet
            for pattern, replacement in WORDPRESS_ADVICE_SUBSTITUTIONS:
                if pattern.search(new_bullet):
                    new_bullet = pattern.sub(replacement, new_bullet).strip()
                    break
            new_bullet = _genericize(new_bullet)
            if new_bullet and new_bullet not in rewritten:
                rewritten.append(new_bullet)

        # A finding must never end up with no advice at all.
        issue.solutions = rewritten or [
            "Review this on your platform and apply the equivalent fix in its settings."]
        issue.why = _genericize(issue.why)

        if platform in PLATFORM_OWNS_PERFORMANCE and issue.category == "Performance":
            issue.solutions.append(
                f"Note: {platform.title()} controls most of this page's loading pipeline, so "
                "the achievable ceiling here is limited by the platform itself.")

    return issues


# --------------------------------------------------------------------------
# Screen mode - fast homepage-only triage across many prospects
#
# Deliberately not a mini-audit: one GET per site, no crawl, no link or image
# checking, no PDF, no state pickle. Detection reuses detect_issues() with
# include_site_level=False rather than a second copy that could drift.
# --------------------------------------------------------------------------

def load_places_cache():
    return load_json_cache(PLACES_CACHE_FILE, "Places")


def save_places_cache(cache):
    save_json_cache(PLACES_CACHE_FILE, cache, "Places")


def lookup_website(name, address, cache):
    """Resolve a business's website via Google Places Text Search.

    Returns (url_or_empty, error_or_empty, billed) where billed is True only
    when a request actually went to the API, so the caller can enforce a cap
    on spend. Cached negatives count as resolved - a business with no website
    is a real answer worth remembering."""
    query = " ".join(p for p in (name, address) if p).strip()
    if not query:
        return "", "no name or address to search", False

    key = f"places:{query.lower()}"
    cached = cache.get(key)
    if cached and (time.time() - cached.get("_fetched_at", 0)) < PLACES_CACHE_TTL_SECONDS:
        return cached.get("website", ""), cached.get("error", ""), False

    if not PLACES_API_KEY:
        return "", "no PLACES_API_KEY/PAGESPEED_API_KEY set", False

    limiter.wait()
    website, error = "", ""
    try:
        resp = requests.post(
            PLACES_API_URL,
            json={"textQuery": query, "maxResultCount": 1},
            headers={"Content-Type": "application/json",
                      "X-Goog-Api-Key": PLACES_API_KEY,
                      "X-Goog-FieldMask": "places.websiteUri"},
            timeout=REQUEST_TIMEOUT)
    except requests.exceptions.RequestException as exc:
        return "", f"places request failed: {exc}", True

    if resp.status_code != 200:
        detail = "quota/permission denied" if resp.status_code in (401, 403, 429) else f"HTTP {resp.status_code}"
        return "", f"places lookup failed: {detail}", True

    try:
        places = (resp.json() or {}).get("places") or []
        website = (places[0].get("websiteUri", "") if places else "").strip()
        if not website:
            error = "no website listed for this business"
    except (ValueError, AttributeError, IndexError, TypeError) as exc:
        error = f"unexpected places response: {exc}"

    cache[key] = {"website": website, "error": error, "_fetched_at": time.time()}
    return website, error, True


def read_prospects(path):
    """Read the input CSV, preserving column order and any extra columns."""
    with open(path, "r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        if not reader.fieldnames:
            raise ValueError(f"{path} has no header row")
        return [dict(row) for row in reader], list(reader.fieldnames)


def write_prospects(path, rows, fieldnames):
    """Write resolved websites back to the input CSV atomically, so an
    interrupted run cannot leave a half-written prospect list."""
    tmp = f"{path}.tmp"
    try:
        with open(tmp, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(rows)
        os.replace(tmp, path)
    except OSError as exc:
        log.warning("Could not write resolved websites back to %s: %s", path, exc)
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except OSError:
                pass


def resolve_websites(rows, fieldnames, csv_path, max_lookups):
    """Fill blank website cells via Places, writing back what was resolved even
    if the cap or an error stops the run early."""
    blanks = [r for r in rows if not (r.get("website") or "").strip()]
    if not blanks:
        return 0
    if "website" not in fieldnames:
        fieldnames.append("website")

    backup = f"{csv_path}.bak"
    if not os.path.exists(backup):
        try:
            shutil.copyfile(csv_path, backup)
            log.info("Backed up original prospect list to %s", backup)
        except OSError as exc:
            log.warning("Could not back up %s: %s", csv_path, exc)

    cache = load_places_cache()
    log.info("%d businesses have no website; resolving via Places (cap: %d lookups)",
              len(blanks), max_lookups)
    billed = resolved = 0
    capped = False
    try:
        for row in blanks:
            if billed >= max_lookups:
                capped = True
                break
            site, error, was_billed = lookup_website(row.get("name", ""), row.get("address", ""), cache)
            billed += 1 if was_billed else 0
            if site:
                row["website"] = site
                resolved += 1
            elif error:
                log.info("No website for %r: %s", row.get("name", ""), error)
    finally:
        # Persist before any early exit so a stopped run is never wasted.
        save_places_cache(cache)
        write_prospects(csv_path, rows, fieldnames)

    log.info("Resolved %d website(s) using %d billable lookup(s); written back to %s",
              resolved, billed, csv_path)
    if capped:
        log.warning("Stopped at the --max-lookups cap of %d. %d business(es) still have no "
                     "website. Everything resolved so far has been saved to %s - re-run with a "
                     "higher --max-lookups to continue where this left off.",
                     max_lookups, len([r for r in rows if not (r.get('website') or '').strip()]), csv_path)
    return resolved


def screen_site(url, want_psi, timeout):
    """Triage one site from its homepage alone. Returns a result dict; never
    raises - transport and parse failures come back in the 'error' field."""
    result = {c: "" for c in SCREEN_CSV_COLUMNS}
    result["website"] = url

    start = time.monotonic()
    resp, transport_error = safe_get(url, timeout=timeout, allow_redirects=True, return_error=True)
    elapsed = time.monotonic() - start
    if resp is None:
        result["error"] = transport_error or "unreachable"
        return result

    final_url = resp.url or url
    result["website"] = final_url
    if len(resp.history) > 3:
        log.info("%s redirected %d times, ending at %s", url, len(resp.history), final_url)
    if resp.status_code >= 400:
        result["error"] = f"HTTP {resp.status_code}"
        if resp.status_code in (401, 403):
            result["error"] += " (blocked to non-browser agents)"
        return result

    content_type = (resp.headers.get("content-type") or "").split(";")[0].strip().lower()
    if content_type and "html" not in content_type:
        result["error"] = f"not an HTML page (content-type: {content_type})"
        return result

    try:
        soup = BeautifulSoup(resp.text, "html.parser")
    except Exception as exc:  # noqa: BLE001 - malformed markup must not kill the run
        result["error"] = f"could not parse HTML: {exc}"
        return result

    pd = PageData(url=final_url, status_code=resp.status_code, ok=True,
                   load_time=elapsed, size_bytes=len(resp.content),
                   headers=dict(resp.headers))
    try:
        analyze_page(pd, soup, urlparse(final_url).netloc)
    except Exception as exc:  # noqa: BLE001
        result["error"] = f"could not analyze page: {exc}"
        return result

    platform = detect_platform(pd, soup)
    result["platform"] = platform.platform
    result["page_builder"] = platform.page_builder

    if want_psi:
        cache = load_pagespeed_cache()
        psi = fetch_pagespeed(final_url, "mobile", cache)
        save_pagespeed_cache(cache)
        pd.psi["mobile"] = psi
        if psi.performance_score is not None:
            result["psi_mobile_score"] = psi.performance_score
        result["psi_mobile_lcp"] = psi.lcp_display or ""
        if psi.error and psi.performance_score is None:
            result["error"] = f"pagespeed: {psi.error}"

    crawl_data = {
        "base_url": final_url,
        "pages": {final_url: pd},
        "incoming_links": {},
        "has_robots": True,      # not probed in screen mode - unknown, not missing
        "sitemap_found": True,   # ditto
        "sitemap_url": "",
        "all_internal_links_seen": set(),
    }
    try:
        issues = detect_issues(crawl_data, {}, {}, include_site_level=False)
        apply_platform_advice(issues, platform)
    except Exception as exc:  # noqa: BLE001
        result["error"] = f"detection failed: {exc}"
        return result

    result["findings_count"] = len(issues)
    result["findings"] = "; ".join(i.issue for i in sorted(
        issues, key=lambda i: (SEVERITY_ORDER.get(i.severity, 9), i.category)))
    return result


def cmd_screen(args):
    if args.url:
        rows = [{"name": domain_key(args.url), "website": args.url}]
        fieldnames = None
    else:
        try:
            rows, fieldnames = read_prospects(args.csv)
        except (OSError, ValueError) as exc:
            sys.stderr.write(f"error: could not read {args.csv}: {exc}\n")
            sys.exit(2)
        if not rows:
            sys.stderr.write(f"error: {args.csv} contains no rows.\n")
            sys.exit(2)
        resolve_websites(rows, fieldnames, args.csv, args.max_lookups)

    results = []
    total = len(rows)
    for idx, row in enumerate(rows, 1):
        name = (row.get("name") or "").strip()
        website = (row.get("website") or "").strip()
        log.info("Screening (%d/%d): %s", idx, total, name or website or "(unnamed)")

        result = {c: "" for c in SCREEN_CSV_COLUMNS}
        result["name"] = name
        result["website"] = website
        try:
            if not website:
                result["error"] = "no website"
            else:
                if not urlparse(website).scheme:
                    website = f"https://{website}"
                    result["website"] = website
                parsed = urlparse(website)
                if parsed.scheme not in ("http", "https"):
                    result["error"] = f"unsupported URL scheme: {parsed.scheme or website}"
                elif not parsed.netloc or not HOSTNAME_RE.match(parsed.netloc):
                    # Catch junk before spending a request and a DNS timeout on it.
                    result["error"] = "malformed URL"
                else:
                    screened = screen_site(website, args.psi, args.timeout)
                    screened["name"] = name
                    result = screened
        except Exception as exc:  # noqa: BLE001 - one bad host must not end a 200-site run
            result["error"] = f"unexpected failure: {type(exc).__name__}: {exc}"
            log.warning("Unexpected failure screening %s: %s", website, exc, exc_info=True)
        results.append(result)

    write_screen_results(args.out, results)
    print_screen_summary(results, args.out)


def write_screen_results(path, results):
    try:
        with open(path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=SCREEN_CSV_COLUMNS, extrasaction="ignore")
            writer.writeheader()
            for row in results:
                writer.writerow({c: row.get(c, "") for c in SCREEN_CSV_COLUMNS})
    except OSError as exc:
        log.error("Could not write results to %s: %s", path, exc)
        raise


def print_screen_summary(results, out_path):
    """Ranked by finding count descending - this is the outreach order."""
    def sort_key(r):
        count = r.get("findings_count")
        return -(count if isinstance(count, int) else -1)

    ranked = sorted(results, key=sort_key)
    ok = [r for r in results if not r.get("error")]
    errored = [r for r in results if r.get("error")]

    print(f"\nScreened {len(results)} site(s): {len(ok)} analyzed, {len(errored)} with errors.")
    print(f"Results written to {out_path}\n")
    print("Outreach priority (most findings first):")
    print(f"  {'#':>3}  {'findings':>8}  {'platform':<14} {'builder':<10} name")
    for i, r in enumerate(ranked, 1):
        count = r.get("findings_count")
        count_display = str(count) if isinstance(count, int) else "-"
        label = (r.get("name") or r.get("website") or "(unnamed)")[:44]
        suffix = f"   [{r['error'][:52]}]" if r.get("error") else ""
        print(f"  {i:>3}  {count_display:>8}  {str(r.get('platform') or '-'):<14} "
               f"{str(r.get('page_builder') or '-'):<10} {label}{suffix}")

    platforms = Counter(r.get("platform") or "-" for r in ok)
    if platforms:
        print("\nPlatform mix (analyzed sites):")
        for name, n in platforms.most_common():
            note = ""
            if name in PLATFORM_OWNS_PERFORMANCE:
                note = "  <- platform owns performance; speed findings not yours to fix"
            print(f"  {n:>3}  {name}{note}")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def valid_url(value):
    """argparse type: accept only well-formed http(s) URLs."""
    parsed = urlparse(value)
    if parsed.scheme not in ("http", "https") or not parsed.netloc:
        raise argparse.ArgumentTypeError(f"'{value}' is not a valid http(s) URL")
    return value


def build_parser():
    parser = argparse.ArgumentParser(
        prog="audit.py",
        description="Site audit tool: deep single-site reports, or fast multi-site triage.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="examples:\n"
                "  python audit.py report --url https://example.com\n"
                "  python audit.py screen --csv prospects.csv --out results.csv\n"
                "  python audit.py screen --url https://example.com --psi\n")
    subs = parser.add_subparsers(dest="command", metavar="{report,screen}")

    def add_shared(sp):
        sp.add_argument("--rate-limit", type=float, default=RATE_LIMIT_SECONDS, metavar="SECONDS",
                         help=f"seconds between requests (default: {RATE_LIMIT_SECONDS})")

    rp = subs.add_parser("report", help="full crawl + PDF report for one site")
    rp.add_argument("--url", required=True, type=valid_url, help="site to audit (required)")
    rp.add_argument("--out", metavar="PATH",
                     help="report path (default: site_audit_report_<domain>_<date>.pdf)")
    rp.add_argument("--max-pages", type=int, default=MAX_PAGES, metavar="N",
                     help=f"maximum pages to crawl (default: {MAX_PAGES})")
    rp.add_argument("--max-link-checks", type=int, default=MAX_LINK_CHECKS, metavar="N",
                     help=f"cap on broken-link checks (default: {MAX_LINK_CHECKS})")
    add_shared(rp)

    sp = subs.add_parser("screen", help="fast homepage-only triage across many sites")
    src = sp.add_mutually_exclusive_group(required=True)
    src.add_argument("--csv", metavar="FILE",
                      help="input CSV with columns: name, address, phone, category, tier, website")
    src.add_argument("--url", type=valid_url, help="screen a single site")
    sp.add_argument("--out", default="results.csv", metavar="PATH",
                     help="output CSV path (default: results.csv)")
    sp.add_argument("--psi", action="store_true",
                     help="also fetch PageSpeed mobile scores (much slower)")
    sp.add_argument("--timeout", type=float, default=SCREEN_TIMEOUT, metavar="SECONDS",
                     help=f"per-request timeout (default: {SCREEN_TIMEOUT})")
    sp.add_argument("--max-lookups", type=int, default=MAX_PLACES_LOOKUPS, metavar="N",
                     help=f"cap on billable Places API lookups (default: {MAX_PLACES_LOOKUPS})")
    add_shared(sp)
    return parser


def apply_global_settings(args):
    """The tunables are module-level constants read at call time throughout the
    pipeline, so flags are applied here once rather than threaded through every
    function signature."""
    global MAX_PAGES, RATE_LIMIT_SECONDS, MAX_LINK_CHECKS
    if getattr(args, "max_pages", None) is not None:
        MAX_PAGES = args.max_pages
    if getattr(args, "max_link_checks", None) is not None:
        MAX_LINK_CHECKS = args.max_link_checks
    if getattr(args, "rate_limit", None) is not None:
        RATE_LIMIT_SECONDS = args.rate_limit
        limiter.delay = args.rate_limit


def main():
    parser = build_parser()
    args = parser.parse_args()
    if not args.command:
        parser.print_usage(sys.stderr)
        sys.stderr.write("\nerror: a command is required (report or screen).\n")
        sys.exit(2)
    apply_global_settings(args)
    if args.command == "screen":
        return cmd_screen(args)
    return cmd_report(args)


def cmd_report(args):
    base_url = args.url
    output_pdf = output_pdf_path(base_url, args.out)

    crawl_data, issues = load_state(base_url)
    if crawl_data is None:
        log.info("No usable checkpoint at %s - running the full pipeline once to build one "
                  "(PageSpeed calls reuse the 7-day cache, so no new API calls happen for pages/strategies "
                  "already fetched).", state_file_path(base_url))
        log.info("Starting audit of %s (max %d pages, %.1fs between requests)",
                  base_url, MAX_PAGES, RATE_LIMIT_SECONDS)

        crawl_data = crawl(base_url)
        log.info("Crawl complete: %d pages fetched", len(crawl_data["pages"]))

        # Sample a few images per page for size checks (shares the same rate limiter)
        image_findings = check_image_sizes(crawl_data)
        log.info("Checked sizes for %d images across %d pages",
                  sum(len(v) for v in image_findings.values()), len(image_findings))

        link_status = check_links(crawl_data)

        run_pagespeed_checks(crawl_data)

        issues = detect_issues(crawl_data, link_status, image_findings)
        issues.extend(check_security(crawl_data))
        log.info("Detected %d distinct issue types (%d total instances)",
                  len(issues), sum(len(i.pages) if i.pages else 1 for i in issues))

        save_state(crawl_data, issues)
    else:
        log.info("Loaded cached crawl/issue data for %s from %s - skipping crawl, link/image checks, "
                  "and PageSpeed calls entirely.", crawl_data["base_url"], state_file_path(base_url))

    # Rewrite platform-specific remediation advice before the hand-written
    # manual findings are added - those are authored per client and must not be
    # genericized. A no-op for WordPress and for checkpoints predating platform
    # detection, which record no platform and so read as unknown.
    apply_platform_advice(issues, crawl_data.get("platform") or PlatformInfo())

    add_manual_findings(issues, crawl_data["base_url"])

    build_pdf(crawl_data["base_url"], issues, crawl_data, output_pdf)
    print(f"\nDone. Report saved to {output_pdf}")


if __name__ == "__main__":
    main()
