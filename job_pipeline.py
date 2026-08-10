#!/usr/bin/env python3
"""
Ireland Job Hunt Pipeline (v2)
================================
Reads Job_Automation.csv (company_name, career_url) and produces jobs.json —
a normalized, filterable dataset for the dashboard (dashboard.html).

WHAT IT DOES AUTOMATICALLY:
  - Detects which companies run on Workday (a platform with a public JSON
    search API) and pulls their LIVE current openings for Ireland, with
    title / location / date posted / employment type / direct apply link.
  - Fetches each job's full description text and scans it for visa
    sponsorship language, tagging each posting as:
        "sponsors"        - description explicitly says sponsorship is offered
        "no_sponsorship"  - description explicitly rules it out
        "not_mentioned"   - sponsorship isn't discussed in the text
  - Keeps a running history file (sponsorship_history.json) across every
    run, so each company builds up a real sample size over time and the
    dashboard can show "mentions sponsorship in 3 of 40 postings scanned"
    instead of a one-off guess.

IMPORTANT HONESTY NOTE ON VISA SPONSORSHIP:
  This is a TEXT SIGNAL from job descriptions, not a legal or HR record.
  Many postings say nothing either way (that's "not_mentioned", the most
  common case) and companies change policy per-role. Treat the rarity
  score as "how often this company has said something about it in the
  postings we've scanned so far" — a helpful heuristic, not a guarantee.

WHAT IT CANNOT FULLY AUTOMATE (and why):
  - The other ~90% of companies on your list run bespoke career sites
    with no shared API and often JS-rendered content or bot protection.
    They're included in the dashboard's directory tab as direct links.
    See README.md for how to extend coverage.

USAGE:
    pip install requests
    python job_pipeline.py --input Job_Automation.csv --output jobs.json

SCHEDULING: see README.md (cron / Task Scheduler / GitHub Actions).
"""

import argparse
import csv
import json
import os
import re
import sys
import time
import uuid
import signal
import html
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

try:
    import requests
except ImportError:
    print("This script needs the 'requests' library: pip install requests")
    sys.exit(1)

try:
    from curl_cffi import requests as cffi_requests
    HAS_CURL_CFFI = True
except ImportError:
    HAS_CURL_CFFI = False
    print("Note: 'curl_cffi' not installed — some strictly-protected Workday tenants "
          "may fail with 400/422 errors that curl_cffi's browser-TLS impersonation "
          "can get past. Install with: pip install curl_cffi")

try:
    from playwright.sync_api import sync_playwright
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False
    print("Note: 'playwright' not installed — Google/Meta browser connectors disabled. "
          "Install with: pip install playwright && python -m playwright install chromium")

IRELAND_LOCATION_HINTS = [
    "ireland", "dublin", "cork", "galway", "limerick", "waterford",
    "kilkenny", "kildare", "leinster", "munster", "belfast", "shannon",
    "sligo", "athlone", "drogheda", "wicklow", "meath",
]

WORKDAY_URL_RE = re.compile(
    r"https?://([\w-]+)\.(wd\d+)\.myworkdayjobs\.com/(?:[\w-]+/)?([\w-]+)"
)

GREENHOUSE_JOBS_URL = "https://boards-api.greenhouse.io/v1/boards/{slug}/jobs?content=true"
LEVER_JOBS_URL = "https://api.lever.co/v0/postings/{slug}?mode=json"
SMARTRECRUITERS_JOBS_URL = "https://api.smartrecruiters.com/v1/companies/{slug}/postings"
SMARTRECRUITERS_DETAIL_URL = "https://api.smartrecruiters.com/v1/companies/{slug}/postings/{posting_id}"
ASHBY_JOBS_URL = "https://api.ashbyhq.com/posting-api/job-board/{slug}"
RECRUITEE_JOBS_URL = "https://{slug}.recruitee.com/api/offers/"
PERSONIO_XML_URL = "https://{slug}.jobs.personio.de/xml"
PINPOINT_JOBS_URL = "https://{slug}.pinpointhq.com/postings.json"
# Eightfold has no officially documented public API — this is a widely-used
# reverse-engineered endpoint. Less stable than the others; could change
# without notice since it's not a supported public contract.
EIGHTFOLD_SMARTAPPLY_URL = "https://{slug}.eightfold.ai/api/apply/v2/jobs?domain={domain}&hl=en&start=0"

CORP_SUFFIX_RE = re.compile(
    r"\b(limited|ltd|plc|unlimited company|uc|inc|incorporated|group|holdings|"
    r"ireland|international|corporation|corp|company|co|technologies|technology)\b",
    re.IGNORECASE,
)

HEADERS = {
    "Content-Type": "application/json",
    "Accept": "application/json",
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36"),
    # Modern Chrome sends these "client hint" and fetch-metadata headers on
    # every real request automatically — a bare requests-style header dict
    # never includes them. Some stricter bot-detection configs specifically
    # check for their presence (not just User-Agent), which curl_cffi's TLS
    # impersonation alone doesn't add unless set explicitly. Genuinely
    # untested angle, not a repeat of prior header attempts.
    "sec-ch-ua": '"Chromium";v="125", "Not.A/Brand";v="24", "Google Chrome";v="125"',
    "sec-ch-ua-mobile": "?0",
    "sec-ch-ua-platform": '"Windows"',
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
}


def workday_headers(tenant, wd_shard, site):
    """Many Workday tenants sit behind bot-protection that blocks requests
    without a Referer/Origin matching the tenant's own domain — a real
    browser visiting the career page always sends these; a bare API script
    without them can get flat-out rejected with a 400, even on a perfectly
    valid endpoint. This makes every request look like it came from the
    tenant's own career page, which is exactly what it's mimicking.

    IMPORTANT: real Workday career pages redirect to a locale-prefixed URL
    (e.g. '/en-US/AccentureCareers') — some tenants validate the Referer
    against that canonical, post-redirect form rather than the bare path,
    so this uses the locale-prefixed version to match what a real browser
    would actually end up sending."""
    site_base = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/en-US/{site}"
    return {
        **HEADERS,
        "Referer": site_base,
        "Origin": f"https://{tenant}.{wd_shard}.myworkdayjobs.com",
        "X-Requested-With": "XMLHttpRequest",
    }


def make_workday_session():
    """Some Workday tenants run bot-protection that fingerprints the TLS
    handshake itself (JA3 fingerprinting) — this can reject a request as
    non-browser-like regardless of what headers/cookies/payload it carries,
    since Python's standard requests/urllib3 has a different, recognizably
    non-browser TLS signature than real Chrome. curl_cffi impersonates an
    actual Chrome TLS handshake, which gets past this class of protection
    where no amount of header tweaking can. Falls back to a plain requests
    session if curl_cffi isn't installed (with reduced success on the most
    strictly-protected tenants)."""
    if HAS_CURL_CFFI:
        return cffi_requests.Session(impersonate="chrome124")
    return requests.Session()


# --- visa sponsorship text signal -------------------------------------

SPONSOR_POSITIVE_PATTERNS = [
    r"visa sponsorship (is |will be )?available",
    r"will sponsor",
    r"we (can|do|are able to) sponsor",
    r"eligible for (visa |work permit )?sponsorship",
    r"sponsorship (is )?available for (this|eligible) (role|candidates)",
    r"provide(s)? immigration sponsorship",
    r"support (a |an )?(critical skills )?employment permit",
    r"open to sponsoring",
    r"sponsor(ship)? (work permit|visa)s? for (this|the) role",
]
SPONSOR_NEGATIVE_PATTERNS = [
    r"unable to (offer|provide) (visa )?sponsorship",
    r"(does not|do not|won't|will not|no) (currently )?(offer|provide) (visa )?sponsorship",
    r"cannot sponsor",
    r"without (the need for )?(visa )?sponsorship",
    r"must (be|already be) (legally )?eligible to work .{0,40}without sponsorship",
    r"no visa sponsorship (is )?available",
    r"not able to sponsor",
    r"sponsorship (is )?not (available|offered|provided)",
]
SPONSOR_POS_RE = re.compile("|".join(SPONSOR_POSITIVE_PATTERNS), re.IGNORECASE)
SPONSOR_NEG_RE = re.compile("|".join(SPONSOR_NEGATIVE_PATTERNS), re.IGNORECASE)
HTML_TAG_RE = re.compile(r"<[^>]+>")


def classify_sponsorship(description_text: str):
    """Returns (label, snippet). label in {'sponsors','no_sponsorship','not_mentioned'}."""
    if not description_text:
        return "not_mentioned", None
    plain = HTML_TAG_RE.sub(" ", description_text)
    plain = re.sub(r"\s+", " ", plain).strip()

    neg = SPONSOR_NEG_RE.search(plain)
    if neg:
        start = max(0, neg.start() - 40)
        return "no_sponsorship", plain[start:neg.end() + 40].strip()

    pos = SPONSOR_POS_RE.search(plain)
    if pos:
        start = max(0, pos.start() - 40)
        return "sponsors", plain[start:pos.end() + 40].strip()

    return "not_mentioned", None


def classify_url(url: str) -> str:
    if WORKDAY_URL_RE.search(url):
        return "workday"
    if "oraclecloud.com" in url or ".fa." in url:
        return "oracle_cloud"
    if "greenhouse.io" in url:
        return "greenhouse"
    if "lever.co" in url:
        return "lever"
    return "custom"


class _HardTimeout(Exception):
    pass


def _timeout_handler(signum, frame):
    raise _HardTimeout()


def run_with_hard_timeout(fn, seconds, label):
    """Forcibly interrupts fn() after `seconds`, no matter what it's doing
    internally — a real, OS-level alarm, not a cooperative check the
    function has to remember to make itself. This is the guaranteed fix
    after two separate incidents today where a company-specific scraper's
    OWN internal time-budget logic either wasn't actually wired up, or an
    entirely different function had no time budget at all, and either way
    the whole pipeline hung for hours. Every single company scraper call
    in main() should go through this from now on — no exceptions, no
    matter how well-behaved a given function looks on inspection, since
    that's exactly what we assumed twice already and were wrong both
    times."""
    old_handler = signal.signal(signal.SIGALRM, _timeout_handler)
    signal.alarm(seconds)
    try:
        return fn()
    except _HardTimeout:
        print(f"      [{label}] HARD TIMEOUT — forcibly stopped after {seconds}s "
              f"(this company's own internal bounds failed or don't exist; "
              f"the pipeline continues normally with whatever it already found)")
        return []
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)


BROWSER_SCRAPE_CACHE_PATH = "browser_scrape_cache.json"
BROWSER_SCRAPE_MAX_AGE_HOURS = 3  # only actually re-run a real browser scrape this often


def _load_browser_scrape_cache():
    if os.path.exists(BROWSER_SCRAPE_CACHE_PATH):
        try:
            with open(BROWSER_SCRAPE_CACHE_PATH, encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}


def cached_browser_scrape(cache, company_key, scraper_fn, timeout_seconds, label):
    """The real fix for a run that took hours even with every individual
    company correctly time-bounded: running ~20 separate real browser
    automations sequentially, every single 15-minute cycle, is simply a
    lot of real work even when nothing is broken. Same principle already
    used elsewhere in this pipeline (ATS platform matching, JSON-LD
    checks) — don't redo expensive, slow-changing work on every run.
    Reuses a cached result if it's recent enough; only actually launches
    a browser when the cache is missing or stale."""
    entry = cache.get(company_key)
    if entry:
        age_hours = (time.time() - entry.get("checked_at", 0)) / 3600
        if age_hours < BROWSER_SCRAPE_MAX_AGE_HOURS:
            jobs = entry.get("jobs", [])
            print(f"      [{label}] using cached result from {age_hours:.1f}h ago "
                  f"({len(jobs)} jobs) — next real check in {BROWSER_SCRAPE_MAX_AGE_HOURS - age_hours:.1f}h")
            return jobs

    jobs = run_with_hard_timeout(scraper_fn, timeout_seconds, label)
    cache[company_key] = {"jobs": jobs, "checked_at": time.time()}
    return jobs


def parse_posted_text(posted_text: str):
    if not posted_text:
        return None
    t = posted_text.lower()
    if "today" in t:
        return 0
    if "yesterday" in t:
        return 1
    m = re.search(r"(\d+)\+?\s*day", t)
    if m:
        return int(m.group(1))
    return None


UNKNOWN_POSTED_DAYS = 9999.0  # critical: JS treats null <= 1 as true, so never emit null for unknown ages


def extract_posted_from_text(text: str):
    """Find a posted-age/date phrase in rendered job-card text — used by
    the browser-scraped sources (Google, Meta, EY, TikTok, etc.) which
    otherwise had no date information at all."""
    if not text:
        return "Unknown", None
    compact = re.sub(r"\s+", " ", str(text)).strip()
    patterns = [
        r"(?:posted\s+)?(?:just now|just posted|today|yesterday)",
        r"(?:posted\s+)?\d+(?:\.\d+)?\s*(?:minutes?|mins?|hours?|hrs?|days?|weeks?|months?)\s+ago",
        r"(?:posted|date posted|published)\s*[:\-]?\s*(?:\d{4}-\d{2}-\d{2}|[A-Za-z]{3,9}\s+\d{1,2},\s+\d{4}|\d{1,2}\s+[A-Za-z]{3,9}\s+\d{4})",
    ]
    for pat in patterns:
        m = re.search(pat, compact, re.I)
        if m:
            txt = m.group(0)
            days = parse_posted_text(txt)
            if days is not None:
                return txt, days
    return "Unknown", None


def normalize_posted_age(job):
    """Normalize posting age without changing the dashboard's time-window
    model. The dashboard filters are cumulative windows: 24 hours
    (posted_days_ago <= 1), 7 days (<=7), 28 days (<=28), Any time (no
    restriction). Unknown dates use a large numeric sentinel so JavaScript
    cannot coerce null to 0 and accidentally classify them as recent —
    they still remain visible under 'Any time', since that option applies
    no age condition at all."""
    days = job.get("posted_days_ago")
    if days is None:
        days = parse_posted_text(job.get("posted_text", ""))
    try:
        days = float(days) if days is not None else UNKNOWN_POSTED_DAYS
    except (TypeError, ValueError):
        days = UNKNOWN_POSTED_DAYS
    if days < 0:
        days = 0.0
    job["posted_days_ago"] = days
    job["posted_age_known"] = days < UNKNOWN_POSTED_DAYS
    job.pop("posted_age_bucket", None)
    return job


def is_ireland_location(location_text: str) -> bool:
    if not location_text:
        return False
    lt = location_text.lower()
    return any(hint in lt for hint in IRELAND_LOCATION_HINTS)


def normalize_employment_type(raw, title=""):
    """Every platform describes employment type in its own wording —
    Ashby uses 'FullTime' (no space), Lever uses 'Full-time', SmartRecruiters
    nests it under a different field entirely, Personio says 'Permanent'.
    The dashboard's filter dropdown only matches one of 6 exact strings, so
    passing any of these through unchanged meant the filter matched almost
    nothing — this collapses whatever a platform says into one of those 6
    canonical values.

    Every check below uses word-boundary regex on the ORIGINAL (space-
    preserved) string, not a naive substring test on a space-stripped
    blob — a naive check is exactly what caused a real bug: 'International'
    was wrongly tagged 'Internship' because it contains 'intern' as a bare
    substring. The same class of mistake exists for several other words
    (contemporary/temporary, irregular/regular, impermanent/permanent),
    so every category gets the same word-boundary treatment, not just the
    one that happened to get caught."""
    original = str(raw).lower() if raw else ""
    title_lower = str(title).lower() if title else ""

    def word(pattern, text):
        return re.search(pattern, text) is not None

    # The bare word 'intern' in the METADATA field is genuinely ambiguous
    # (a real Version 1 posting used it to mean something like 'Internal',
    # not internship) — only the full word 'internship' counts there.
    # But the same bare word in the actual public-facing TITLE is a much
    # more trustworthy signal: no employer titles a real senior role
    # "Intern" by mistake. 'Work placement' is another real, common phrase
    # for the same thing (e.g. Deloitte's Aspire Programme postings).
    if word(r"\binternship\b", original):
        return "Internship"
    if word(r"\bintern(?:ship)?\b", title_lower) or word(r"\bwork\s?placement\b", title_lower):
        return "Internship"
    if word(r"\bpart[\s-]?time\b", original):
        return "Part-time"
    if word(r"\bpart[\s-]?time\b", title_lower):
        return "Part-time"
    if word(r"\btemp(?:orary)?\b", original):  # 'temp' alone should count too, not just 'temporary'
        return "Temporary"
    if word(r"\btemp(?:orary)?\b", title_lower):
        return "Temporary"
    if word(r"\b(?:contract(?:or)?|freelance)\b", original):
        # NOTE: 'consultant' deliberately excluded — it's commonly a
        # permanent full-time JOB TITLE at many companies (Accenture,
        # Deloitte, etc.), not a genuine employment-type signal. Treating
        # it as Contract would misclassify real full-time consultants.
        return "Contract"
    # Title-based Contract check is deliberately NARROWER than Part-time/
    # Temporary above — "Contract Manager", "Contract Administrator", and
    # "Contract Specialist" are real, common PERMANENT job titles about
    # managing contracts, not contract-type roles themselves. A bare
    # "contract" match in the title would recreate the same class of bug
    # already fixed elsewhere. Only specific, unambiguous phrasing counts.
    if word(r"\b(?:fixed[\s-]?term|contract\s+(?:role|position|basis)|\d+[\s-]?(?:month|week|year)s?\s+contract|contractor)\b", title_lower):
        return "Contract"
    if word(r"\b(?:full[\s-]?time|permanent|regular)\b", original):
        return "Full-time"
    return "Unspecified"


def fetch_job_description(tenant, wd_shard, site, external_path, session):
    detail_url = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/wday/cxs/{tenant}/{site}{external_path}"
    try:
        resp = session.get(detail_url, headers=workday_headers(tenant, wd_shard, site), timeout=15)
        resp.raise_for_status()
        data = resp.json()
        return (data.get("jobPostingInfo") or {}).get("jobDescription", "")
    except Exception:
        return ""


def find_ireland_facet_values(facets):
    """Workday exposes a 'locations' facet (sometimes hierarchical: country ->
    city). Recursively search it for anything Ireland-related and return the
    facet parameter name + matching value IDs, so we can ask Workday's API to
    filter server-side instead of guessing from a few hundred results."""
    def walk(values):
        matched = []
        for v in values or []:
            descriptor = str(v.get("descriptor", ""))
            if any(hint in descriptor.lower() for hint in IRELAND_LOCATION_HINTS):
                matched.append(v.get("id"))
            # Don't descend into a matched country node's children — including
            # the parent id already covers them in Workday's filter semantics.
            elif v.get("values"):
                matched.extend(walk(v["values"]))
        return matched

    for facet in facets or []:
        param = facet.get("facetParameter", "")
        if "location" not in param.lower():
            continue
        ids = walk(facet.get("values"))
        if ids:
            return param, ids
    return None, []


def post_workday_variants(session, api_base, headers, applied_facets, limit, offset, search_text=""):
    """Different Workday tenants (depending on their CXS API version) can
    reject a payload shape that others accept fine — e.g. some reject an
    empty 'searchText' string, others want 'appliedFacets' omitted when
    empty. Try a few known-real variants in order and use whichever the
    tenant actually accepts, instead of assuming one shape works everywhere."""
    variants = [
        {"appliedFacets": applied_facets, "limit": limit, "offset": offset, "searchText": search_text},
        {"appliedFacets": applied_facets, "limit": limit, "offset": offset},
        {"searchText": search_text, "limit": limit, "offset": offset, "appliedFacets": applied_facets},
        {"appliedFacets": applied_facets, "limit": limit, "offset": offset, "searchText": search_text, "clientRequestID": ""},
        # Genuinely new attempt: a real UUID, not an empty string — real
        # Workday frontend JS always generates one for this field.
        {"appliedFacets": applied_facets, "limit": limit, "offset": offset, "searchText": search_text,
         "clientRequestID": str(uuid.uuid4())},
        {"appliedFacets": {}, "limit": limit, "offset": offset, "searchText": "Ireland"},
    ]
    # One more low-cost shape: omit empty keys entirely instead of sending
    # them as {} / "". Low confidence this is the actual fix (Strategy 1
    # already sends a genuinely non-empty facet and still gets rejected for
    # the same stuck tenants, which argues against "empty fields" being the
    # real cause) — but cheap enough to include as one more attempt.
    clean_variant = {"limit": limit, "offset": offset}
    if applied_facets:
        clean_variant["appliedFacets"] = applied_facets
    if search_text:
        clean_variant["searchText"] = search_text
    variants.append(clean_variant)
    last_error = None
    for i, payload in enumerate(variants):
        try:
            resp = session.post(api_base, headers=headers, json=payload, timeout=15)
            if resp.status_code == 200:
                return resp, None
            if resp.status_code == 429:
                # Rate limited — trying more variants right now will almost
                # certainly also get 429'd and just makes it worse. Stop
                # immediately, back off, and surface this clearly rather
                # than silently hammering through the rest of the list.
                last_error = f"HTTP 429 rate limited"
                time.sleep(3)
                return None, last_error
            last_error = f"HTTP {resp.status_code}: {resp.text[:150]}"
        except Exception as e:
            last_error = str(e)
        if i < len(variants) - 1:
            time.sleep(0.4)  # brief pause between attempts, not a rapid-fire burst
    return None, last_error


def fetch_workday_jobs(company_name, url, session, fetch_descriptions=True,
                        page_size=20, detail_delay=0.15):
    m = WORKDAY_URL_RE.search(url)
    if not m:
        return [], f"URL did not match Workday pattern: {url}"

    tenant, wd_shard, site = m.group(1), m.group(2), m.group(3)
    api_base = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/wday/cxs/{tenant}/{site}/jobs"
    site_base = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/{site}"
    site_base_locale = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/en-US/{site}"

    # IMPORTANT: visit the actual career page first, like a real browser
    # would, before calling the API directly. Workday's bot-protection
    # commonly rejects "cold" API calls with no prior page visit (400/422)
    # regardless of headers — this establishes the session cookies it's
    # checking for. Use the locale-prefixed URL, matching what a real
    # browser actually lands on after Workday's own redirect, since some
    # tenants validate the Referer against that canonical form specifically.
    # Best-effort: if this fails, still try the API anyway.
    try:
        session.get(site_base_locale, headers=workday_headers(tenant, wd_shard, site), timeout=15)
        time.sleep(0.5)
    except Exception:
        pass

    # First, small probe request just to read the facet list (no location
    # filter yet) so we can find Workday's own Ireland location facet IDs.
    applied_facets = {}
    # Server-side facet filtering is used purely to reduce how many pages
    # need scanning — it is never trusted blindly. A client-side location
    # check always runs on every result regardless of which strategy
    # found it: some tenants' Workday setup doesn't recognize the shared
    # Ireland facet ID and silently returns their ENTIRE global job list
    # instead of erroring (confirmed: PwC and MSD returned 600/591 "Ireland"
    # postings that were really just their whole global listing).
    max_pages = 10  # fallback cap if we can't find a location facet at all
    probe_error = None

    # Strategy 1 (primary): Workday ships the SAME internal ID for "Ireland"
    # as a country to every customer who uses its standard country
    # reference data — confirmed identical across completely unrelated
    # tenants (Sky, Motorola Solutions, BDR Thermea, even Workday's own
    # careers site all use this exact value). Trying it directly is far
    # more reliable than *discovering* the right facet by sampling search
    # results, which can miss Ireland entirely for large multinationals
    # where Ireland postings don't happen to appear in the sample window —
    # this was the actual cause of companies like Accenture showing 0
    # postings despite having dozens of real open Ireland roles.
    strategy1_note = None
    rate_limited = False
    try:
        known_facets = {"locationCountry": ["04a05835925f45b3a59406a2a6b72c8a"]}
        probe, probe_err = post_workday_variants(
            session, api_base, workday_headers(tenant, wd_shard, site), known_facets, 20, 0)
        if probe is None:
            strategy1_note = f"request failed ({probe_err})"
            if probe_err and "429" in str(probe_err):
                rate_limited = True
        else:
            probe_data = probe.json()
            total = probe_data.get("total", 0)
            # Sanity ceiling: no real company has hundreds of simultaneous
            # open Ireland roles. A "filtered" total this high (we've seen
            # PwC report 4586, MSD 882) is proof the facet ID wasn't
            # actually recognized by that tenant and the filter silently
            # no-op'd, returning their entire global job list instead —
            # treat that as a non-match rather than trusting it, and let
            # it fall through to the next strategy.
            if 0 < total <= 150:
                applied_facets = known_facets
                max_pages = 30
                strategy1_note = f"matched, total={total}"
            elif total > 150:
                strategy1_note = f"rejected — total={total} is implausibly high, filter likely didn't apply"
            else:
                strategy1_note = "request succeeded but total=0 under 'locationCountry' key"
    except Exception as e:
        strategy1_note = f"exception ({e})"

    # Strategy 1b: same universal ID, but under a different facet parameter
    # name — Workday's URL query param name and the actual API body key
    # aren't always identical, so 'locationCountry' might not be what this
    # specific tenant's API expects even though the ID value is universal.
    # NOT trusted the same way as Strategy 1: the same ID string reused
    # under a different facet dimension (e.g. 'locations' instead of
    # 'locationCountry') has no verified meaning — it could silently match
    # something other than Ireland. Keep the client-side text safety net
    # active for this path (this is what let non-Ireland jobs slip through
    # unfiltered and inflate some companies' counts to hundreds).
    if not applied_facets and not rate_limited:
        for alt_key in ("locations", "country", "Location_Country"):
            try:
                alt_facets = {alt_key: ["04a05835925f45b3a59406a2a6b72c8a"]}
                probe, alt_err = post_workday_variants(
                    session, api_base, workday_headers(tenant, wd_shard, site), alt_facets, 20, 0)
                if alt_err and "429" in str(alt_err):
                    rate_limited = True
                    break
                if probe is not None and 0 < probe.json().get("total", 0) <= 150:
                    applied_facets = alt_facets
                    max_pages = 30
                    strategy1_note += f" | but '{alt_key}' key worked (untrusted, total={probe.json().get('total')})"
                    break
            except Exception:
                continue
            time.sleep(0.4)

    # Strategy 1c (removed): tried plain ISO country codes ('IRL'/'IE')
    # under a few facet key name guesses. Never once succeeded in any real
    # run — pure wasted time, cut for the sake of runtime.

    # Strategy 2 (fallback): the universal ID didn't return anything for
    # this tenant (rare — could be a customized/non-standard instance) —
    # fall back to dynamically discovering whatever facet this specific
    # tenant does expose for Ireland. Search WITH "Ireland" as the search
    # text while discovering facets (not an empty/unrelated search) — the
    # facet counts Workday returns are computed from the CURRENT result
    # set, so an empty search on a huge global company can completely miss
    # Ireland as a facet option, even though it exists, simply because
    # Ireland isn't common enough to surface in an unrelated sample. This
    # path is less certain either way, so the client-side text safety net
    # stays active for it.
    if not applied_facets and not rate_limited:
        try:
            probe = None
            for search_text in ("Ireland", ""):
                try:
                    probe = session.post(
                        api_base, headers=workday_headers(tenant, wd_shard, site),
                        json={"appliedFacets": {}, "limit": 20, "offset": 0, "searchText": search_text},
                        timeout=15)
                    if probe.status_code == 200:
                        break
                    if probe.status_code == 429:
                        rate_limited = True
                        probe = None
                        break
                    probe = None
                except Exception:
                    probe = None
                time.sleep(0.4)
            if probe is None:
                raise RuntimeError("both Ireland-search and empty-search facet probes failed")
            probe_data = probe.json()
            facet_param, facet_ids = find_ireland_facet_values(probe_data.get("facets"))
            if facet_param and facet_ids:
                applied_facets = {facet_param: facet_ids}
                max_pages = 30  # server-side filtered results should be a small, complete set
            else:
                # No usable location facet for this tenant — fall back to a much
                # wider unfiltered scan so large global job boards (e.g.
                # multinationals with thousands of postings) aren't missed just
                # because Ireland roles weren't in the first couple hundred.
                max_pages = 20
        except Exception as e:
            # Don't give up on the whole company over one failed probe request —
            # try the plain unfiltered search below instead. If the tenant is
            # genuinely unreachable, the main loop's own request will fail too
            # and surface a proper error there.
            probe_error = f"{company_name}: facet probe failed, falling back to unfiltered scan ({e})"
            max_pages = 20

    results = []
    seen_urls = set()
    raw_sample_job = None
    error = probe_error

    def run_pagination(facets, search_text, pages):
        nonlocal raw_sample_job, error
        found_any = False
        offset = 0
        for _ in range(pages):
            try:
                resp, req_err = post_workday_variants(
                    session, api_base, workday_headers(tenant, wd_shard, site), facets, page_size, offset,
                    search_text=search_text)
                if resp is None:
                    raise RuntimeError(req_err)
                data = resp.json()
            except Exception as e:
                error = f"{company_name}: request failed ({e})"
                break

            postings = data.get("jobPostings", [])
            if not postings:
                break
            if raw_sample_job is None:
                raw_sample_job = postings[0]

            new_this_page = 0
            for job in postings:
                # Location text can appear under different field names, or
                # buried among bulletFields at an index other than 0 (e.g. a
                # requisition ID at [0] and the actual location at [1]) —
                # check everything plausible rather than assuming one fixed
                # spot, since guessing wrong was causing genuine Ireland jobs
                # to be wrongly discarded.
                candidates = [job.get("locationsText", ""), job.get("location", ""),
                              job.get("primaryLocation", "")]
                candidates.extend(job.get("bulletFields", []) or [])
                location_text = next((c for c in candidates if c and is_ireland_location(c)), "")
                if not location_text:
                    location_text = candidates[0] if candidates and candidates[0] else ""

                # ALWAYS verify client-side, regardless of which strategy found
                # this job — trusting the server-side filter unconditionally
                # was the actual cause of wildly inflated counts for a few
                # companies (PwC showing 600, MSD showing 591), AND of wrong-
                # country jobs slipping through under a small, plausible-
                # looking total (Diageo's "2 Ireland jobs" was actually a job
                # in Gimli, Canada) — the client-side check is the only thing
                # that catches either failure mode.
                if not is_ireland_location(location_text):
                    continue
                posted_text = job.get("postedOn", "")
                external_path = job.get("externalPath", "")
                job_url = site_base.rstrip("/") + external_path

                # Dedup safety net: if Workday returns the same jobs again on
                # a later "page" (offset not actually advancing server-side,
                # or any other pagination quirk), never add the same job
                # twice — this is what was causing wildly inflated counts.
                if job_url in seen_urls:
                    continue
                seen_urls.add(job_url)
                new_this_page += 1
                found_any = True

                sponsorship, snippet = "not_mentioned", None
                if fetch_descriptions and external_path:
                    desc = fetch_job_description(tenant, wd_shard, site, external_path, session)
                    sponsorship, snippet = classify_sponsorship(desc)
                    time.sleep(detail_delay)

                results.append({
                    "company": company_name,
                    "title": job.get("title", "").strip(),
                    "location": location_text,
                    "posted_text": posted_text,
                    "posted_days_ago": parse_posted_text(posted_text),
                    "employment_type": normalize_employment_type(
                        " ".join(str(b) for b in (job.get("bulletFields") or [])),
                        job.get("title", "")),
                    "url": job_url,
                    "source": "workday_api",
                    "visa_sponsorship": sponsorship,
                    "visa_snippet": snippet,
                })

            # Circuit breaker: an entire page with zero genuinely new jobs
            # means pagination has stalled (server returning the same set
            # repeatedly) — stop immediately rather than trusting 'total'
            # and looping up to max_pages re-adding the same postings.
            if new_this_page == 0:
                break

            total = data.get("total", 0)
            offset += page_size
            if offset >= total:
                break
            time.sleep(0.3)
        return found_any

    wide_scan_search_text = "" if applied_facets else "Ireland"
    found = run_pagination(applied_facets, wide_scan_search_text, max_pages)

    # Fallback: the 'smart' filter found SOMETHING (a plausible total), but
    # every result it returned turned out to be a different country once
    # actually checked — this tenant's facet ID doesn't mean what we
    # thought. Rather than accept 0 and give up, retry with a real text
    # search for "Ireland" across the tenant's full job list, same as the
    # last-resort path for tenants where no facet was found at all.
    if not found and applied_facets and not rate_limited:
        strategy1_note = (strategy1_note or "") + " | facet matched but all results were wrong-country; retrying wide Ireland-text search"
        time.sleep(1)
        run_pagination({}, "Ireland", 15)

    if not results and not error:
        print(f"      [diagnostic] {company_name}: 0 postings, strategy1={strategy1_note}")
        if raw_sample_job is not None:
            raw_fields = {
                "locationsText": raw_sample_job.get("locationsText"),
                "location": raw_sample_job.get("location"),
                "primaryLocation": raw_sample_job.get("primaryLocation"),
                "bulletFields": raw_sample_job.get("bulletFields"),
                "all_keys": list(raw_sample_job.keys()),
            }
            print(f"      [diagnostic-raw] {company_name}: sample job location fields = {raw_fields}")

    if len(results) > 100:
        print(f"      [WARNING] {company_name}: {len(results)} Ireland postings is implausibly high — "
              f"likely means the location filter didn't actually work for this tenant despite the "
              f"client-side check passing. Treat this company's numbers with suspicion until verified.")

    return results, error


def candidate_slugs(company_name: str):
    """Guesses a small set of plausible ATS board slugs from a company name.
    e.g. 'VMware (Broadcom)' -> ['vmware', 'broadcom']; 'HubSpot' -> ['hubspot']

    Kept deliberately bounded — every extra candidate multiplies cost
    across all 8 platforms for every one of ~340 manual companies, most
    of which match nothing at all. The 'jobs' suffix pattern (found
    HubSpot's real token 'hubspotjobs') proved this kind of suffix
    convention is real and common, so 'careers' gets the same treatment —
    genuinely new, not a repeat of the bare-first-word guess that was
    tried and dropped for never producing a single real hit."""
    base = re.sub(r"\([^)]*\)", " ", company_name)  # drop "(Broadcom)" etc.
    base = CORP_SUFFIX_RE.sub(" ", base)
    words = re.findall(r"[a-zA-Z0-9]+", base)
    if not words:
        return []
    slugs = set()
    slugs.add("".join(words).lower())
    slugs.add("-".join(words).lower())
    slugs.add("".join(words).lower() + "jobs")  # e.g. HubSpot's real board token is 'hubspotjobs', not 'hubspot'
    slugs.add("".join(words).lower() + "careers")  # same convention, different common suffix
    if len(words) >= 2:
        slugs.add("".join(words[:2]).lower())   # first two words joined, e.g. "johnsonjohnson"
    return list(slugs)[:5]  # bounded — see docstring


def try_greenhouse(slug, session):
    try:
        resp = session.get(GREENHOUSE_JOBS_URL.format(slug=slug), headers=HEADERS, timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        jobs = data.get("jobs")
        return jobs if jobs else None
    except Exception:
        return None


def try_lever(slug, session):
    try:
        resp = session.get(LEVER_JOBS_URL.format(slug=slug), headers=HEADERS, timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        return data if isinstance(data, list) and data else None
    except Exception:
        return None


def normalize_greenhouse_job(company_name, job):
    location = (job.get("location") or {}).get("name", "")
    if not is_ireland_location(location):
        return None
    description = job.get("content", "") or ""
    sponsorship, snippet = classify_sponsorship(description)
    posted_text, days_ago = "Unknown", None
    updated = job.get("updated_at") or job.get("first_published")
    if updated:
        try:
            posted_dt = datetime.fromisoformat(updated.replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass
    return {
        "company": company_name,
        "title": job.get("title", "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(None, job.get("title", "")),
        "url": job.get("absolute_url", ""),
        "source": "greenhouse_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def normalize_lever_job(company_name, job):
    categories = job.get("categories") or {}
    location = categories.get("location", "") or ""
    if not is_ireland_location(location):
        return None
    description = (job.get("descriptionPlain") or job.get("description") or "")
    sponsorship, snippet = classify_sponsorship(description)
    posted_text, days_ago = "Unknown", None
    created_ms = job.get("createdAt")
    if created_ms:
        try:
            posted_dt = datetime.fromtimestamp(created_ms / 1000, tz=timezone.utc)
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass
    return {
        "company": company_name,
        "title": job.get("text", "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(categories.get("commitment"), job.get("text", "")),
        "url": job.get("hostedUrl", ""),
        "source": "lever_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def try_smartrecruiters_probe(slug, session):
    """Cheap single-page check used only during discovery (does this slug
    match at all?) — the full paginated fetch in try_smartrecruiters is
    reserved for once a company is actually confirmed, to avoid paying
    the multi-page cost twice for every real match."""
    try:
        resp = session.get(SMARTRECRUITERS_JOBS_URL.format(slug=slug), headers=HEADERS, timeout=10)
        if resp.status_code != 200:
            return None
        content = resp.json().get("content")
        return content if content else None
    except Exception:
        return None


def try_smartrecruiters(slug, session):
    """Paginates through ALL postings, not just the first page — the
    previous version only fetched page 1 with no offset/total check,
    which for a company posting globally (hundreds of postings) could
    easily miss Ireland-specific roles that just weren't in that first
    batch. Capped at a reasonable number of pages as a safety net."""
    all_content = []
    offset = 0
    page_size = 100
    for _ in range(10):  # up to 1000 postings, generous for any real company
        try:
            resp = session.get(SMARTRECRUITERS_JOBS_URL.format(slug=slug), headers=HEADERS,
                                params={"offset": offset, "limit": page_size}, timeout=10)
            if resp.status_code != 200:
                break
            data = resp.json()
            content = data.get("content") or []
            if not content:
                break
            all_content.extend(content)
            total_found = data.get("totalFound", len(all_content))
            offset += page_size
            if offset >= total_found:
                break
        except Exception:
            break
    return all_content if all_content else None


def fetch_smartrecruiters_description(slug, posting_id, session):
    """SmartRecruiters' list endpoint doesn't include the full description —
    a separate detail call is needed, same pattern as the Workday detail
    fetch. Only called for postings that already passed the Ireland filter,
    to keep the extra request count down."""
    try:
        url = SMARTRECRUITERS_DETAIL_URL.format(slug=slug, posting_id=posting_id)
        resp = session.get(url, headers=HEADERS, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        sections = (data.get("jobAd") or {}).get("sections") or {}
        parts = []
        for key in ("jobDescription", "qualifications", "additionalInformation"):
            text = (sections.get(key) or {}).get("text", "")
            if text:
                parts.append(text)
        return " ".join(parts)
    except Exception:
        return ""


def normalize_smartrecruiters_job(company_name, job, slug, session, fetch_descriptions):
    location_obj = job.get("location") or {}
    location = ", ".join(filter(None, [location_obj.get("city"), location_obj.get("region"),
                                        location_obj.get("country")]))
    if not is_ireland_location(location):
        return None

    posting_id = job.get("id", "")
    posted_text, days_ago = "Unknown", None
    released = job.get("releasedDate")
    if released:
        try:
            posted_dt = datetime.fromisoformat(released.replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass

    type_field = job.get("typeOfEmployment") or {}
    raw_employment_type = type_field.get("label") if isinstance(type_field, dict) else type_field

    sponsorship, snippet = "not_mentioned", None
    if fetch_descriptions and posting_id:
        desc = fetch_smartrecruiters_description(slug, posting_id, session)
        sponsorship, snippet = classify_sponsorship(desc)

    return {
        "company": company_name,
        "title": job.get("name", "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(raw_employment_type, job.get("name", "")),
        "url": f"https://jobs.smartrecruiters.com/{slug}/{posting_id}",
        "source": "smartrecruiters_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def try_ashby(slug, session):
    try:
        resp = session.get(ASHBY_JOBS_URL.format(slug=slug), headers=HEADERS, timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        jobs = data.get("jobs")
        return jobs if jobs else None
    except Exception:
        return None


def normalize_ashby_job(company_name, job):
    location = job.get("location", "") or job.get("locationName", "") or ""
    if not is_ireland_location(location):
        return None
    description = job.get("descriptionHtml", "") or job.get("descriptionPlain", "")
    sponsorship, snippet = classify_sponsorship(description)
    posted_text, days_ago = "Unknown", None
    published = job.get("publishedAt")
    if published:
        try:
            posted_dt = datetime.fromisoformat(published.replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass
    return {
        "company": company_name,
        "title": job.get("title", "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(job.get("employmentType"), job.get("title", "")),
        "url": job.get("applyUrl", "") or job.get("jobUrl", ""),
        "source": "ashby_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def try_recruitee(slug, session):
    try:
        resp = session.get(RECRUITEE_JOBS_URL.format(slug=slug), headers=HEADERS, timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        offers = data.get("offers")
        return offers if offers else None
    except Exception:
        return None


def normalize_recruitee_job(company_name, job):
    location = ", ".join(filter(None, [job.get("city"), job.get("country_code")]))
    if job.get("remote"):
        location = (location + " (Remote)").strip()
    if not is_ireland_location(location):
        return None
    description = job.get("description", "") or job.get("requirements", "")
    sponsorship, snippet = classify_sponsorship(description)
    posted_text, days_ago = "Unknown", None
    published = job.get("published_at")
    if published:
        try:
            posted_dt = datetime.fromisoformat(published.replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass
    return {
        "company": company_name,
        "title": job.get("title", "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(job.get("employment_type_code"), job.get("title", "")),
        "url": job.get("careers_url", ""),
        "source": "recruitee_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def try_personio(slug, session):
    """Personio exposes an unauthenticated XML job feed rather than JSON —
    same public-data idea as the others, different format. Returns a list
    of parsed <position> elements, or None if this isn't a real Personio
    board for this slug."""
    try:
        resp = session.get(PERSONIO_XML_URL.format(slug=slug), headers=HEADERS, timeout=10)
        if resp.status_code != 200 or not resp.text.strip():
            return None
        root = ET.fromstring(resp.text)
        positions = root.findall("position")
        return positions if positions else None
    except Exception:
        return None


def normalize_personio_job(company_name, slug, position):
    def field(tag):
        el = position.find(tag)
        return el.text.strip() if el is not None and el.text else ""

    office = field("office")
    if not is_ireland_location(office):
        return None

    description_parts = []
    for jd in position.findall("./jobDescriptions/jobDescription"):
        value = jd.find("jobDescriptionValue")
        if value is not None and value.text:
            description_parts.append(value.text)
    sponsorship, snippet = classify_sponsorship(" ".join(description_parts))

    posted_text, days_ago = "Unknown", None
    created = field("createdAt")
    if created:
        try:
            posted_dt = datetime.fromisoformat(created.replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass

    position_id = field("id")
    return {
        "company": company_name,
        "title": field("name"),
        "location": office,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(field("employmentType"), field("name")),
        "url": f"https://{slug}.jobs.personio.de/job/{position_id}",
        "source": "personio_xml",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def try_pinpoint(slug, session):
    try:
        resp = session.get(PINPOINT_JOBS_URL.format(slug=slug), headers={
            **HEADERS, "Accept": "application/json, text/javascript, */*; q=0.01",
            "X-Requested-With": "XMLHttpRequest",
        }, timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        jobs = data.get("data")
        return jobs if jobs else None
    except Exception:
        return None


def normalize_pinpoint_job(company_name, slug, job):
    """Pinpoint's documented schema examples are inconsistent between their
    JSON and RSS docs (some snake_case, some camelCase) — checking several
    likely field-name variants rather than assuming one exact shape."""
    location = job.get("location") or job.get("location_name") or job.get("locationName") or ""
    if isinstance(location, dict):
        location = ", ".join(filter(None, [location.get("city"), location.get("state"),
                                             location.get("country")]))
    location = str(location)
    if not is_ireland_location(location):
        return None

    description = (job.get("description") or job.get("htmlDescription") or
                    job.get("html_description") or job.get("benefits") or "")
    sponsorship, snippet = classify_sponsorship(description)

    posted_text, days_ago = "Unknown", None
    published = job.get("published_at") or job.get("publishedAt") or job.get("pubDate")
    if published:
        try:
            posted_dt = datetime.fromisoformat(str(published).replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass

    job_id = job.get("id", "")
    url = job.get("link") or job.get("url") or f"https://{slug}.pinpointhq.com/postings/{job_id}"

    return {
        "company": company_name,
        "title": (job.get("title") or "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(job.get("employmentType") or job.get("employment_type"), job.get("title") or ""),
        "url": url,
        "source": "pinpoint_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def extract_json_array_after(text, marker):
    """Finds `marker` (e.g. '"positions":') and extracts the JSON array
    that follows it by counting bracket depth — a simple regex like
    \\[.*?\\] breaks here because each job object contains its OWN nested
    arrays (e.g. "locations": [...]), so a naive 'stop at the first ]'
    match truncates at the wrong spot every time. This walks character by
    character and only stops when the brackets are actually balanced."""
    start = text.find(marker)
    if start == -1:
        return None
    bracket_start = text.find("[", start)
    if bracket_start == -1:
        return None
    depth = 0
    for i in range(bracket_start, len(text)):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return text[bracket_start:i + 1]
    return None


EF_GROUP_ID_RE = re.compile(r'_EF_GROUP_ID[\'"]?\]?\s*[=:]\s*[\'"]([^\'"]+)[\'"]')


def try_eightfold(slug, session):
    """Two attempts, tried in order of confidence:
    1. The simple domain-query pattern — confirmed genuinely working via a
       real, live reference (Netflix's own Eightfold-powered careers site
       uses exactly this shape). This constant existed in this file before
       but was never actually being called anywhere.
    2. The more complex group-ID-extraction approach from before, kept as
       a fallback in case a given tenant needs it — though it never once
       succeeded all session, so attempt 1 is tried first now."""
    try:
        resp = session.get(
            EIGHTFOLD_SMARTAPPLY_URL.format(slug=slug, domain=f"{slug}.com"),
            headers=HEADERS, timeout=10)
        if resp.status_code == 200:
            data = resp.json()
            positions = data.get("positions")
            if positions:
                return positions
    except Exception:
        pass

    try:
        page = session.get(f"https://{slug}.eightfold.ai/careers", headers=HEADERS, timeout=10)
        if page.status_code != 200:
            return None
        m = EF_GROUP_ID_RE.search(page.text)
        if not m:
            return None
        group_id = m.group(1)
        resp = session.get(
            f"https://{slug}.eightfold.ai/api/pcsx/search",
            params={"domain": group_id, "query": "", "location": "", "start": 0},
            headers=HEADERS, timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        positions = data.get("positions") or data.get("results")
        return positions if positions else None
    except Exception:
        return None


def scrape_netflix_ireland(session):
    """Netflix runs on Eightfold, but under its own custom-branded domain
    (explore.jobs.netflix.net) rather than the standard {slug}.eightfold.ai
    hosting — confirmed working directly, not guessed, so it needs its own
    override rather than relying on the generic slug-based pattern."""
    try:
        resp = session.get(
            "https://explore.jobs.netflix.net/api/apply/v2/jobs",
            params={"domain": "netflix.com", "start": 0, "num": 100, "query": ""},
            headers=HEADERS, timeout=15)
        if resp.status_code != 200:
            return []
        data = resp.json()
    except Exception:
        return []

    results = []
    for job in data.get("positions") or []:
        norm = normalize_eightfold_job("Netflix", "netflix", job)
        if norm:
            results.append(norm)
    return results


def normalize_eightfold_job(company_name, slug, job):
    location = (job.get("location") or job.get("locations") or job.get("city") or "")
    if isinstance(location, list):
        location = ", ".join(str(x) for x in location)
    location = str(location)
    if not is_ireland_location(location):
        return None

    description = job.get("job_description") or job.get("description") or job.get("text") or ""
    sponsorship, snippet = classify_sponsorship(description)

    posted_text, days_ago = "Unknown", None
    posted = job.get("t_create") or job.get("start_date") or job.get("posted_date")
    if posted:
        try:
            if isinstance(posted, (int, float)):
                posted_dt = datetime.fromtimestamp(posted, tz=timezone.utc)
            else:
                posted_dt = datetime.fromisoformat(str(posted).replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass

    job_id = job.get("id", "")
    url = job.get("canonicalPositionUrl") or job.get("apply_url") or \
        f"https://{slug}.eightfold.ai/careers/job/{job_id}"

    return {
        "company": company_name,
        "title": (job.get("name") or job.get("title") or "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(job.get("employment_type"), job.get("name") or job.get("title") or ""),
        "url": url,
        "source": "eightfold_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


# Phenom has no free public API (their real API requires a paid OAuth
# token). This uses a widely-documented reverse-engineered pattern
# instead: Phenom career pages embed a company-specific 'refNum' token in
# their HTML, which their own front-end JS uses to call an internal
# '/widgets' search endpoint. Less stable than the official public APIs
# above — Phenom could change this without notice — but real and working.
PHENOM_REFNUM_RE = re.compile(r'"refNum"\s*:\s*"([A-Za-z0-9_-]+)"')

# Companies whose EXACT real Phenom page was confirmed by direct research —
# generic sub-path guessing (/,/en,/search-jobs,/careers) never matched any
# of these, meaning their real search page lives at a more specific path
# than any short generic list would guess. Storing the precise confirmed
# path removes the guessing entirely for these.
KNOWN_PHENOM_DOMAINS = {
    "Baxter International": ("jobs.baxter.com", "/search-jobs/Ireland"),
    "Applied Materials": ("jobs.appliedmaterials.com", "/location/ireland-jobs/95/2963597/2"),
    "Palo Alto Networks": ("jobs.paloaltonetworks.com", "/en/location/dublin-jobs/47263/2963597-7521314-2964574/4"),
}

# Companies confirmed on Workable by direct research. Checked once each,
# not via the generic per-candidate loop — that loop was removed after
# real trace evidence showed Workable rate-limits us into uselessness
# when checking many companies' guessed slugs in sequence.
KNOWN_WORKABLE_SLUGS = {
    "Fenergo": "fenergocareers",
}


def fetch_phenom_jobs_by_refnum(domain, ref_num, session):
    """Re-fetches using an already-discovered domain+refnum pair (from
    cache), skipping the HTML scrape needed to find it the first time."""
    try:
        payload = {
            "lang": "en_global", "deviceType": "desktop", "country": "global",
            "pageName": "search-results", "size": 20, "from": 0,
            "jobs": True, "counts": True, "all_fields": ["category", "country", "city", "type"],
            "clearAll": False, "jdsource": "facets", "isSliderEnable": False,
            "pageId": "page20", "siteType": "external", "keywords": "", "global": True,
            "selected_fields": {}, "sort": {"order": "desc", "field": "postedDate"},
            "locationData": {}, "refNum": ref_num, "ddoKey": "refineSearch",
        }
        resp = session.post(f"https://{domain}/widgets", json=payload,
                             headers={"Content-Type": "application/json"}, timeout=15)
        if resp.status_code != 200:
            return []
        data = resp.json()
        return (data.get("refineSearch") or {}).get("data", {}).get("jobs", []) or []
    except Exception:
        return []


def try_phenom_domain(domain, session, verbose=True, exact_path=None):
    """Tries a specific known Phenom domain — an exact confirmed path first
    if provided (most reliable), then the bare root and a couple of common
    sub-paths as a fallback guess. Some tenants (confirmed: Baxter, Applied
    Materials, Palo Alto Networks) don't return anything usable at any
    generic path — only their specific real search-results URL works."""
    paths_to_try = ([exact_path] if exact_path else []) + ["/", "/en", "/search-jobs", "/careers"]
    for path in paths_to_try:
        try:
            page = session.get(f"https://{domain}{path}", headers=HEADERS, timeout=10)
            if page.status_code != 200:
                if verbose and path == exact_path:
                    print(f"      [phenom-diagnostic] {domain}{path}: exact confirmed path "
                          f"returned HTTP {page.status_code}, not 200")
                continue
            m = PHENOM_REFNUM_RE.search(page.text)
            if not m:
                if verbose:
                    print(f"      [phenom-diagnostic] {domain}{path}: page loaded (200) but no "
                          f"refNum pattern found — may not actually be Phenom, or uses a "
                          f"different embedding format than expected.")
                continue
            ref_num = m.group(1)
            payload = {
                "lang": "en_global", "deviceType": "desktop", "country": "global",
                "pageName": "search-results", "size": 20, "from": 0,
                "jobs": True, "counts": True, "all_fields": ["category", "country", "city", "type"],
                "clearAll": False, "jdsource": "facets", "isSliderEnable": False,
                "pageId": "page20", "siteType": "external", "keywords": "", "global": True,
                "selected_fields": {}, "sort": {"order": "desc", "field": "postedDate"},
                "locationData": {}, "refNum": ref_num, "ddoKey": "refineSearch",
            }
            resp = session.post(f"https://{domain}/widgets", json=payload,
                                 headers={"Content-Type": "application/json"}, timeout=15)
            if resp.status_code != 200:
                if verbose:
                    print(f"      [phenom-diagnostic] {domain}{path}: found refNum '{ref_num}' but "
                          f"/widgets API call failed with HTTP {resp.status_code}")
                continue
            data = resp.json()
            jobs = (data.get("refineSearch") or {}).get("data", {}).get("jobs", [])
            if not jobs and verbose:
                print(f"      [phenom-diagnostic] {domain}{path}: /widgets call succeeded (200) "
                      f"but returned zero jobs — response keys: {list(data.keys())}")
            if jobs:
                return ref_num, jobs
        except Exception:
            continue
    return None, None


def try_phenom(slug, session):
    """Tries jobs.{slug}.com and careers.{slug}.com — the two most common
    Phenom domain conventions. Returns (domain, refnum, jobs) or
    (None, None, None). Diagnostic prints only fire once we've confirmed a
    real Phenom domain (page loaded successfully) — this avoids spamming
    the log for the hundreds of wrong-guess slugs that fail immediately,
    while still showing exactly where it breaks for genuine matches."""
    for domain in (f"jobs.{slug}.com", f"careers.{slug}.com"):
        ref_num, jobs = try_phenom_domain(domain, session)
        if jobs:
            return domain, ref_num, jobs
    return None, None, None


def normalize_phenom_job(company_name, domain, job):
    location = (job.get("locationDisplay") or job.get("cityStateCountry") or
                job.get("cityCountry") or job.get("city") or "")
    if not is_ireland_location(str(location)):
        return None
    description = job.get("descriptionTeaser") or job.get("description") or ""
    sponsorship, snippet = classify_sponsorship(description)
    posted_text, days_ago = "Unknown", None
    posted = job.get("postedDate")
    if posted:
        try:
            posted_dt = datetime.fromisoformat(str(posted).replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass
    job_id = job.get("jobId") or job.get("id") or ""
    url = job.get("applyUrl") or job.get("jdUrl") or f"https://{domain}/job/{job_id}"
    return {
        "company": company_name,
        "title": (job.get("title") or job.get("jobTitle") or "").strip(),
        "location": str(location),
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(job.get("type"), job.get("title") or job.get("jobTitle") or ""),
        "url": url,
        "source": "phenom_widgets",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


WORKABLE_JOBS_URL = "https://apply.workable.com/api/v1/widget/accounts/{slug}"


def try_workable(slug, session):
    for attempt in range(2):  # one retry after a real, confirmed 429 rate-limit
        try:
            resp = session.get(WORKABLE_JOBS_URL.format(slug=slug), headers=HEADERS, timeout=10)
            if resp.status_code == 429:
                if attempt == 0:
                    time.sleep(3)
                    continue
                return None
            if resp.status_code != 200:
                return None
            data = resp.json()
            jobs = data.get("jobs")
            return jobs if jobs else None
        except Exception:
            return None
    return None


def normalize_workable_job(company_name, job):
    location_obj = job.get("location") or {}
    if isinstance(location_obj, dict):
        location = (location_obj.get("location_str") or
                    ", ".join(filter(None, [location_obj.get("city"), location_obj.get("country")])))
    else:
        location = str(location_obj)
    if not is_ireland_location(location):
        return None

    description = job.get("description") or ""
    sponsorship, snippet = classify_sponsorship(description)

    posted_text, days_ago = "Unknown", None
    published = job.get("published_on") or job.get("created_at")
    if published:
        try:
            posted_dt = datetime.fromisoformat(str(published).replace("Z", "+00:00"))
            days_ago = (datetime.now(timezone.utc) - posted_dt).days
            posted_text = f"Posted {days_ago} days ago" if days_ago > 0 else "Posted Today"
        except Exception:
            pass

    return {
        "company": company_name,
        "title": (job.get("title") or "").strip(),
        "location": location,
        "posted_text": posted_text,
        "posted_days_ago": days_ago,
        "employment_type": normalize_employment_type(job.get("employment_type") or job.get("type"), job.get("title") or ""),
        "url": job.get("url") or job.get("shortlink") or "",
        "source": "workable_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def _strip_html_tags(text):
    return re.sub(r"<[^>]+>", " ", str(text or ""))


def _html_to_text(fragment):
    return re.sub(r"\s+", " ", html.unescape(_strip_html_tags(fragment))).strip()


def scrape_apple_ireland(session):
    """Apple's careers site has no public API and no shared ATS — but unlike
    what I assumed, its search results page IS server-rendered: the job
    data is present in the raw HTML response itself, before any JavaScript
    runs (confirmed independently — search engine crawlers, which don't
    execute JS, have indexed full job listings including reference numbers
    directly from this URL). That means it can be parsed directly, the
    same class of technique as any other HTML scrape, just without a
    clean JSON API behind it."""
    base = "https://jobs.apple.com"
    url = base + "/en-ie/search?location=ireland-IRL"
    try:
        resp = session.get(url, headers=HEADERS, timeout=20)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []

    results = []
    blocks = re.findall(r"(<li[^>]*>.*?/en-ie/details/.*?</li>)", page, flags=re.I | re.S)
    if not blocks:
        blocks = re.split(r'(?=<a[^>]+href=["\']/en-ie/details/)', page, flags=re.I)

    seen_urls = set()
    for block in blocks:
        m = re.search(r'href=["\']([^"\']*/en-ie/details/[^"\']+)["\'][^>]*>(.*?)</a>',
                       block, flags=re.I | re.S)
        if not m:
            continue
        href = urllib.parse.urljoin(base, m.group(1))
        title = _html_to_text(m.group(2))
        if not title or href in seen_urls:
            continue
        seen_urls.add(href)

        block_text = _html_to_text(block)
        loc_match = re.search(r"Location\s+([^|•]+?)(?:Actions|Role Number|Weekly Hours|$)",
                               block_text, flags=re.I)
        location = loc_match.group(1).strip() if loc_match else "Ireland"
        if not is_ireland_location(location):
            continue

        date_match = re.search(r"\b(\d{1,2}\s+[A-Za-z]{3}\s+20\d{2}|[A-Za-z]{3}\s+\d{1,2},?\s+20\d{2})\b",
                                block_text)
        posted_text = date_match.group(1) if date_match else "Unknown"

        sponsorship, snippet = classify_sponsorship(block_text[:5000])

        results.append({
            "company": "Apple",
            "title": title,
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": None,
            "employment_type": normalize_employment_type(None, title),
            "url": href,
            "source": "apple_html",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        })
    return results


def _extract_html_blocks_for_links(page, href_pattern):
    """Splits a page into per-link chunks so each job's surrounding text
    (title, location, description) can be pulled out separately, instead
    of treating the whole page as one blob."""
    positions = [m.start() for m in re.finditer(href_pattern, page)]
    blocks = []
    for i, pos in enumerate(positions):
        start = max(0, pos - 300)
        end = positions[i + 1] if i + 1 < len(positions) else min(len(page), pos + 2000)
        blocks.append(page[start:end])
    return blocks


def scrape_amazon_ireland(session):
    """Amazon has no public developer API — confirmed earlier. But unlike
    what that meant for Apple, Amazon's search RESULTS PAGE genuinely is
    client-rendered (verified: crawled content showed only generic
    marketing text, no real listings). The actual data instead comes from
    a real internal JSON endpoint their own frontend JS calls —
    amazon.jobs/en/search.json — confirmed genuinely working (returned 197
    real Ireland postings with real requisition IDs when tested). A third,
    different category from both Apple (server-rendered HTML) and
    everything else: a real hidden API, just not a documented public one."""
    results, seen = [], set()
    limit = 100
    for offset in range(0, 600, limit):  # bounded — matches the confirmed-working reference implementation
        params = {"base_query": "", "loc_query": "Ireland", "country": "IRL",
                   "result_limit": limit, "offset": offset}
        url = "https://www.amazon.jobs/en/search.json?" + urllib.parse.urlencode(params)
        try:
            resp = session.get(url, headers=HEADERS, timeout=10)
            if resp.status_code != 200:
                break
            data = resp.json()
        except Exception:
            break
        jobs = data.get("jobs") or []
        if not jobs:
            break
        for job in jobs:
            title = job.get("title", "")
            location = job.get("normalized_location") or job.get("location") or ""
            if not is_ireland_location(location):
                continue
            path = job.get("job_path", "")
            job_id = str(job.get("id_icims") or job.get("id") or path or "")
            key = job_id or (title.lower(), location.lower())
            if key in seen:
                continue
            seen.add(key)
            description = job.get("description") or job.get("basic_qualifications") or ""
            sponsorship, snippet = classify_sponsorship(description[:5000])
            results.append({
                "company": "Amazon",
                "title": title,
                "location": location,
                "posted_text": job.get("posted_date", "Unknown"),
                "posted_days_ago": None,
                "employment_type": normalize_employment_type(None, title),
                "url": f"https://www.amazon.jobs{path}" if path else "https://www.amazon.jobs/en/",
                "source": "amazon_json",
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            })
        if len(jobs) < limit:
            break
        time.sleep(0.2)
    return results


# Filter/UI section headings that show up as real <h1-h3> elements on
# these career pages but are never actual job titles — confirmed via
# direct evidence (a real run returned "Locations", "Experience", "Degree"
# etc. as if they were postings, because the filter sidebar's applied-
# filter chip literally displays "Ireland" as text, passing the location
# check even though it has nothing to do with any real job).
_NON_JOB_HEADING_TEXTS = {
    "locations", "location", "experience", "skills & qualifications", "skills and qualifications",
    "degree", "job types", "job type", "organizations", "organization", "sort by", "filters",
    "filter", "clear all", "search", "featured jobs", "results", "refine your search",
    "expand_less", "expand_more", "info_outline", "remove", "which location(s) do you prefer?",
}


def _browser_text(locator):
    try:
        return re.sub(r"\s+", " ", locator.inner_text(timeout=3000)).strip()
    except Exception:
        return ""


def _browser_job_links(page, fragment):
    """Scrolls until the number of matching links stabilizes — handles
    infinite-scroll/lazy-loaded job lists instead of assuming everything
    is present on initial load."""
    stable, last = 0, -1
    for _ in range(25):
        count = page.locator(f'a[href*="{fragment}"]').count()
        stable = stable + 1 if count == last else 0
        last = count
        if stable >= 3:
            break
        page.mouse.wheel(0, 5000)
        page.wait_for_timeout(1200)
    return page.locator(f'a[href*="{fragment}"]')


def _browser_card(anchor):
    """Walks up the DOM from a job link to find its surrounding card text
    (title + location) — reads what's actually rendered on screen rather
    than guessing at an underlying API's data shape.

    Stops at the FIRST reasonably-sized candidate instead of continuing
    to expand — the earlier version kept walking until text stopped
    fitting under a loose 2500-char cap, which usually meant landing on
    a shared container holding MANY different jobs' info mashed together
    (confirmed by real evidence: every single card came back with the
    exact same oversized text, regardless of which link it started from).
    A single job's own card is normally well under a few hundred
    characters — once we're in a plausible range, stop growing."""
    MIN_LEN, MAX_LEN = 15, 500
    node = anchor
    best = ""
    for _ in range(6):
        node = node.locator("..")
        candidate = _browser_text(node)
        if not candidate:
            continue
        if len(candidate) > MAX_LEN:
            # Grew into a shared/multi-job container — stop and use
            # whatever the last reasonably-sized candidate was, even if
            # it didn't contain a matched location, rather than accepting
            # this oversized one.
            break
        if len(candidate) >= MIN_LEN:
            best = candidate
        if best and is_ireland_location(best):
            break
    return best


def _browser_scrape_jobs(company_name, url, link_fragment, source_tag):
    """Generic real-browser job scraper — works the same way regardless of
    whether the underlying site uses GraphQL, a REST API, or anything
    else, because it reads the actual rendered page rather than
    replicating a specific backend contract. This is the technique that
    replaced two earlier, more fragile attempts (a guessed Google RPC
    call, and a Meta-specific GraphQL network-interception approach) —
    both were tied to one company's exact internal API shape and broke or
    never worked; this one is shared and more resilient to change."""
    if not HAS_PLAYWRIGHT:
        return []
    results, seen = [], set()
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1000}, locale="en-IE")
            page.goto(url, wait_until="domcontentloaded", timeout=60000)
            page.wait_for_timeout(2000)
            # EU/Ireland-locale sessions almost always trigger a GDPR
            # cookie-consent banner — if it's never dismissed, some sites
            # never render the real content behind it at all. Try several
            # common real-world button phrasings; harmless if none match.
            consent_clicked = False
            for consent_text in ("Accept all", "Accept All", "I agree", "I Agree", "Accept",
                                  "Allow all", "Allow All", "Got it", "OK"):
                try:
                    btn = page.get_by_role("button", name=consent_text, exact=False)
                    if btn.count() > 0:
                        btn.first.click(timeout=2000)
                        page.wait_for_timeout(1000)
                        consent_clicked = True
                        break
                except Exception:
                    continue
            page.wait_for_timeout(2000)
            links = _browser_job_links(page, link_fragment)
            print(f"      [browser] {company_name}: consent banner clicked={consent_clicked}, "
                  f"matching links found={links.count()}")
            if links.count() == 0:
                # Zero links at all — the URL/page-structure assumption is
                # likely wrong. Show what's actually there instead of
                # guessing blind a third time.
                try:
                    print(f"      [browser] {company_name}: actual page title = {page.title()!r}, "
                          f"final URL = {page.url!r}")
                    body_sample = _browser_text(page.locator("body"))[:300]
                    print(f"      [browser] {company_name}: body text sample = {body_sample!r}")
                except Exception as e:
                    print(f"      [browser] {company_name}: couldn't read page for diagnostics ({e})")
            filtered_out_samples = []
            for i in range(links.count()):
                a = links.nth(i)
                href = urllib.parse.urljoin(url, a.get_attribute("href") or "")
                if not href or href in seen:
                    continue
                card = _browser_card(a)
                if not is_ireland_location(card):
                    if len(filtered_out_samples) < 3:
                        filtered_out_samples.append(card[:200])
                    continue
                title = _browser_text(a)
                if not title or len(title) > 300:
                    lines = [x.strip() for x in card.splitlines() if x.strip()]
                    title = next((x for x in lines if 4 <= len(x) <= 180 and not is_ireland_location(x)), "")
                if not title:
                    continue
                locs = [x.strip() for x in card.splitlines() if x.strip() and is_ireland_location(x)]
                seen.add(href)
                description = card[:5000]
                sponsorship, snippet = classify_sponsorship(description)
                posted_text, posted_days = extract_posted_from_text(card)
                results.append({
                    "company": company_name,
                    "title": title,
                    "location": locs[0] if locs else "Ireland",
                    "posted_text": posted_text,
                    "posted_days_ago": posted_days,
                    "employment_type": normalize_employment_type(None, title),
                    "url": href,
                    "source": source_tag,
                    "visa_sponsorship": sponsorship,
                    "visa_snippet": snippet,
                })
            if not results and filtered_out_samples:
                print(f"      [browser] {company_name}: {len(filtered_out_samples)} sample card(s) "
                      f"that got filtered out for not matching an Ireland location:")
                for s in filtered_out_samples:
                    print(f"      [browser]   -> {s!r}")
            browser.close()
    except Exception as e:
        print(f"      [browser] {company_name} failed: {e}")
    return results


def _extract_location_from_card(card_text, default="Ireland"):
    """Best-effort location extraction for already location-filtered career
    pages. Important: Google/Meta virtualized result cards do not always
    expose the location text in the same DOM subtree as the title/link.
    Because the page itself is explicitly filtered to Ireland, lack of
    visible location text is NOT a reason to discard the posting — this
    was the actual bug that made real Meta postings disappear (location
    hidden behind a collapsed '+N locations' control). Prefers a specific
    city when visible, otherwise safely falls back to the default."""
    lines = [x.strip() for x in (card_text or "").splitlines() if x.strip()]
    for line in lines:
        if is_ireland_location(line):
            return line[:180]
    return default


def _collect_filtered_page_jobs(page, company_name, href_regex, source_tag,
                                 results_by_url, default_location="Ireland"):
    """Collect job links currently rendered on a location-filtered page.
    Intentionally TRUSTS the page-level location filter already applied
    via the URL, rather than re-verifying 'Ireland' appears in each card's
    visible text — that redundant re-check was the actual bug (confirmed
    by real evidence) silently dropping genuine Ireland postings whenever
    a site didn't render location as plain text in the card."""
    href_re = re.compile(href_regex, re.I)
    anchors = page.locator("a[href]")
    for i in range(anchors.count()):
        a = anchors.nth(i)
        try:
            raw_href = a.get_attribute("href") or ""
            href = urllib.parse.urljoin(page.url, raw_href)
        except Exception:
            continue
        if not href_re.search(href) or href in results_by_url:
            continue

        title = _browser_text(a).strip()
        card = ""
        node = a
        for _ in range(5):
            try:
                node = node.locator("..")
                candidate = _browser_text(node)
            except Exception:
                break
            if candidate and len(candidate) <= 1600:
                card = candidate
            if card and len(card) >= 30:
                break

        # Meta often puts the title in a sibling/parent element while the
        # actual link text is empty — prefer a nearby heading in that case.
        if not title or len(title) > 260:
            try:
                hs = node.locator("h1, h2, h3, h4")
                if hs.count():
                    title = _browser_text(hs.first).strip()
            except Exception:
                pass
        if not title:
            lines = [x.strip() for x in card.splitlines() if 3 < len(x.strip()) <= 220]
            title = lines[0] if lines else ""
        if not title or title.lower() in _NON_JOB_HEADING_TEXTS:
            continue

        location = _extract_location_from_card(card, default_location)
        posted_text, posted_days = extract_posted_from_text(card)
        sponsorship, snippet = classify_sponsorship(card[:5000])
        results_by_url[href] = {
            "company": company_name,
            "title": title[:300],
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href,
            "source": source_tag,
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }


def scrape_google_ireland(session, fetch_descriptions=True):
    """Collect Google jobs whose Google Careers search is filtered to
    Ireland. Uses explicit ?page=N pagination (confirmed more reliable
    than scroll-based accumulation, which plateaued regardless of scroll
    time). Reads job TITLES FROM HEADINGS rather than per-job links —
    real evidence showed Google, unlike Meta, doesn't expose individual
    job listings as distinct clickable links with unique hrefs (an href-
    based version of this function found 0 real results across 2 pages,
    while this heading-based approach has confirmed real hits before).
    Trusts the page-level ?location=Ireland filter for location, the same
    principle that fixed Meta, rather than requiring 'Ireland' literally
    inside each heading's nearby text."""
    if not HAS_PLAYWRIGHT:
        print("      [google] playwright not installed — skipping")
        return []

    base = "https://www.google.com/about/careers/applications/jobs/results"
    seen_titles, results = set(), []
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")

            empty_pages = 0
            for page_no in range(1, 31):  # hard safety ceiling
                query = urllib.parse.urlencode({"location": "Ireland", "page": page_no})
                url = f"{base}?{query}"
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1500)

                if page_no == 1:
                    for consent_text in ("Accept all", "Accept All", "I agree", "I Agree", "Accept",
                                         "Allow all", "Allow All", "Got it", "OK"):
                        try:
                            btn = page.get_by_role("button", name=consent_text, exact=False)
                            if btn.count() and btn.first.is_visible():
                                btn.first.click(timeout=1500)
                                page.wait_for_timeout(500)
                                break
                        except Exception:
                            pass

                before = len(results)
                headings = page.locator("h3")
                for i in range(headings.count()):
                    h = headings.nth(i)
                    title = _browser_text(h)
                    if not title or len(title) > 200 or title.strip().lower() in _NON_JOB_HEADING_TEXTS:
                        continue
                    key = title.lower().strip()
                    if key in seen_titles:
                        continue
                    seen_titles.add(key)
                    node = h
                    card = ""
                    for _ in range(4):
                        node = node.locator("..")
                        candidate = _browser_text(node)
                        if candidate and len(candidate) < 500:
                            card = candidate
                        if candidate and len(candidate) >= 30:
                            break
                    # Trust the page-level Ireland filter — don't require
                    # 'Ireland' literally in the card text (same fix that
                    # rescued Meta's real postings from being dropped).
                    location = _extract_location_from_card(card, "Ireland")
                    posted_text, posted_days = extract_posted_from_text(card)
                    sponsorship, snippet = classify_sponsorship(card[:5000])
                    results.append({
                        "company": "Google",
                        "title": title,
                        "location": location,
                        "posted_text": posted_text,
                        "posted_days_ago": posted_days,
                        "employment_type": normalize_employment_type(None, title),
                        "url": url,
                        "source": "google_browser",
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    })
                added = len(results) - before
                print(f"      [google] page {page_no}: +{added} jobs ({len(results)} total)")
                if added == 0:
                    empty_pages += 1
                else:
                    empty_pages = 0
                if empty_pages >= 2:
                    break

            browser.close()
    except Exception as e:
        print(f"      [google] browser scrape failed: {e}")

    return results


def scrape_meta_ireland(session):
    """Collect Meta jobs from its Ireland office pages directly. Meta's
    current public detail links are /profile/job_details/<numeric-id>/,
    not an older pattern — confirmed real, current. Dublin and Clonee are
    both real Meta Ireland office locations; scraping each office's own
    pre-filtered page sidesteps the '+N locations' problem entirely,
    since we don't need to verify location text when the page itself is
    already scoped to that specific office."""
    if not HAS_PLAYWRIGHT:
        print("      [meta] playwright not installed — skipping")
        return []

    ireland_pages = [
        ("Dublin, Ireland",
         "https://www.metacareers.com/locations/dublin/?offices%5B0%5D=Dublin%2C+Ireland&p%5Boffices%5D%5B0%5D=Dublin%2C+Ireland"),
        ("Clonee, Ireland",
         "https://www.metacareers.com/locations/clonee/?offices%5B0%5D=Clonee%2C+Ireland&p%5Boffices%5D%5B0%5D=Clonee%2C+Ireland"),
    ]
    results_by_url = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")

            for default_location, url in ireland_pages:
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1800)

                for consent_text in ("Accept all", "Accept All", "I agree", "I Agree", "Accept",
                                     "Allow all", "Allow All", "Got it", "OK"):
                    try:
                        btn = page.get_by_role("button", name=consent_text, exact=False)
                        if btn.count() and btn.first.is_visible():
                            btn.first.click(timeout=1500)
                            page.wait_for_timeout(500)
                            break
                    except Exception:
                        pass

                stagnant = 0
                previous = len(results_by_url)
                for _ in range(100):
                    _collect_filtered_page_jobs(
                        page, "Meta",
                        r"metacareers\.com/profile/job_details/\d+/?",
                        "meta_browser", results_by_url, default_location
                    )

                    for more_text in ("Show more", "Load more", "See more", "More jobs", "View more"):
                        try:
                            btn = page.get_by_role("button", name=more_text, exact=False)
                            if btn.count() and btn.first.is_visible():
                                btn.first.click(timeout=1000)
                                page.wait_for_timeout(400)
                        except Exception:
                            pass

                    page.mouse.wheel(0, 3200)
                    page.wait_for_timeout(500)
                    _collect_filtered_page_jobs(
                        page, "Meta",
                        r"metacareers\.com/profile/job_details/\d+/?",
                        "meta_browser", results_by_url, default_location
                    )

                    current = len(results_by_url)
                    if current == previous:
                        stagnant += 1
                    else:
                        stagnant = 0
                    previous = current
                    if stagnant >= 12:
                        break

                print(f"      [meta] {default_location}: {len(results_by_url)} unique Ireland jobs accumulated")

            browser.close()
    except Exception as e:
        print(f"      [meta] browser scrape failed: {e}")

    return list(results_by_url.values())





def _browser_accept_consent(page):
    for consent_text in ("Accept all", "Accept All", "I agree", "I Agree", "Accept",
                         "Allow all", "Allow All", "Got it", "OK"):
        try:
            btn = page.get_by_role("button", name=consent_text, exact=False)
            if btn.count() and btn.first.is_visible():
                btn.first.click(timeout=1500)
                page.wait_for_timeout(400)
                return True
        except Exception:
            pass
    return False


def _collect_links_from_html(page, company_name, href_regex, source_tag,
                             results_by_url, default_location="Ireland"):
    """Fallback for pages where job cards are server-rendered but Playwright
    locators do not expose the link cleanly — parses the raw page markup
    directly instead of going through Playwright's DOM query layer, which
    can miss links a plain regex over the actual HTML still catches."""
    try:
        markup = page.content()
    except Exception:
        return
    rx = re.compile(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', re.I | re.S)
    href_re = re.compile(href_regex, re.I)
    for raw_href, body in rx.findall(markup):
        href = urllib.parse.urljoin(page.url, html.unescape(raw_href))
        if not href_re.search(href) or href in results_by_url:
            continue
        title = _html_to_text(body)
        if not title or title.lower() in _NON_JOB_HEADING_TEXTS or len(title) > 300:
            continue
        sponsorship, snippet = classify_sponsorship("")
        results_by_url[href] = {
            "company": company_name,
            "title": title,
            "location": default_location,
            "posted_text": "Unknown",
            "posted_days_ago": None,
            "employment_type": normalize_employment_type(None, title),
            "url": href,
            "source": source_tag,
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }


def scrape_ey_ireland(session):
    """EY uses SAP SuccessFactors — confirmed earlier to have no free public
    API, which only mattered for a requests-based approach. Real browser
    automation doesn't need an API, it just reads the page like a human
    would, so the earlier 'no API' conclusion doesn't block this. Walks
    SuccessFactors' locationsearch + startrow pagination."""
    if not HAS_PLAYWRIGHT:
        print("      [ey] playwright not installed — skipping")
        return []
    base = "https://careers.ey.com/ey/search/"
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            stagnant = 0
            for startrow in range(0, 2500, 25):
                url = base + "?" + urllib.parse.urlencode({"q": "", "locationsearch": "Ireland", "startrow": startrow})
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1000)
                if startrow == 0:
                    _browser_accept_consent(page)
                before = len(results)
                _collect_filtered_page_jobs(page, "EY Ireland", r"careers\.ey\.com/ey/job/", "ey_successfactors", results, "Ireland")
                _collect_links_from_html(page, "EY Ireland", r"careers\.ey\.com/ey/job/", "ey_successfactors", results, "Ireland")
                added = len(results) - before
                print(f"      [ey] startrow={startrow}: +{added} jobs ({len(results)} total)")
                stagnant = stagnant + 1 if added == 0 else 0
                if stagnant >= 2:
                    break
            browser.close()
    except Exception as e:
        print(f"      [ey] browser scrape failed: {e}")
    return list(results.values())


def scrape_kpmg_ireland(session):
    """KPMG Ireland's live experienced-hire board is Avature — same story
    as EY: no free API, but browser automation doesn't need one. Walks
    Avature's folderOffset pagination."""
    if not HAS_PLAYWRIGHT:
        print("      [kpmg] playwright not installed — skipping")
        return []
    base = "https://kpmgireland.avature.net/careers/SearchJobs/"
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            stagnant = 0
            for offset in range(0, 1000, 10):
                url = base + "?" + urllib.parse.urlencode({"folderOffset": offset})
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(900)
                if offset == 0:
                    _browser_accept_consent(page)
                before = len(results)
                _collect_filtered_page_jobs(page, "KPMG Ireland", r"kpmgireland\.avature\.net/careers/(?:JobDetail|jobdetail|FolderDetail|folderdetail)", "kpmg_avature", results, "Ireland")
                _collect_links_from_html(page, "KPMG Ireland", r"kpmgireland\.avature\.net/careers/(?:JobDetail|jobdetail|FolderDetail|folderdetail)", "kpmg_avature", results, "Ireland")
                added = len(results) - before
                print(f"      [kpmg] folderOffset={offset}: +{added} jobs ({len(results)} total)")
                stagnant = stagnant + 1 if added == 0 else 0
                if stagnant >= 2:
                    break
            browser.close()
    except Exception as e:
        print(f"      [kpmg] browser scrape failed: {e}")
    return list(results.values())


def scrape_tiktok_ireland(session):
    """TikTok's current careers frontend is lifeattiktok.com (different
    from the older careers.tiktok.com custom-token URLs checked earlier
    this session — real evidence they've since moved to a more
    conventional, searchable board). Uses the site's own real search box."""
    if not HAS_PLAYWRIGHT:
        print("      [tiktok] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://lifeattiktok.com/search", wait_until="domcontentloaded", timeout=60000)
            page.wait_for_timeout(1200)
            _browser_accept_consent(page)
            try:
                inp = page.get_by_placeholder(re.compile(r"Enter Title, Skill, or City", re.I))
                if inp.count():
                    inp.first.fill("Dublin")
                    btn = page.get_by_role("button", name=re.compile(r"Search now|Search", re.I))
                    if btn.count():
                        btn.first.click(timeout=3000)
                        page.wait_for_timeout(1400)
            except Exception:
                pass

            stagnant, previous = 0, 0
            for _ in range(120):
                _collect_filtered_page_jobs(page, "TikTok Ireland", r"lifeattiktok\.com/search/\d+", "tiktok_browser", results, "Dublin, Ireland")
                _collect_links_from_html(page, "TikTok Ireland", r"lifeattiktok\.com/search/\d+", "tiktok_browser", results, "Dublin, Ireland")
                for txt in ("Load more", "Show more", "See more", "More jobs"):
                    try:
                        b = page.get_by_role("button", name=txt, exact=False)
                        if b.count() and b.first.is_visible():
                            b.first.click(timeout=1000)
                            page.wait_for_timeout(350)
                    except Exception:
                        pass
                page.mouse.wheel(0, 3000)
                page.wait_for_timeout(350)
                current = len(results)
                stagnant = stagnant + 1 if current == previous else 0
                previous = current
                if stagnant >= 6:
                    break
            print(f"      [tiktok] {len(results)} unique Ireland jobs accumulated")
            browser.close()
    except Exception as e:
        print(f"      [tiktok] browser scrape failed: {e}")
    return list(results.values())


def _collect_verified_ireland_page_jobs(page, company_name, href_regex, source_tag,
                                        results_by_url, default_location="Ireland"):
    """Like _collect_filtered_page_jobs, but requires Ireland evidence in the
    surrounding result card. Useful for boards whose location-filtered pages
    may append unrelated "similar jobs" underneath the real filtered results."""
    href_re = re.compile(href_regex, re.I)
    anchors = page.locator("a[href]")
    for i in range(anchors.count()):
        a = anchors.nth(i)
        try:
            href = urllib.parse.urljoin(page.url, a.get_attribute("href") or "")
        except Exception:
            continue
        if not href_re.search(href) or href in results_by_url:
            continue
        node, card = a, ""
        for _ in range(6):
            try:
                node = node.locator("..")
                candidate = _browser_text(node)
            except Exception:
                break
            if candidate and len(candidate) <= 1800:
                card = candidate
            if card and (is_ireland_location(card) or re.search(r"\bIE\b", card)):
                break
        if not (is_ireland_location(card) or re.search(r"\bIE\b", card)):
            continue
        title = _browser_text(a).strip()
        if not title or len(title) > 300:
            lines = [x.strip() for x in card.splitlines() if 4 <= len(x.strip()) <= 220]
            title = lines[0] if lines else ""
        if not title or title.lower() in _NON_JOB_HEADING_TEXTS:
            continue
        location = _extract_location_from_card(card, default_location)
        posted_text, posted_days = extract_posted_from_text(card)
        sponsorship, snippet = classify_sponsorship(card[:5000])
        results_by_url[href] = {
            "company": company_name,
            "title": title[:300],
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href,
            "source": source_tag,
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }


def scrape_boston_scientific_ireland(session):
    """Boston Scientific runs SAP SuccessFactors. Its Ireland location pages
    are server-rendered and can include unrelated 'similar jobs', so collect
    only rows/cards that themselves show an Irish city/country marker."""
    if not HAS_PLAYWRIGHT:
        print("      [boston-scientific] playwright not installed — skipping")
        return []
    pages = [
        ("Galway, Ireland", "https://jobs.bostonscientific.com/go/All-Jobs-in-Galway%2C-Ireland/392200/"),
        ("Cork, Ireland", "https://jobs.bostonscientific.com/go/All-Jobs-in-Cork%2C-Ireland/392198/"),
        ("Clonmel, Ireland", "https://jobs.bostonscientific.com/go/All-Jobs-in-Clonmel%2C-Ireland/392199/"),
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for default_location, base in pages:
                stagnant = 0
                for startrow in range(0, 500, 25):
                    url = base if startrow == 0 else base.rstrip("/") + f"/{startrow}/"
                    page.goto(url, wait_until="domcontentloaded", timeout=60000)
                    page.wait_for_timeout(800)
                    if startrow == 0:
                        _browser_accept_consent(page)
                    before = len(results)
                    _collect_verified_ireland_page_jobs(
                        page, "Boston Scientific",
                        r"jobs\.bostonscientific\.com/job/[^/]+/\d+/?",
                        "boston_scientific_successfactors", results, default_location)
                    added = len(results) - before
                    if startrow == 0:
                        print(f"      [boston-scientific] {default_location}: +{added} jobs")
                    stagnant = stagnant + 1 if added == 0 else 0
                    if stagnant >= 2:
                        break
            browser.close()
    except Exception as e:
        print(f"      [boston-scientific] browser scrape failed: {e}")
    print(f"      [boston-scientific] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())



def _collect_browser_job_links(page, company_name, href_patterns, source_tag, results, default_location="Ireland"):
    """Collect individual job links from the currently rendered browser page.
    href_patterns is a list of regexes. The surrounding card must contain
    Ireland evidence unless the caller explicitly supplies a page that is
    already scoped to one Ireland location."""
    patterns = [re.compile(x, re.I) for x in href_patterns]
    anchors = page.locator("a[href]")
    for i in range(anchors.count()):
        a = anchors.nth(i)
        try:
            raw = a.get_attribute("href") or ""
            href = urllib.parse.urljoin(page.url, raw)
        except Exception:
            continue
        if not any(rx.search(href) for rx in patterns):
            continue
        key = href.split("?")[0].rstrip("/").lower()
        if key in results:
            continue
        node, card = a, ""
        for _ in range(6):
            try:
                node = node.locator("..")
                text = _browser_text(node)
            except Exception:
                break
            if text and len(text) <= 2500:
                card = text
            if card and (is_ireland_location(card) or re.search(r"\bIE\b", card, re.I)):
                break
        if not (is_ireland_location(card) or re.search(r"\bIE\b", card, re.I)):
            continue
        title = _browser_text(a).strip()
        if not title or len(title) > 300:
            try:
                hs = node.locator("h1, h2, h3, h4")
                if hs.count():
                    title = _browser_text(hs.first).strip()
            except Exception:
                pass
        if not title:
            lines = [x.strip() for x in card.splitlines() if 4 <= len(x.strip()) <= 220]
            title = lines[0] if lines else ""
        if not title or title.lower() in _NON_JOB_HEADING_TEXTS:
            continue
        location = _extract_location_from_card(card, default_location)
        posted_text, posted_days = extract_posted_from_text(card)
        sponsorship, snippet = classify_sponsorship(card[:5000])
        results[key] = {
            "company": company_name,
            "title": title[:300],
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href,
            "source": source_tag,
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }


def scrape_microsoft_ireland(session):
    """Microsoft's Dublin page is dynamically rendered. The old raw-HTML
    scraper commonly saw only the first three cards while the live page had
    additional openings. Use the real browser and keep following rendered
    job links, while requiring Ireland in each result card."""
    if not HAS_PLAYWRIGHT:
        print("      [microsoft] playwright not installed — skipping")
        return []
    urls = [
        "https://careers.microsoft.com/v2/global/en/locations/dublin.html",
        "https://jobs.careers.microsoft.com/global/en/search?q=&lc=Ireland",
        "https://apply.careers.microsoft.com/careers?location=Ireland",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for start_url in urls:
                page.goto(start_url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1800)
                if start_url == urls[0]:
                    _browser_accept_consent(page)
                stagnant = 0
                previous = 0
                for _ in range(25):
                    _collect_browser_job_links(
                        page, "Microsoft",
                        [r"careers\.microsoft\.com/.*/job/", r"jobs\.careers\.microsoft\.com/.*/job/",
                         r"apply\.careers\.microsoft\.com/", r"/job/"],
                        "microsoft_browser", results, "Ireland")
                    for txt in ("Load more", "Show more", "See more", "Next"):
                        try:
                            b = page.get_by_role("button", name=txt, exact=False)
                            if b.count() and b.first.is_visible():
                                b.first.click(timeout=1500)
                                page.wait_for_timeout(700)
                        except Exception:
                            pass
                    page.mouse.wheel(0, 3500)
                    page.wait_for_timeout(500)
                    current = len(results)
                    stagnant = stagnant + 1 if current == previous else 0
                    previous = current
                    if stagnant >= 5:
                        break
            browser.close()
    except Exception as e:
        print(f"      [microsoft] browser scrape failed: {e}")
    print(f"      [microsoft] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_citi_ireland(session):
    """Citi's Dublin search is paginated. The old implementation visited a
    few hard-coded URLs and could stop at 25 while the official search had
    more pages. Follow the numbered result pages and deduplicate by job URL."""
    if not HAS_PLAYWRIGHT:
        print("      [citi] playwright not installed — skipping")
        return []
    base = "https://jobs.citi.com/location/dublin/5441/2963597-7521314-2964574/4/{}"
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for page_no in range(1, 8):
                url = base.format(page_no)
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1200)
                if page_no == 1:
                    _browser_accept_consent(page)
                before = len(results)
                _collect_browser_job_links(
                    page, "Citi",
                    [r"jobs\.citi\.com/job/dublin/", r"jobs\.citi\.com/en/job/dublin/", r"jobs\.citi\.com/job/"],
                    "citi_browser", results, "Dublin, Leinster, Ireland")
                added = len(results) - before
                print(f"      [citi] page {page_no}: +{added} jobs ({len(results)} total)")
                # Current Citi pages expose the total in the page text. Stop
                # after the first empty page; the URL itself is authoritative
                # enough that we don't need to guess a fixed page count.
                if added == 0 and page_no > 1:
                    break
            browser.close()
    except Exception as e:
        print(f"      [citi] browser scrape failed: {e}")
    print(f"      [citi] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_red_hat_ireland(session):
    """Red Hat's locations page links into its live country search. Use a
    browser so the Ireland country link and subsequent dynamic results are
    actually rendered rather than scraping navigation text as jobs."""
    if not HAS_PLAYWRIGHT:
        print("      [red-hat] playwright not installed — skipping")
        return []
    start = "https://www.redhat.com/en/jobs/locations"
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto(start, wait_until="domcontentloaded", timeout=60000)
            page.wait_for_timeout(1200)
            _browser_accept_consent(page)
            # Prefer the actual Ireland country link; if it is not a direct
            # href, click the visible text and let the site route normally.
            ireland_link = page.get_by_role("link", name=re.compile(r"^Ireland$", re.I))
            ireland_link_found = ireland_link.count() > 0
            if ireland_link_found:
                try:
                    ireland_link.first.click(timeout=3000)
                    page.wait_for_timeout(3000)  # was 1500 — real results page needs more time to render
                except Exception:
                    pass
            try:
                all_links = page.locator("a[href]")
                hrefs = [all_links.nth(i).get_attribute("href") or "" for i in range(all_links.count())]
                matching = sum(1 for h in hrefs if re.search(r"redhat\.com/.*job", h, re.I))
                print(f"      [red-hat] Ireland link found={ireland_link_found}, page title={page.title()!r}, "
                      f"total links={len(hrefs)}, matching job-pattern links={matching}")
                sample = [h for h in hrefs if h and "redhat" in h.lower()][:10]
                print(f"      [red-hat] sample real hrefs on page: {sample}")
            except Exception as e:
                print(f"      [red-hat] diagnostic read failed: {e}")
            _collect_browser_job_links(
                page, "Red Hat",
                [r"redhat\.com/.*job", r"redhat\.com/en/jobs/", r"redhat\.com/jobs/"],
                "redhat_browser", results, "Ireland")
            for _ in range(20):
                for txt in ("Load more", "Show more", "See more", "Next"):
                    try:
                        b = page.get_by_role("button", name=txt, exact=False)
                        if b.count() and b.first.is_visible():
                            b.first.click(timeout=1200)
                            page.wait_for_timeout(500)
                    except Exception:
                        pass
                page.mouse.wheel(0, 3500)
                page.wait_for_timeout(400)
                before = len(results)
                _collect_browser_job_links(
                    page, "Red Hat",
                    [r"redhat\.com/.*job", r"redhat\.com/en/jobs/", r"redhat\.com/jobs/"],
                    "redhat_browser", results, "Ireland")
                if len(results) == before:
                    break
            browser.close()
    except Exception as e:
        print(f"      [red-hat] browser scrape failed: {e}")
    print(f"      [red-hat] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_jnj_ireland(session):
    """Johnson & Johnson's first-party careers site supports an Ireland
    location query. Accumulate its current result cards while scrolling and
    loading more, trusting the page-level Ireland filter."""
    if not HAS_PLAYWRIGHT:
        print("      [jnj] playwright not installed — skipping")
        return []
    results = {}
    urls = [
        "https://www.careers.jnj.com/en/locations/emea/ireland/",
        "https://www.careers.jnj.com/en/jobs/?search=Ireland",
    ]
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1200)
                # Real evidence: this site shows a Cloudflare "Just a
                # moment..." bot-check page first, which auto-resolves
                # after several seconds for a genuine browser. Poll for it
                # to clear instead of a fixed short wait that's nowhere
                # near long enough for the JS challenge to complete.
                for _ in range(12):
                    if "just a moment" not in (page.title() or "").lower():
                        break
                    page.wait_for_timeout(1000)
                _browser_accept_consent(page)
                try:
                    all_links = page.locator("a[href]")
                    matching = sum(1 for i in range(all_links.count())
                                   if re.search(r"careers\.jnj\.com/en/job", (all_links.nth(i).get_attribute("href") or ""), re.I))
                    print(f"      [jnj] {url}: page title={page.title()!r}, total links={all_links.count()}, "
                          f"matching job-pattern links={matching}")
                except Exception as e:
                    print(f"      [jnj] diagnostic read failed: {e}")
                stagnant, previous = 0, 0
                for _ in range(100):
                    _collect_filtered_page_jobs(
                        page, "Johnson & Johnson",
                        r"careers\.jnj\.com/en/job(?:s)?/",
                        "jnj_browser", results, "Ireland")
                    _collect_links_from_html(
                        page, "Johnson & Johnson",
                        r"careers\.jnj\.com/en/job(?:s)?/",
                        "jnj_browser", results, "Ireland")
                    for txt in ("Load more", "Show more", "See more", "Next"):
                        try:
                            b = page.get_by_role("button", name=txt, exact=False)
                            if b.count() and b.first.is_visible():
                                b.first.click(timeout=1000)
                                page.wait_for_timeout(400)
                        except Exception:
                            pass
                    page.mouse.wheel(0, 3000)
                    page.wait_for_timeout(350)
                    current = len(results)
                    stagnant = stagnant + 1 if current == previous else 0
                    previous = current
                    if stagnant >= 8:
                        break
            browser.close()
    except Exception as e:
        print(f"      [jnj] browser scrape failed: {e}")
    print(f"      [jnj] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_johnson_controls_ireland(session):
    """Johnson Controls' current first-party search is a JS/Algolia-style
    board. Use its real Ireland refinement and additionally verify Ireland in
    each rendered card so a failed/refused URL filter cannot leak global jobs."""
    if not HAS_PLAYWRIGHT:
        print("      [johnson-controls] playwright not installed — skipping")
        return []
    results = {}
    params = urllib.parse.urlencode({
        "production_JCI_jobs[refinementList][locations_list][0]": "Ireland"
    })
    url = "https://jobs.johnsoncontrols.com/job-search?" + params
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto(url, wait_until="domcontentloaded", timeout=60000)
            page.wait_for_timeout(1400)
            _browser_accept_consent(page)
            stagnant, previous = 0, 0
            for _ in range(120):
                _collect_verified_ireland_page_jobs(
                    page, "Johnson Controls", r"jobs\.johnsoncontrols\.com/job/WD\d+/?",
                    "johnson_controls_browser", results, "Ireland")
                for txt in ("Load more", "Show more", "See more", "Next"):
                    try:
                        b = page.get_by_role("button", name=txt, exact=False)
                        if b.count() and b.first.is_visible():
                            b.first.click(timeout=1000)
                            page.wait_for_timeout(350)
                    except Exception:
                        pass
                page.mouse.wheel(0, 3200)
                page.wait_for_timeout(350)
                current = len(results)
                stagnant = stagnant + 1 if current == previous else 0
                previous = current
                if stagnant >= 8:
                    break
            browser.close()
    except Exception as e:
        print(f"      [johnson-controls] browser scrape failed: {e}")
    print(f"      [johnson-controls] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_hsbc_ireland(session):
    """HSBC Ireland's live careers site runs SAP SuccessFactors — same
    platform, same technique as EY, adapted to HSBC's own search URL and
    parameters."""
    if not HAS_PLAYWRIGHT:
        print("      [hsbc] playwright not installed — skipping")
        return []
    search_urls = [
        "https://apply.careers.hsbc.com/search/?q=&locationsearch=Dublin",
        "https://apply.careers.hsbc.com/search/?q=&locationsearch=Ireland",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for search_url in search_urls:
                page.goto(search_url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1200)
                _browser_accept_consent(page)
                try:
                    all_links = page.locator("a[href]")
                    hrefs = [all_links.nth(i).get_attribute("href") or "" for i in range(all_links.count())]
                    matching = sum(1 for h in hrefs if re.search(r"hsbc\.com/(?:job|position|opportunit|career)", h, re.I))
                    print(f"      [hsbc] {search_url}: page title={page.title()!r}, total links={len(hrefs)}, "
                          f"matching job-pattern links={matching}")
                    sample = [h for h in hrefs if h and "hsbc" in h.lower()][:8]
                    print(f"      [hsbc] sample real hrefs on page: {sample}")
                except Exception as e:
                    print(f"      [hsbc] diagnostic read failed: {e}")
                stagnant, previous = 0, 0
                for _ in range(60):
                    _collect_filtered_page_jobs(
                        page, "HSBC Ireland",
                        r"hsbc\.com/(?:job|position|opportunit|career)",
                        "hsbc_successfactors", results, "Dublin, Ireland")
                    _collect_links_from_html(
                        page, "HSBC Ireland",
                        r"hsbc\.com/(?:job|position|opportunit|career)",
                        "hsbc_successfactors", results, "Dublin, Ireland")
                    for txt in ("Load more", "Show more", "See more", "Next"):
                        try:
                            b = page.get_by_role("button", name=txt, exact=False)
                            if b.count() and b.first.is_visible():
                                b.first.click(timeout=1000)
                                page.wait_for_timeout(400)
                        except Exception:
                            pass
                    page.mouse.wheel(0, 3000)
                    page.wait_for_timeout(350)
                    current = len(results)
                    stagnant = stagnant + 1 if current == previous else 0
                    previous = current
                    if stagnant >= 6:
                        break
            browser.close()
    except Exception as e:
        print(f"      [hsbc] browser scrape failed: {e}")
    print(f"      [hsbc] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_dxc_ireland(session):
    """DXC Technology is currently stuck in the Workday 422-error cluster
    (a shared, unresolved block affecting ~15 tenants this whole session).
    Bypasses that entirely with a direct scrape of their own public
    careers site instead."""
    if not HAS_PLAYWRIGHT:
        print("      [dxc] playwright not installed — skipping")
        return []
    urls = [
        "https://careers.dxc.com/job-search-results/?location=Ireland",
        "https://careers.dxc.com/job-search-results/?keyword=&location=Ireland",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                page.goto(url, wait_until="domcontentloaded", timeout=60000)
                page.wait_for_timeout(1200)
                _browser_accept_consent(page)
                try:
                    all_links = page.locator("a[href]")
                    hrefs = [all_links.nth(i).get_attribute("href") or "" for i in range(all_links.count())]
                    matching = sum(1 for h in hrefs if re.search(r"careers\.dxc\.com/job", h, re.I))
                    print(f"      [dxc] {url}: page title={page.title()!r}, total links={len(hrefs)}, "
                          f"matching job-pattern links={matching}")
                    sample = [h for h in hrefs if h and "dxc" in h.lower()][:8]
                    print(f"      [dxc] sample real hrefs on page: {sample}")
                except Exception as e:
                    print(f"      [dxc] diagnostic read failed: {e}")
                stagnant, previous = 0, 0
                for _ in range(40):
                    _collect_verified_ireland_page_jobs(
                        page, "DXC Technology", r"careers\.dxc\.com/job/",
                        "dxc_browser", results, "Ireland")
                    for txt in ("Load more", "Show more", "See more", "Next"):
                        try:
                            b = page.get_by_role("button", name=txt, exact=False)
                            if b.count() and b.first.is_visible():
                                b.first.click(timeout=1000)
                                page.wait_for_timeout(400)
                        except Exception:
                            pass
                    page.mouse.wheel(0, 3000)
                    page.wait_for_timeout(350)
                    current = len(results)
                    stagnant = stagnant + 1 if current == previous else 0
                    previous = current
                    if stagnant >= 8:
                        break
            browser.close()
    except Exception as e:
        print(f"      [dxc] browser scrape failed: {e}")
    print(f"      [dxc] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_grant_thornton_direct(session):
    """Grant Thornton's original Workday tenant (iegt.wd3) has been part of
    the stuck-422 cluster all session and appears to no longer be their
    live hiring source — their current real careers pages are on their
    own site instead. Lightweight, no browser needed."""
    urls = [
        "https://www.grantthornton.ie/careers/",
        "https://www.grantthornton.ie/careers/experienced-hires/",
        "https://www.grantthornton.ie/careers/early-careers/",
    ]
    hints = ("/careers/", "/job/", "/jobs/", "vacanc", "opportunit",
             "experienced-hires", "graduate", "undergrad")
    blocked_titles = {
        "why grant thornton", "our benefits", "working at grant thornton",
        "careers", "experienced hires", "early careers",
        "graduate programme", "undergrad programme", "contact us",
    }
    results, seen = [], set()
    for url in urls:
        try:
            rows = _scrape_public_careers_page("Grant Thornton Ireland", url, hints, session, "Ireland")
        except Exception as e:
            print(f"      [grant-thornton] page failed {url}: {e}")
            continue
        for job in rows:
            title = (job.get("title") or "").strip()
            href = (job.get("url") or "").strip()
            if not title or not href or title.lower() in blocked_titles:
                continue
            key = href.split("?")[0].rstrip("/").lower()
            if key in seen:
                continue
            seen.add(key)
            results.append(job)
    print(f"      [grant-thornton] {len(results)} candidate Ireland opportunities")
    return results


def _browser_collect_job_links_with_retries(page, company_name, patterns, source_tag, results,
                                             default_location="Ireland", rounds=40, timeout_ms=45000):
    """Shared browser loop for proprietary career sites.  It keeps scrolling,
    follows visible load-more/next controls, and deduplicates individual job URLs.

    timeout_ms is now an ACTUAL hard wall-clock budget, not just an unused
    parameter — confirmed real bug: it was defined but never checked
    anywhere, meaning the only real bound was a round count, with no
    guarantee on how long each round actually took. A run went over 90
    minutes as a direct result. This is now enforced every round,
    regardless of internal state, matching the lesson from an earlier
    unbounded-loop incident this session (never trust round/iteration
    counts alone to bound real time)."""
    start_time = time.time()
    for _ in range(rounds):
        if (time.time() - start_time) * 1000 > timeout_ms:
            break
        before = len(results)
        _collect_browser_job_links(page, company_name, patterns, source_tag, results, default_location)
        for txt in ("Load more", "Show more", "See more", "Next", "View more"):
            if (time.time() - start_time) * 1000 > timeout_ms:
                break
            try:
                b = page.get_by_role("button", name=txt, exact=False)
                if b.count() and b.first.is_visible():
                    b.first.click(timeout=1500)
                    page.wait_for_timeout(700)
            except Exception:
                pass
        page.mouse.wheel(0, 5000)
        page.wait_for_timeout(500)
        if len(results) == before:
            # A second pass catches cards injected after the scroll.
            page.wait_for_timeout(700)
            _collect_browser_job_links(page, company_name, patterns, source_tag, results, default_location)
            if len(results) == before:
                break


def scrape_aon_ireland(session):
    """Aon now publishes live vacancies on jobs.aon.com.  The location index
    exposes Ireland/Dublin and individual postings use /jobs/<numeric-id>.
    Use the first-party location page and rendered pagination rather than the
    old generic ATS probing."""
    if not HAS_PLAYWRIGHT:
        print("      [aon] playwright not installed — skipping")
        return []
    urls = [
        "https://jobs.aon.com/?country=ie",
        "https://jobs.aon.com/jobs/locations?lang=en-US",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=30000)
                    page.wait_for_timeout(1800)
                    _browser_accept_consent(page)
                    # If this is the location index, click Ireland first.
                    for name in (r"^Ireland$", r"^Dublin$"):
                        try:
                            link = page.get_by_role("link", name=re.compile(name, re.I))
                            if link.count():
                                link.first.click(timeout=3000)
                                page.wait_for_timeout(1600)
                                break
                        except Exception:
                            pass
                    _browser_collect_job_links_with_retries(
                        page, "Aon", [r"jobs\.aon\.com/(?:jobs|signin/jobs|sign-up/jobs)/\d+"],
                        "aon_browser", results, "Ireland", rounds=35)
                except Exception as e:
                    print(f"      [aon] page failed {url}: {e}")
            browser.close()
    except Exception as e:
        print(f"      [aon] browser scrape failed: {e}")
    print(f"      [aon] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_eaton_ireland(session):
    """Eaton's public careers entry point is jobs.eaton.com.  The marketing
    site links into that applicant portal, so use a real browser, follow the
    Search Jobs entry point, search for Ireland/Dublin when possible, and
    verify Ireland on each rendered job card."""
    if not HAS_PLAYWRIGHT:
        print("      [eaton] playwright not installed — skipping")
        return []
    urls = [
        "https://jobs.eaton.com/",
        "https://www.eaton.com/ie/en-gb/company/careers.html",
        "https://www.eaton.com/ie/en-gb/company/careers/life-at-eaton/dublin.html",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=30000)
                    page.wait_for_timeout(1800)
                    _browser_accept_consent(page)
                    # Click the site's search/apply entry point if present.
                    for label in (r"Search jobs", r"Search and apply", r"Find Jobs", r"Search Careers"):
                        try:
                            el = page.get_by_role("link", name=re.compile(label, re.I))
                            if el.count():
                                href = el.first.get_attribute("href") or ""
                                if href:
                                    page.goto(urllib.parse.urljoin(page.url, href), wait_until="domcontentloaded", timeout=30000)
                                    page.wait_for_timeout(1500)
                                else:
                                    el.first.click(timeout=3000)
                                    page.wait_for_timeout(1500)
                                break
                        except Exception:
                            pass
                    # Best-effort location/search box.
                    for selector in ("input[placeholder*='Location' i]", "input[placeholder*='Search' i]", "input[type='search']"):
                        try:
                            inp = page.locator(selector)
                            if inp.count():
                                inp.first.fill("Ireland")
                                inp.first.press("Enter")
                                page.wait_for_timeout(1500)
                                break
                        except Exception:
                            pass
                    _browser_collect_job_links_with_retries(
                        page, "Eaton",
                        [r"jobs\.eaton\.com/[^#?]*(?:job|jobs)[^#?]*", r"jobs\.eaton\.com/[^#?]*\d{4,}"],
                        "eaton_browser", results, "Ireland", rounds=35)
                except Exception as e:
                    print(f"      [eaton] page failed {url}: {e}")
            browser.close()
    except Exception as e:
        print(f"      [eaton] browser scrape failed: {e}")
    print(f"      [eaton] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_nvidia_ireland(session):
    """NVIDIA has moved its public jobs experience to jobs.nvidia.com,
    powered by Eightfold.  Prefer the public Eightfold JSON feed and only
    fall back to the old Workday/browser path if that feed is unavailable.
    Never treat a login/recaptcha page as zero jobs."""
    results = {}
    # Public Eightfold feed used by the current jobs.nvidia.com experience.
    for start_at in range(0, 2000, 100):
        try:
            resp = session.get(
                "https://jobs.nvidia.com/api/apply/v2/jobs",
                params={"domain": "nvidia.com", "start": start_at, "num": 100, "query": "Ireland"},
                headers=HEADERS, timeout=20)
            if resp.status_code != 200:
                print(f"      [nvidia] Eightfold API HTTP {resp.status_code} at start={start_at}")
                break
            data = resp.json()
        except Exception as e:
            print(f"      [nvidia] Eightfold API unavailable: {e}")
            break
        positions = data.get("positions") or []
        if not positions:
            break
        before = len(results)
        for raw in positions:
            norm = normalize_eightfold_job("NVIDIA", "nvidia", raw)
            if norm:
                key = norm["url"].split("?")[0].rstrip("/").lower()
                results[key] = norm
        print(f"      [nvidia] Eightfold start={start_at}: +{len(results)-before} Ireland jobs ({len(results)} total)")
        if len(positions) < 100:
            break
    if results:
        return list(results.values())

    if not HAS_PLAYWRIGHT:
        print("      [nvidia] public Eightfold feed returned no usable Ireland jobs and playwright is not installed")
        return []

    # Browser fallback against the new public site.  A login/recaptcha page is
    # explicitly reported rather than converted into a false zero.
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://jobs.nvidia.com/careers", wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(2500)
            title = (page.title() or "").lower()
            body = _browser_text(page).lower()
            if any(x in title or x in body for x in ("sign in", "login", "recaptcha", "verify you are human")):
                print("      [nvidia] official jobs site is currently behind login/anti-bot verification; not reporting a false zero")
                browser.close()
                return []
            _browser_collect_job_links_with_retries(
                page, "NVIDIA", [r"jobs\.nvidia\.com/careers/job/\d+"],
                "nvidia_eightfold_browser", results, "Ireland", rounds=45)
            browser.close()
    except Exception as e:
        print(f"      [nvidia] browser fallback failed: {e}")
    print(f"      [nvidia] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())



def _scrape_public_careers_page(company_name, url, href_hints, session, default_location="Ireland"):
    """Conservative server-rendered careers-page parser for proprietary
    sites that don't need a browser — plain HTTP GET plus regex over the
    raw HTML. Only emits cards whose surrounding text clearly contains an
    Irish location, keeping bounded chunks around each anchor so one
    Ireland mention elsewhere on the page can't wrongly tag an unrelated
    role. This is a fallback technique, not a claim that every JS-only
    site is covered — for sites that need real JS execution, the
    Playwright-based scrapers elsewhere in this file are the right tool."""
    try:
        resp = session.get(url, headers=HEADERS, timeout=15)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []

    results, seen = [], set()
    for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', page, flags=re.I | re.S):
        href, label = m.group(1), _html_to_text(m.group(2))
        if not label or len(label) < 3 or len(label) > 220:
            continue
        full = urllib.parse.urljoin(url, href)
        low = full.lower()
        if not any(h in low for h in href_hints):
            continue
        start, end = max(0, m.start() - 1800), min(len(page), m.end() + 2600)
        chunk = _html_to_text(page[start:end])
        if not is_ireland_location(chunk):
            continue
        loc_match = re.search(
            r'((?:Dublin|Cork|Galway|Limerick|Waterford|Kilkenny|Athlone|Ireland)(?:[^|•<>]{0,80}))',
            chunk, flags=re.I)
        location = loc_match.group(1).strip()[:140] if loc_match else default_location
        key = (label.lower(), full.split("?")[0])
        if key in seen:
            continue
        seen.add(key)
        posted_text, posted_days = extract_posted_from_text(chunk)
        sponsorship, snippet = classify_sponsorship(chunk[:5000])
        results.append({
            "company": company_name,
            "title": label,
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, label),
            "url": full,
            "source": "direct_html",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        })
    return results


def scrape_oracle_candidate_experience(company_name, host, site_number, session, country_code="IE", max_pages=12):
    """Oracle Recruiting Cloud's public Candidate Experience UI is
    JavaScript-heavy, but its job search uses a real, public REST resource
    (recruitingCEJobRequisitions) underneath — confirmed working, not
    guessed. Used by JPMorgan Chase and Oracle itself, and likely other
    large enterprises on Oracle Cloud HCM."""
    base = host.rstrip("/")
    endpoint = base + "/hcmRestApi/resources/latest/recruitingCEJobRequisitions"
    results, seen = [], set()
    limit = 100

    for page in range(max_pages):
        offset = page * limit
        finder = (f"findReqs;siteNumber={site_number},"
                  f"workLocationCountryCode={country_code},limit={limit},offset={offset}")
        params = {"onlyData": "true", "expand": "requisitionList", "finder": finder}
        url = endpoint + "?" + urllib.parse.urlencode(params, safe=";,")
        try:
            resp = session.get(url, headers=HEADERS, timeout=15)
            if resp.status_code != 200:
                break
            data = resp.json()
        except Exception:
            break

        rows = []
        for item in data.get("items") or []:
            reqs = item.get("requisitionList")
            if isinstance(reqs, list):
                rows.extend(reqs)
            elif item.get("Title"):
                rows.append(item)
        if not rows:
            break

        for j in rows:
            title = str(j.get("Title") or j.get("title") or "").strip()
            location = str(j.get("PrimaryLocation") or j.get("Location") or j.get("location") or "").strip()
            country = str(j.get("PrimaryLocationCountry") or "").upper()
            if country not in {"IE", "IRL"} and not is_ireland_location(location):
                continue
            req_id = j.get("Id") or j.get("RequisitionId") or j.get("RequisitionNumber") or j.get("JobId")
            if not title or req_id is None:
                continue
            req_id = str(req_id)
            if req_id in seen:
                continue
            seen.add(req_id)
            job_url = f"{base}/hcmUI/CandidateExperience/en/sites/{site_number}/job/{urllib.parse.quote(req_id)}/"
            description = j.get("ShortDescriptionStr") or ""
            sponsorship, snippet = classify_sponsorship(description)
            posted_days = None
            posted_text = "Unknown"
            posted_raw = j.get("PostedDate") or j.get("PostingStartDate")
            if posted_raw:
                try:
                    posted_dt = datetime.fromisoformat(str(posted_raw).replace("Z", "+00:00"))
                    posted_days = (datetime.now(timezone.utc) - posted_dt).days
                    posted_text = f"Posted {posted_days} days ago" if posted_days > 0 else "Posted Today"
                except Exception:
                    pass
            results.append({
                "company": company_name,
                "title": title,
                "location": location or "Ireland",
                "posted_text": posted_text,
                "posted_days_ago": posted_days,
                "employment_type": normalize_employment_type(None, title),
                "url": job_url,
                "source": "oracle_cx",
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            })

        has_more = bool(data.get("hasMore"))
        if not has_more and len(rows) < limit:
            break
        time.sleep(0.2)

    return results


def scrape_jsonld_jobpostings(url, company_name, session):
    """Schema.org JobPosting is a real, standardized, machine-readable
    format — not a company-specific trick. Companies embed it directly in
    their career page HTML (as a <script type="application/ld+json">
    block) specifically so Google can show their jobs in search results.
    Since it's a genuine web standard rather than a guessed API, this can
    work across many different companies' own existing career page URLs,
    not just one company at a time. Handles a single JobPosting, a list
    of them, or an ItemList wrapping them — real pages use all three
    shapes depending on how they implemented it."""
    try:
        resp = session.get(url, headers=HEADERS, timeout=7)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []

    scripts = re.findall(r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
                          page, flags=re.I | re.S)
    if not scripts:
        return []

    def extract_postings(node):
        """JobPosting data can be a single dict, a list, or nested inside
        an ItemList's 'itemListElement' — walk all three shapes."""
        found = []
        if isinstance(node, list):
            for item in node:
                found.extend(extract_postings(item))
        elif isinstance(node, dict):
            node_type = node.get("@type", "")
            type_list = node_type if isinstance(node_type, list) else [node_type]
            if "JobPosting" in type_list:
                found.append(node)
            elif "itemListElement" in node:
                found.extend(extract_postings(node["itemListElement"]))
            elif "item" in node:
                found.extend(extract_postings(node["item"]))
        return found

    postings = []
    for raw_script in scripts:
        try:
            parsed = json.loads(raw_script.strip())
        except Exception:
            continue
        postings.extend(extract_postings(parsed))

    results = []
    seen_urls = set()
    for job in postings:
        location_obj = job.get("jobLocation") or {}
        if isinstance(location_obj, list):
            location_obj = location_obj[0] if location_obj else {}
        address = location_obj.get("address") or {}
        if isinstance(address, dict):
            location = ", ".join(filter(None, [
                address.get("addressLocality"), address.get("addressRegion"),
                address.get("addressCountry")]))
        else:
            location = str(address)
        if not location:
            location = _html_to_text(str(job.get("jobLocationType", "")))
        if not is_ireland_location(location):
            continue

        job_url = job.get("url") or job.get("sameAs") or url
        if job_url in seen_urls:
            continue
        seen_urls.add(job_url)

        description = _html_to_text(job.get("description", ""))
        sponsorship, snippet = classify_sponsorship(description[:5000])

        title = job.get("title", "").strip()
        results.append({
            "company": company_name,
            "title": title,
            "location": location,
            "posted_text": job.get("datePosted", "Unknown"),
            "posted_days_ago": None,
            "employment_type": normalize_employment_type(job.get("employmentType"), title),
            "url": job_url,
            "source": "jsonld",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        })
    return results


PROBE_VERSION = 18  # bump whenever a new ATS platform is added to the probe list, or slug guessing changes

# Deliberately SEPARATE from PROBE_VERSION — these two caches were sharing
# one version number, which meant every ATS-platform fix (Workable, etc.)
# was also silently wiping the entire JobPosting structured-data cache and
# forcing an expensive full 342-company recheck for something completely
# unrelated. Only bump this when the JSON-LD scraping logic itself changes.
JSONLD_CACHE_VERSION = 1


def probe_ats_for_manual_companies(manual_companies, session, cache_path, fetch_descriptions=True):
    """For companies with no known API (custom sites), try a few likely
    Greenhouse / Lever / SmartRecruiters / Ashby board slugs. If one hits,
    that company's Ireland jobs get pulled automatically from then on
    instead of needing a manual visit. Results (including 'no match found')
    are cached so repeat runs don't re-probe the same misses every 15 min.

    The cache is versioned: whenever a new platform is added to the probe
    list, companies previously cached as 'none' get automatically
    re-probed against the new platform too — otherwise they'd be stuck
    permanently skipped just because an older run tried fewer platforms.
    Confirmed real matches are never discarded, only re-checked misses."""
    cache = {}
    if os.path.exists(cache_path):
        with open(cache_path, encoding="utf-8") as f:
            raw = json.load(f)
        stored_version = raw.pop("__probe_version__", 1)
        cache = raw
        if stored_version != PROBE_VERSION:
            cache = {name: c for name, c in cache.items() if c.get("platform") != "none"}

    still_manual = []
    discovered_jobs = []
    known_platforms = ("greenhouse", "lever", "smartrecruiters", "ashby", "recruitee", "personio", "pinpoint", "eightfold", "phenom", "workable")
    cache_hits_matched, cache_hits_none, freshly_probed = 0, 0, 0

    for entry in manual_companies:
        name, url = entry["company"], entry["url"]
        cached = cache.get(name)

        if name == "Fenergo":
            print(f"=== FENERGO TRACE: cached entry = {cached} ===")

        if cached and cached.get("platform") in known_platforms:
            platform, slug = cached["platform"], cached["slug"]
            cache_hits_matched += 1
        elif cached and cached.get("platform") == "none":
            if name == "Fenergo":
                print("=== FENERGO TRACE: hit the 'none' cache branch — SKIPPED without re-probing. "
                      "This is the bug if it's still happening on a run that should include Workable. ===")
            still_manual.append(entry)
            cache_hits_none += 1
            continue
        else:
            if name == "Fenergo":
                print("=== FENERGO TRACE: no valid cache hit — proceeding to fresh probe now ===")
            freshly_probed += 1
            platform, slug = None, None
            if name in KNOWN_PHENOM_DOMAINS:
                known_domain, known_path = KNOWN_PHENOM_DOMAINS[name]
                ref_num, jobs_found = try_phenom_domain(known_domain, session, exact_path=known_path, verbose=False)
                if jobs_found:
                    platform, slug = "phenom", f"{known_domain}|{ref_num}"
            if platform is None and name in KNOWN_WORKABLE_SLUGS:
                known_slug = KNOWN_WORKABLE_SLUGS[name]
                if try_workable(known_slug, session) is not None:
                    platform, slug = "workable", known_slug
            if platform is None:
                for candidate in candidate_slugs(name):
                    if try_greenhouse(candidate, session) is not None:
                        platform, slug = "greenhouse", candidate
                        break
                    if try_lever(candidate, session) is not None:
                        platform, slug = "lever", candidate
                        break
                    if try_smartrecruiters_probe(candidate, session) is not None:
                        platform, slug = "smartrecruiters", candidate
                        break
                    if try_ashby(candidate, session) is not None:
                        platform, slug = "ashby", candidate
                        break
                    if try_recruitee(candidate, session) is not None:
                        platform, slug = "recruitee", candidate
                        break
                    if try_personio(candidate, session) is not None:
                        platform, slug = "personio", candidate
                        break
                    if try_pinpoint(candidate, session) is not None:
                        platform, slug = "pinpoint", candidate
                        break
                    if try_eightfold(candidate, session) is not None:
                        platform, slug = "eightfold", candidate
                        break
                    # NOTE: generic Workable guessing removed from this loop —
                    # confirmed via real trace evidence (Fenergo: 429 on every
                    # single candidate slug, every time) that Workable's shared
                    # API rate-limits us into uselessness at the scale of
                    # checking hundreds of companies. The retry-and-backoff
                    # was costing real time on every attempt without a single
                    # real success anywhere this session. Same treatment as
                    # Phenom: not worth running generically anymore.
                    # NOTE: generic Phenom guessing removed from this loop —
                    # across the entire session it never once succeeded,
                    # including on a URL confirmed to be genuine Phenom,
                    # while costing thousands of wasted requests per run
                    # (a major cause of a 2-hour runtime). The technique
                    # itself doesn't work via static fetch here, not just
                    # the slug guessing — not worth running on every
                    # candidate for every company anymore. Still checked,
                    # cheaply, via the exact-URL override above for the
                    # handful of companies verified by hand.
            cache[name] = {"platform": platform or "none", "slug": slug}
            if name == "Fenergo":
                print(f"=== FENERGO TRACE: fresh probe finished, result = platform={platform!r}, slug={slug!r} ===")
            if platform is None:
                still_manual.append(entry)
                continue

        # Fetch (or re-fetch) this company's postings.
        company_jobs = []
        if platform == "greenhouse":
            jobs = try_greenhouse(slug, session) or []
            for job in jobs:
                norm = normalize_greenhouse_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "lever":
            jobs = try_lever(slug, session) or []
            for job in jobs:
                norm = normalize_lever_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "smartrecruiters":
            jobs = try_smartrecruiters(slug, session) or []
            for job in jobs:
                norm = normalize_smartrecruiters_job(name, job, slug, session, fetch_descriptions)
                if norm:
                    company_jobs.append(norm)
        elif platform == "ashby":
            jobs = try_ashby(slug, session) or []
            for job in jobs:
                norm = normalize_ashby_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "recruitee":
            jobs = try_recruitee(slug, session) or []
            for job in jobs:
                norm = normalize_recruitee_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "personio":
            jobs = try_personio(slug, session) or []
            for job in jobs:
                norm = normalize_personio_job(name, slug, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "pinpoint":
            jobs = try_pinpoint(slug, session) or []
            for job in jobs:
                norm = normalize_pinpoint_job(name, slug, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "eightfold":
            jobs = try_eightfold(slug, session) or []
            for job in jobs:
                norm = normalize_eightfold_job(name, slug, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "phenom":
            domain, ref_num = slug.split("|", 1)
            jobs = fetch_phenom_jobs_by_refnum(domain, ref_num, session)
            for job in jobs:
                norm = normalize_phenom_job(name, domain, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "workable":
            jobs = try_workable(slug, session) or []
            for job in jobs:
                norm = normalize_workable_job(name, job)
                if norm:
                    company_jobs.append(norm)

        if company_jobs:
            discovered_jobs.extend(company_jobs)
        else:
            # Matched a platform, but no Ireland postings on it right now —
            # still needs to show up somewhere clickable, not vanish.
            still_manual.append({"company": name, "url": url,
                                  "platform": f"{platform} (no Ireland postings found right now)"})

    cache["__probe_version__"] = PROBE_VERSION
    with open(cache_path, "w", encoding="utf-8") as f:
        json.dump(cache, f, indent=2)

    print(f"  Cache summary: {cache_hits_matched} companies served from cache (confirmed platform), "
          f"{cache_hits_none} served from cache (confirmed no match), "
          f"{freshly_probed} freshly probed this run.")
    if freshly_probed > 50:
        print(f"  NOTE: {freshly_probed} freshly-probed companies is high — if this number stays "
              f"high on your NEXT run too (not just this one), the cache isn't persisting between "
              f"runs and that's the real runtime problem to chase next.")

    return discovered_jobs, still_manual


def load_companies(csv_path):
    with open(csv_path, newline="", encoding="utf-8-sig") as f:
        return list(csv.DictReader(f))


def load_official_permit_stats(path="official_permit_stats.json"):
    """Loads output of visa_stats.py (real DETE government data), if present."""
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    return {}


def load_adzuna_jobs(path="adzuna_jobs.json"):
    """Loads output of adzuna_fallback.py (aggregator-sourced jobs for
    companies with no direct ATS integration), if present. Structure:
    {company_name: [job_dict, ...]}."""
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    return {}


def notify_github_issue(new_jobs):
    """If running inside GitHub Actions, opens a GitHub Issue listing newly
    found jobs — GitHub's own free notification system (email/mobile push
    via your existing GitHub notification settings) then alerts you. No
    external service or API key needed beyond the Action's built-in token."""
    token = os.environ.get("GITHUB_TOKEN")
    repo = os.environ.get("GITHUB_REPOSITORY")  # "owner/repo", auto-set by Actions
    if not token or not repo or not new_jobs:
        return

    lines = [f"- **{j['company']}** — [{j['title']}]({j['url']}) ({j['location']})" for j in new_jobs]
    body = "New Ireland job postings found this run:\n\n" + "\n".join(lines)
    title = f"New job posting(s) - {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} ({len(new_jobs)})"

    try:
        resp = requests.post(
            f"https://api.github.com/repos/{repo}/issues",
            headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json"},
            json={"title": title, "body": body, "labels": ["new-jobs"]},
            timeout=15,
        )
        if resp.status_code >= 300:
            print(f"  GitHub issue notification failed: {resp.status_code} {resp.text[:200]}")
    except Exception as e:
        print(f"  GitHub issue notification failed: {e}")


def load_history(path):
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    return {}


def load_seen_jobs(path):
    """Tracks every job URL ever seen + when it was first seen, so we can
    flag which postings are new since the previous run."""
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    return {}


def mark_new_jobs(live_jobs, seen_jobs, now_iso):
    for job in live_jobs:
        url = job["url"]
        if url not in seen_jobs:
            seen_jobs[url] = now_iso
            job["new_since_last_check"] = True
            job["first_seen_at"] = now_iso
        else:
            job["new_since_last_check"] = False
            job["first_seen_at"] = seen_jobs[url]
    return seen_jobs


def update_history(history, live_jobs):
    for job in live_jobs:
        h = history.setdefault(job["company"], {"sponsors": 0, "no_sponsorship": 0, "not_mentioned": 0, "total": 0})
        h[job["visa_sponsorship"]] = h.get(job["visa_sponsorship"], 0) + 1
        h["total"] += 1
    return history


def sponsorship_rarity_label(h):
    """Returns {'label': str, 'category': str}. Crucially: silence is NOT the
    same as a 'no'. Most job postings never mention sponsorship either way —
    that's the default, expected, neutral case ('no_data'), and should never
    be shown to look like bad news. Only an postings that EXPLICITLY rule out
    sponsorship should read as a negative signal."""
    total = h.get("total", 0)
    sponsors = h.get("sponsors", 0)
    no_sponsorship = h.get("no_sponsorship", 0)

    if total < 5:
        return {"label": f"Not enough data yet ({total} scanned)", "category": "no_data"}

    if sponsors == 0 and no_sponsorship == 0:
        return {"label": f"No sponsorship info found ({total} postings scanned)", "category": "no_data"}

    if sponsors == 0 and no_sponsorship > 0:
        return {"label": f"Rules out sponsorship in {no_sponsorship} of {total} postings",
                "category": "explicit_negative"}

    ratio = sponsors / total
    if ratio < 0.10:
        return {"label": f"Rarely mentions sponsorship ({sponsors} of {total})", "category": "rare_positive"}
    if ratio < 0.40:
        return {"label": f"Occasionally mentions sponsorship ({sponsors} of {total})", "category": "occasional_positive"}
    return {"label": f"Frequently mentions sponsorship ({sponsors} of {total})", "category": "frequent_positive"}


def test_single_company(name):
    """Fast test mode for one company — skips the full ~30 min pipeline
    entirely. Checks known dedicated scrapers by name directly (Apple,
    Google, Amazon, Meta, EY, KPMG, TikTok, Boston Scientific, J&J,
    Johnson Controls, Microsoft, Citi, Red Hat), or falls back to trying it as a Workday tenant /
    generic ATS candidate using the company's row from the CSV."""
    print(f"=== Fast test mode: checking only '{name}' ===\n")
    session = requests.Session()
    name_lower = name.strip().lower()

    dedicated = {
        "apple": lambda: scrape_apple_ireland(session),
        "google": lambda: scrape_google_ireland(session),
        "amazon": lambda: scrape_amazon_ireland(session),
        "meta": lambda: scrape_meta_ireland(session),
        "ey": lambda: scrape_ey_ireland(session),
        "kpmg": lambda: scrape_kpmg_ireland(session),
        "tiktok": lambda: scrape_tiktok_ireland(session),
        "boston scientific": lambda: scrape_boston_scientific_ireland(session),
        "johnson & johnson": lambda: scrape_jnj_ireland(session),
        "johnson controls": lambda: scrape_johnson_controls_ireland(session),
        "hsbc": lambda: scrape_hsbc_ireland(session),
        "dxc": lambda: scrape_dxc_ireland(session),
        "grant thornton": lambda: scrape_grant_thornton_direct(session),
        "nvidia": lambda: scrape_nvidia_ireland(session),
        "aon": lambda: scrape_aon_ireland(session),
        "eaton": lambda: scrape_eaton_ireland(session),
        "microsoft": lambda: scrape_microsoft_ireland(session),
        "citi": lambda: scrape_citi_ireland(session),
        "red hat": lambda: scrape_red_hat_ireland(session),
        "oracle": lambda: scrape_oracle_candidate_experience("Oracle", "https://eeho.fa.us2.oraclecloud.com", "CX_1", session),
        "jpmorgan chase": lambda: scrape_oracle_candidate_experience("JPMorgan Chase", "https://jpmc.fa.oraclecloud.com", "CX_1001", session),
    }
    matched_key = next((k for k in dedicated if name_lower == k or name_lower.startswith(k)), None)

    if matched_key:
        print(f"Matched dedicated scraper: '{matched_key}'\n")
        jobs = dedicated[matched_key]()
        for j in jobs:
            normalize_posted_age(j)
        print(f"\n=== RESULT: {len(jobs)} Ireland postings found for '{name}' ===")
        for j in jobs[:10]:
            print(f"  - {j['title']} | {j['location']} | posted_days_ago={j['posted_days_ago']} | {j['url']}")
        if len(jobs) > 10:
            print(f"  ... and {len(jobs) - 10} more")
        return

    print(f"'{name}' isn't one of the dedicated scrapers — checking it as a "
          f"Workday/generic-ATS candidate from your CSV instead.\n")
    companies = load_companies("Job_Automation.csv")
    row = next((c for c in companies if c["company_name"].strip().lower() == name_lower), None)
    if not row:
        print(f"'{name}' not found in Job_Automation.csv (exact match required for this fallback path).")
        return

    url = row["career_url"].strip()
    if classify_url(url) == "workday":
        workday_session = make_workday_session()
        jobs, error = fetch_workday_jobs(row["company_name"], url, workday_session, fetch_descriptions=True)
        if error:
            print(f"Workday error: {error}")
        print(f"\n=== RESULT: {len(jobs)} Ireland postings found for '{name}' (Workday) ===")
        for j in jobs[:10]:
            print(f"  - {j['title']} | {j['location']} | {j['url']}")
        return

    for candidate in candidate_slugs(row["company_name"]):
        for try_fn, platform in ((try_greenhouse, "greenhouse"), (try_lever, "lever"),
                                  (try_smartrecruiters_probe, "smartrecruiters"), (try_ashby, "ashby")):
            result = try_fn(candidate, session)
            if result is not None:
                print(f"Matched '{platform}' with slug '{candidate}'.")
                print(f"(Re-run without --only to pull full job details through the normal pipeline.)")
                return
    print(f"No known platform matched for '{name}' — would land in manual-check.")


def main():
    print(f"=== job_pipeline.py running with PROBE_VERSION={PROBE_VERSION} "
          f"(should be 13 or higher — if this shows anything less, the uploaded "
          f"file is NOT the latest version) ===")
    print(f"=== Platforms supported: greenhouse, lever, smartrecruiters, ashby, "
          f"recruitee, personio, pinpoint, eightfold, phenom, workable ===")
    print(f"=== Dedicated company scrapers present: "
          f"dxc={('scrape_dxc_ireland' in globals())}, "
          f"grant_thornton={('scrape_grant_thornton_direct' in globals())}, "
          f"nvidia={('scrape_nvidia_ireland' in globals())} "
          f"(should all say True — if any say False, this upload is missing that code) ===")
    if os.path.exists("ats_platform_cache.json"):
        with open("ats_platform_cache.json", encoding="utf-8") as f:
            existing_cache = json.load(f)
        stored_v = existing_cache.get("__probe_version__", "MISSING")
        print(f"=== Existing ats_platform_cache.json found: stored __probe_version__={stored_v}, "
              f"{len(existing_cache)} total entries ===")
        if "Fenergo" in existing_cache:
            print(f"=== Fenergo cache entry BEFORE this run: {existing_cache['Fenergo']} ===")
        else:
            print(f"=== Fenergo has no cache entry yet (never probed) ===")
    else:
        print("=== No ats_platform_cache.json found yet — this will be a fully fresh run ===")

    ap = argparse.ArgumentParser()
    ap.add_argument("--input", default="Job_Automation.csv")
    ap.add_argument("--output", default="jobs.json")
    ap.add_argument("--history", default="sponsorship_history.json")
    ap.add_argument("--seen", default="seen_jobs.json")
    ap.add_argument("--no-descriptions", action="store_true",
                     help="Skip fetching full job descriptions (faster, but no visa sponsorship signal)")
    ap.add_argument("--only", default=None,
                     help="Test a single company by name (e.g. --only \"Johnson Controls\") "
                          "instead of running the full ~30 min pipeline. Prints results directly "
                          "and exits — does not write jobs.json or touch any cache files.")
    args = ap.parse_args()

    if args.only:
        test_single_company(args.only)
        return

    companies = load_companies(args.input)
    print(f"Loaded {len(companies)} companies from {args.input}")

    browser_cache = _load_browser_scrape_cache()
    fresh_count = sum(1 for v in browser_cache.values()
                       if (time.time() - v.get("checked_at", 0)) / 3600 < BROWSER_SCRAPE_MAX_AGE_HOURS)
    print(f"=== Browser-scrape cache: {len(browser_cache)} companies tracked, "
          f"{fresh_count} still fresh (within {BROWSER_SCRAPE_MAX_AGE_HOURS}h) and will be reused "
          f"instantly instead of re-launching a real browser this run ===")

    session = requests.Session()
    workday_session = make_workday_session()
    live_jobs, manual_check, errors = [], [], []

    for row in companies:
        name = row["company_name"].strip()
        url = row["career_url"].strip()
        kind = classify_url(url)

        if kind == "workday":
            print(f"  [workday] fetching {name} ...")
            jobs, err = fetch_workday_jobs(name, url, workday_session, fetch_descriptions=not args.no_descriptions)
            live_jobs.extend(jobs)
            if err:
                errors.append(err)
            print(f"      -> {len(jobs)} Ireland postings")
            time.sleep(1)  # spread out aggregate request rate across companies —
            # a shared CDN/WAF across Workday tenants can rate-limit based on
            # total volume from our IP, not just per-tenant.
            if not jobs:
                # Never let a company silently disappear — whether it's a
                # real fetch error or genuinely zero open Ireland roles
                # today, it still needs to show up somewhere clickable.
                reason = "fetch error, verify manually" if err else "no Ireland postings found right now"
                manual_check.append({"company": name, "url": url, "platform": f"workday ({reason})"})
        else:
            manual_check.append({"company": name, "url": url, "platform": kind})

    print(f"\nProbing remaining {len(manual_check)} companies for Greenhouse/Lever/SmartRecruiters/"
          f"Ashby/Recruitee/Personio/Pinpoint/Eightfold boards "
          f"(cached — only new/changed companies are actually re-probed)...")
    discovered_jobs, manual_check = probe_ats_for_manual_companies(
        manual_check, session, cache_path="ats_platform_cache.json",
        fetch_descriptions=not args.no_descriptions)
    if discovered_jobs:
        found_companies = sorted(set(j["company"] for j in discovered_jobs))
        print(f"  -> Auto-discovered {len(discovered_jobs)} Ireland postings across "
              f"{len(found_companies)} companies previously in the manual list: {', '.join(found_companies)}")
    live_jobs.extend(discovered_jobs)

    apple_entry = next((c for c in manual_check if c["company"].strip().lower().startswith("apple")), None)
    if apple_entry:
        print("\nTrying direct HTML scrape for Apple (no API/shared ATS, but their search "
              "page is server-rendered)...")
        apple_jobs = cached_browser_scrape(browser_cache, "Apple", lambda: scrape_apple_ireland(session), 180, "apple")
        if apple_jobs:
            print(f"  -> Apple: {len(apple_jobs)} Ireland postings found via direct scrape")
            for job in apple_jobs:
                job["company"] = apple_entry["company"]  # match the exact name used in the CSV
            live_jobs.extend(apple_jobs)
            manual_check = [c for c in manual_check if c is not apple_entry]
        else:
            print("  -> Apple: scrape ran but found nothing this time (page structure may "
                  "have changed, or genuinely zero current Ireland postings)")

    google_entry = next((c for c in manual_check if c["company"].strip().lower() == "google"), None)
    if google_entry:
        print("\nTrying Google via real browser automation (reads the actual rendered page — "
              "no API guessing, more resilient to backend changes than the two earlier attempts "
              "that guessed at a specific hidden endpoint and didn't work)...")
        google_jobs = cached_browser_scrape(browser_cache, "Google", lambda: scrape_google_ireland(session), 240, "google")
        if google_jobs:
            print(f"  -> Google: {len(google_jobs)} Ireland postings found")
            for job in google_jobs:
                job["company"] = google_entry["company"]
            live_jobs.extend(google_jobs)
            manual_check = [c for c in manual_check if c is not google_entry]
        else:
            print("  -> Google: found nothing this time")

    amazon_entry = next((c for c in manual_check if c["company"].strip().lower().startswith("amazon")), None)
    if amazon_entry:
        print("\nTrying Amazon's internal jobs search endpoint (no public API, but a real "
              "hidden JSON endpoint their own site uses — confirmed working, 197 real Ireland "
              "postings found when tested)...")
        amazon_jobs = cached_browser_scrape(browser_cache, "Amazon", lambda: scrape_amazon_ireland(session), 180, "amazon")
        if amazon_jobs:
            print(f"  -> Amazon: {len(amazon_jobs)} Ireland postings found")
            for job in amazon_jobs:
                job["company"] = amazon_entry["company"]
            live_jobs.extend(amazon_jobs)
            manual_check = [c for c in manual_check if c is not amazon_entry]
        else:
            print("  -> Amazon: found nothing this time")

    meta_entry = next((c for c in manual_check if c["company"].strip().lower().startswith("meta")), None)
    if meta_entry:
        print("\nTrying Meta via real browser automation (same technique as Google — reads the "
              "actual rendered page rather than replicating their internal GraphQL contract, "
              "which is more resilient if that contract changes)...")
        meta_jobs = cached_browser_scrape(browser_cache, "Meta", lambda: scrape_meta_ireland(session), 240, "meta")
        if meta_jobs:
            print(f"  -> Meta: {len(meta_jobs)} Ireland postings found")
            for job in meta_jobs:
                job["company"] = meta_entry["company"]
            live_jobs.extend(meta_jobs)
            manual_check = [c for c in manual_check if c is not meta_entry]
        else:
            print("  -> Meta: found nothing this time (browser automation failed, or genuinely "
                  "zero current Ireland postings)")

    browser_targets = [
        ("ey", scrape_ey_ireland, "EY (SuccessFactors — no free API, but browser automation "
                                    "doesn't need one, it just reads the page)"),
        ("kpmg", scrape_kpmg_ireland, "KPMG (Avature — same story as EY)"),
        ("tiktok", scrape_tiktok_ireland, "TikTok (moved to a searchable board since last checked)"),
    ]
    for prefix, scraper_fn, description in browser_targets:
        entry = next((c for c in manual_check if c["company"].strip().lower().startswith(prefix)), None)
        if not entry:
            continue
        print(f"\nTrying {entry['company']} via real browser automation — {description}...")
        found_jobs = cached_browser_scrape(browser_cache, entry["company"], lambda: scraper_fn(session), 240, entry["company"])
        if found_jobs:
            print(f"  -> {entry['company']}: {len(found_jobs)} Ireland postings found")
            for job in found_jobs:
                job["company"] = entry["company"]
            live_jobs.extend(found_jobs)
            manual_check = [c for c in manual_check if c is not entry]
        else:
            print(f"  -> {entry['company']}: found nothing this time")

    # Exact-name matching here, not prefix — "Johnson Controls" and
    # "Johnson & Johnson" share a prefix, as do "Boston Scientific" and
    # "Boston Consulting Group (BCG)". A prefix match would risk running
    # the wrong company's scraper against the wrong CSV entry.
    exact_browser_targets = [
        ("boston scientific", scrape_boston_scientific_ireland, "Boston Scientific (SuccessFactors, office-specific pages)"),
        ("johnson & johnson", scrape_jnj_ireland, "Johnson & Johnson (first-party board)"),
        ("johnson controls", scrape_johnson_controls_ireland, "Johnson Controls (Algolia-style board)"),
        ("hsbc ireland", scrape_hsbc_ireland, "HSBC Ireland (SuccessFactors, same technique as EY)"),
        ("dxc technology", scrape_dxc_ireland, "DXC Technology (bypasses its stuck Workday tenant)"),
        ("grant thornton ireland", scrape_grant_thornton_direct, "Grant Thornton (their real current careers site, not the stuck Workday tenant)"),
        ("nvidia", scrape_nvidia_ireland, "NVIDIA (public Eightfold feed, same platform as Netflix — falls back to a browser check that honestly reports a sign-in wall instead of a false zero)"),
        ("aon", scrape_aon_ireland, "Aon (first-party jobs.aon.com, bypasses their stuck Workday tenant)"),
        ("eaton", scrape_eaton_ireland, "Eaton (first-party jobs.eaton.com applicant portal, bypasses their stuck Workday tenant)"),
    ]
    for exact_name, scraper_fn, description in exact_browser_targets:
        entry = next((c for c in manual_check if c["company"].strip().lower() == exact_name), None)
        if not entry:
            continue
        print(f"\nTrying {entry['company']} via real browser automation — {description}...")
        found_jobs = cached_browser_scrape(browser_cache, entry["company"], lambda: scraper_fn(session), 240, entry["company"])
        if found_jobs:
            print(f"  -> {entry['company']}: {len(found_jobs)} Ireland postings found")
            for job in found_jobs:
                job["company"] = entry["company"]
            live_jobs.extend(found_jobs)
            manual_check = [c for c in manual_check if c is not entry]
        else:
            print(f"  -> {entry['company']}: found nothing this time")

    # Dedicated browser scrapers for companies whose public pages are dynamic
    # or paginated. These run before the generic HTML fallback so counts are
    # based on the rendered first-party job listings rather than partial HTML.
    special_browser_targets = [
        ("microsoft", scrape_microsoft_ireland, "Microsoft Dublin/Ireland rendered careers search"),
        ("citi", scrape_citi_ireland, "Citi Dublin paginated careers search"),
        ("red hat", scrape_red_hat_ireland, "Red Hat rendered Ireland careers search"),
    ]
    for exact_name, scraper_fn, description in special_browser_targets:
        entry = next((c for c in manual_check if c["company"].strip().lower() == exact_name), None)
        if not entry:
            continue
        print(f"\nTrying {entry['company']} via dedicated browser automation — {description}...")
        found_jobs = cached_browser_scrape(browser_cache, entry["company"], lambda: scraper_fn(session), 240, entry["company"])
        if found_jobs:
            print(f"  -> {entry['company']}: {len(found_jobs)} Ireland postings found")
            for job in found_jobs:
                job["company"] = entry["company"]
            live_jobs.extend(found_jobs)
            manual_check = [c for c in manual_check if c is not entry]
        else:
            print(f"  -> {entry['company']}: found nothing this time")

    netflix_entry = next((c for c in manual_check if c["company"].strip().lower() == "netflix"), None)
    if netflix_entry:
        print("\nTrying Netflix (Eightfold, custom-branded domain, confirmed working endpoint)...")
        netflix_jobs = cached_browser_scrape(browser_cache, "Netflix", lambda: scrape_netflix_ireland(session), 120, "netflix")
        if netflix_jobs:
            print(f"  -> Netflix: {len(netflix_jobs)} Ireland postings found")
            for job in netflix_jobs:
                job["company"] = netflix_entry["company"]
            live_jobs.extend(netflix_jobs)
            manual_check = [c for c in manual_check if c is not netflix_entry]
        else:
            print("  -> Netflix: found nothing this time")

    # Lightweight, pure-requests scraper (no browser needed) — real hint
    # patterns and URLs confirmed via a working reference, not guessed.
    direct_html_targets = []  # handled above by dedicated browser scrapers
    for exact_name, display_name, urls, hints, default_loc in direct_html_targets:
        entry = next((c for c in manual_check if c["company"].strip().lower() == exact_name), None)
        if not entry:
            continue
        print(f"\nTrying {display_name} via direct HTML scrape (no browser needed)...")
        found = {}
        for u in urls:
            for job in _scrape_public_careers_page(display_name, u, hints, session, default_loc):
                key = job["url"].split("?")[0].rstrip("/").lower()
                found[key] = job
        found_jobs = list(found.values())
        if display_name == "Red Hat":
            blocked = {"locations", "departments", "life at red hat", "hiring process", "info guide", "students", "benefits"}
            found_jobs = [j for j in found_jobs if j["title"].strip().lower() not in blocked]
        if found_jobs:
            print(f"  -> {entry['company']}: {len(found_jobs)} Ireland postings found")
            for job in found_jobs:
                job["company"] = entry["company"]
            live_jobs.extend(found_jobs)
            manual_check = [c for c in manual_check if c is not entry]
        else:
            print(f"  -> {entry['company']}: found nothing this time")

    # Oracle Candidate Experience REST API — real, public, confirmed working.
    oracle_cx_targets = [
        ("jpmorgan chase", "JPMorgan Chase", "https://jpmc.fa.oraclecloud.com", "CX_1001"),
        ("oracle", "Oracle", "https://eeho.fa.us2.oraclecloud.com", "CX_1"),
    ]
    for exact_name, display_name, host, site_number in oracle_cx_targets:
        entry = next((c for c in manual_check if c["company"].strip().lower() == exact_name), None)
        if not entry:
            continue
        print(f"\nTrying {display_name} via Oracle Recruiting Cloud's public REST API...")
        found_jobs = cached_browser_scrape(
            browser_cache, display_name,
            lambda: scrape_oracle_candidate_experience(display_name, host, site_number, session),
            180, display_name)
        if found_jobs:
            print(f"  -> {entry['company']}: {len(found_jobs)} Ireland postings found")
            for job in found_jobs:
                job["company"] = entry["company"]
            live_jobs.extend(found_jobs)
            manual_check = [c for c in manual_check if c is not entry]
        else:
            print(f"  -> {entry['company']}: found nothing this time")

    jsonld_cache_path = "jsonld_cache.json"
    jsonld_cache = {}
    if os.path.exists(jsonld_cache_path):
        with open(jsonld_cache_path, encoding="utf-8") as f:
            jsonld_cache = json.load(f)
    jsonld_cache_version = jsonld_cache.pop("__version__", 0)
    if jsonld_cache_version != JSONLD_CACHE_VERSION:
        # Version changed — only clear the "no data found" verdicts so they
        # get a fresh chance; keep confirmed "has JobPosting data" hits as-is.
        jsonld_cache = {k: v for k, v in jsonld_cache.items() if v.get("has_data")}

    print(f"\nChecking remaining manual companies for embedded JobPosting structured data on "
          f"their own career page (a real, standardized SEO format many companies use — not "
          f"every company implements it, and results are cached so this only costs real time "
          f"once per company, not every run)...")
    jsonld_found_companies = []
    still_manual_after_jsonld = []
    jsonld_checked_this_run = 0
    for entry in manual_check:
        name = entry["company"]
        cached = jsonld_cache.get(name)
        if cached is not None:
            if cached.get("has_data"):
                # Confirmed source before — re-fetch fresh job data (jobs change),
                # but skip re-checking whether the page has JobPosting markup at all.
                jsonld_jobs = scrape_jsonld_jobpostings(entry["url"], name, session)
                if jsonld_jobs:
                    live_jobs.extend(jsonld_jobs)
                    jsonld_found_companies.append(name)
                else:
                    still_manual_after_jsonld.append(entry)
            else:
                still_manual_after_jsonld.append(entry)
            continue

        if not entry.get("url"):
            still_manual_after_jsonld.append(entry)
            jsonld_cache[name] = {"has_data": False}
            continue

        jsonld_checked_this_run += 1
        jsonld_jobs = scrape_jsonld_jobpostings(entry["url"], name, session)
        if jsonld_jobs:
            live_jobs.extend(jsonld_jobs)
            jsonld_found_companies.append(name)
            jsonld_cache[name] = {"has_data": True}
        else:
            still_manual_after_jsonld.append(entry)
            jsonld_cache[name] = {"has_data": False}
        time.sleep(0.2)

    manual_check = still_manual_after_jsonld
    jsonld_cache["__version__"] = JSONLD_CACHE_VERSION
    with open(jsonld_cache_path, "w", encoding="utf-8") as f:
        json.dump(jsonld_cache, f, indent=2)
    print(f"  Checked {jsonld_checked_this_run} companies fresh this run (rest served from cache).")
    if jsonld_found_companies:
        print(f"  -> JobPosting structured data found for {len(jsonld_found_companies)} companies: "
              f"{', '.join(jsonld_found_companies)}")
    else:
        print("  -> No companies had usable JobPosting structured data this run")

    adzuna_jobs = load_adzuna_jobs()
    if adzuna_jobs:
        adzuna_flat = [job for jobs in adzuna_jobs.values() for job in jobs]
        adzuna_companies = set(adzuna_jobs.keys())
        live_jobs.extend(adzuna_flat)
        manual_check = [c for c in manual_check if c["company"] not in adzuna_companies]
        print(f"  -> Merged {len(adzuna_flat)} Adzuna-sourced postings across "
              f"{len(adzuna_companies)} companies (run adzuna_fallback.py separately, daily, to refresh this).")

    history = load_history(args.history)
    history = update_history(history, live_jobs)
    with open(args.history, "w", encoding="utf-8") as f:
        json.dump(history, f, indent=2)

    now_iso = datetime.now(timezone.utc).isoformat()
    seen_jobs = load_seen_jobs(args.seen)
    seen_jobs = mark_new_jobs(live_jobs, seen_jobs, now_iso)
    with open(args.seen, "w", encoding="utf-8") as f:
        json.dump(seen_jobs, f, indent=2)
    new_count = sum(1 for j in live_jobs if j["new_since_last_check"])

    company_sponsorship_stats = {
        company: {**h, **sponsorship_rarity_label(h)}
        for company, h in history.items()
    }

    official_permit_stats = load_official_permit_stats()
    if official_permit_stats:
        print(f"Merged official DETE permit records for {len(official_permit_stats)} companies "
              f"(run visa_stats.py separately, monthly, to refresh this).")

    # Normalize posted age for EVERY source before writing jobs.json. Time
    # filtering stays cumulative exactly as the dashboard expects: 24 hours
    # (<=1 day), 7 days (<=7), 28 days (<=28), Any time (no restriction).
    # Unknown dates become the 9999 sentinel instead of null so they can't
    # be misclassified as recent — they still appear when "Any time" is
    # selected, since that option applies no age condition at all.
    for job in live_jobs:
        normalize_posted_age(job)

    with open(BROWSER_SCRAPE_CACHE_PATH, "w", encoding="utf-8") as f:
        json.dump(browser_cache, f, indent=2, ensure_ascii=False)

    output = {
        "generated_at": now_iso,
        "live_jobs": live_jobs,
        "manual_check_companies": manual_check,
        "company_sponsorship_stats": company_sponsorship_stats,
        "official_permit_stats": official_permit_stats,
        "errors": errors,
        "stats": {
            "total_companies": len(companies),
            "automated_companies": len(companies) - len(manual_check),
            "manual_companies": len(manual_check),
            "live_jobs_found": len(live_jobs),
            "new_since_last_check": new_count,
        },
    }

    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    new_jobs = [j for j in live_jobs if j["new_since_last_check"]]
    notify_github_issue(new_jobs)

    print(f"\nDone. {len(live_jobs)} live Ireland job postings written to {args.output}")
    print(f"{new_count} of those are NEW since the last run (see seen_jobs.json).")
    print(f"Sponsorship history (cumulative across all runs) saved to {args.history}")
    print(f"{len(manual_check)} companies need manual checking — still listed in the dashboard's directory tab.")
    if errors:
        print(f"{len(errors)} companies had fetch errors — see 'errors' in {args.output}")


if __name__ == "__main__":
    main()
