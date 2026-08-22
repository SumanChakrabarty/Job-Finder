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
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError as FuturesTimeoutError
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


BROWSER_SCRAPE_CACHE_PATH = "browser_scrape_cache.json"
BROWSER_SCRAPE_MAX_AGE_HOURS = 3  # only actually re-run a real browser scrape this often
EMPTY_RESULT_MAX_AGE_HOURS = 0.5  # empty results retried much sooner — could be a real "no jobs",
# or could be a one-time failure (crash, resource contention); don't lock in a failure for 3 hours
PARALLEL_WORKERS = int(os.environ.get("SCRAPE_WORKERS", "10"))  # conservative — GitHub Actions'
# free-tier runners have limited CPU/memory (~2 cores, 7GB RAM); too many simultaneous real
# Chrome instances can crash or silently fail


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
    a browser when the cache is missing or stale.

    Empty results get a much shorter cache lifetime than real ones — a
    genuine "no current openings" is one thing, but an empty result could
    just as easily mean the browser crashed or got resource-starved this
    one time. Only a confirmed, real (non-empty) result earns the long
    cache duration."""
    entry = cache.get(company_key)
    if entry:
        age_hours = (time.time() - entry.get("checked_at", 0)) / 3600
        had_jobs = bool(entry.get("jobs"))
        max_age = BROWSER_SCRAPE_MAX_AGE_HOURS if had_jobs else EMPTY_RESULT_MAX_AGE_HOURS
        if age_hours < max_age:
            jobs = entry.get("jobs", [])
            print(f"      [{label}] using cached result from {age_hours:.1f}h ago "
                  f"({len(jobs)} jobs) — next real check in {max_age - age_hours:.1f}h")
            return jobs

    jobs = scraper_fn()  # timeout enforced by the caller (future.result(timeout=X)),
    # not signal.alarm() — that only works in the main thread and crashed
    # every dedicated company the first time this ran in parallel.
    prior_failures = (cache.get(company_key) or {}).get("consecutive_failures", 0)
    new_failures = 0 if jobs else prior_failures + 1
    cache[company_key] = {"jobs": jobs, "checked_at": time.time(), "consecutive_failures": new_failures}
    return jobs


def effective_timeout(cache, company_key, base_timeout):
    """A company that has failed several cycles in a row is unlikely to
    suddenly succeed this run — but still deserves periodic full-length
    attempts in case a real fix actually resolves it. Shrinks the budget
    progressively for repeat failures, with a floor so it's never fully
    abandoned, and resets to full trust immediately the moment a company
    succeeds again."""
    failures = (cache.get(company_key) or {}).get("consecutive_failures", 0)
    if failures <= 1:
        return base_timeout
    elif failures <= 3:
        return max(45, int(base_timeout * 0.5))
    else:
        return max(30, int(base_timeout * 0.25))


def run_company_tasks_in_parallel(tasks, workers=None):
    """Runs company scrapers concurrently instead of one at a time — the
    real fix for a multi-hour runtime. Each task is (label, company_name,
    callable, timeout_seconds).

    Timeout is enforced via future.result(timeout=X) — the thread-safe
    way to do this. signal.alarm() (the previous mechanism, used
    elsewhere in an earlier version of this file) ONLY works in the main
    thread and crashed every single dedicated company the moment this ran
    in worker threads instead — confirmed via a real run where all 44
    companies failed with the identical error, and confirmed fixed here
    via a direct side-by-side reproduction test before shipping.

    Critical follow-up bug, also confirmed via a real run: giving up on a
    slow task via future.result(timeout=X) does NOT stop its underlying
    thread — that thread keeps running in the background. Using
    ThreadPoolExecutor as a context manager (`with ... as pool:`) shuts
    the pool down on exit with wait=True by default, which BLOCKS THE
    WHOLE PROGRAM until every background thread actually finishes — even
    ones already reported as timed out. A real run hit exactly this: DXC
    correctly printed "HARD TIMEOUT after 240s", but the pipeline then
    silently hung for 10+ minutes waiting for DXC's still-running browser
    task to actually complete before the pool would let the program move
    on. Explicitly shutting down with wait=False avoids this — any
    genuinely stuck background thread is abandoned (Python has no clean
    way to force-kill a thread) rather than blocking everything else."""
    results, errors = [], []
    if not tasks:
        return results, errors
    pool = ThreadPoolExecutor(max_workers=workers or PARALLEL_WORKERS)
    try:
        future_map = {pool.submit(fn): (label, company, timeout_s) for label, company, fn, timeout_s in tasks}
        start_time = time.time()
        deadlines = {fut: start_time + timeout_s for fut, (_, _, timeout_s) in future_map.items()}
        pending = set(future_map)
        # Report in TRUE completion order, not submission order — a task
        # near the front of the list that happens to be slow (DXC, in a
        # real run) was blocking the reported results of faster companies
        # that had already quietly finished behind it. Real work was
        # already parallel; only the reporting order was misleading.
        #
        # BUG FIXED HERE, confirmed via direct test: an earlier version of
        # this fix used one shared overall timeout (the longest individual
        # value in the batch) instead of each task's own specific budget —
        # a company meant to give up after 60s could run the full 240s
        # instead, since nothing enforced its own shorter deadline anymore.
        # Poll in short intervals and check each still-pending task against
        # its OWN deadline, not just one shared ceiling.
        while pending:
            now = time.time()
            soonest_deadline = min(deadlines[f] for f in pending)
            poll_window = max(0.1, min(soonest_deadline - now, 5.0))
            try:
                for fut in as_completed(pending, timeout=poll_window):
                    pending.discard(fut)
                    label, company, timeout_s = future_map[fut]
                    try:
                        jobs = fut.result() or []
                        if jobs:
                            print(f"  -> {company}: {len(jobs)} Ireland postings found")
                        else:
                            print(f"  -> {company}: found nothing this time")
                        results.append((company, jobs))
                    except Exception as exc:
                        print(f"  -> {company}: task failed ({exc})")
                        errors.append(f"{label}/{company}: {exc}")
            except FuturesTimeoutError:
                pass  # normal — just means nothing finished within this poll window
            # Anything still pending whose OWN deadline has now passed is
            # reported as timed out, even if the shared poll loop continues
            # for other tasks with a later deadline.
            now = time.time()
            timed_out_now = [f for f in pending if deadlines[f] <= now]
            for fut in timed_out_now:
                pending.discard(fut)
                label, company, timeout_s = future_map[fut]
                print(f"  -> {company}: HARD TIMEOUT after {timeout_s}s "
                      f"(pipeline continues normally with whatever else it already found)")
                errors.append(f"{label}/{company}: timed out after {timeout_s}s")
    finally:
        pool.shutdown(wait=False)
    return results, errors


def parse_posted_text(posted_text: str):
    if not posted_text:
        return None
    t = posted_text.lower()
    # Try a real, exact date first — a raw ISO date, or a bare "DD Mon
    # YYYY" (confirmed real format from ESB's listings, e.g. "19 Aug
    # 2026", with no preceding keyword like "posted") would otherwise
    # silently fall through every check below and return None.
    try:
        parsed = datetime.fromisoformat(str(posted_text).replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=timezone.utc)
        days = (datetime.now(timezone.utc) - parsed).days
        return max(0, days)
    except (ValueError, TypeError):
        pass
    dm = re.search(r"\b(\d{1,2})\s+([A-Za-z]{3,9})\s+(\d{4})\b", str(posted_text))
    if dm:
        try:
            parsed = datetime.strptime(f"{dm.group(1)} {dm.group(2)[:3]} {dm.group(3)}", "%d %b %Y")
            days = (datetime.now(timezone.utc).replace(tzinfo=None) - parsed).days
            return max(0, days)
        except ValueError:
            pass
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
        r"\b\d{1,2}\s+[A-Za-z]{3,9}\s+\d{4}\b",
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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



def scrape_priority_sheet2_generic(company_name, url, session=None):
    """Generic Ireland-first browser fallback for selected high-priority companies
    from the user's Sheet 2. It does not change the existing company/platform
    scrapers; it only adds a fallback path for companies that otherwise remain
    manual. The page is rendered in an Ireland locale, job-looking links are
    collected from the rendered page, and only cards/details with an Ireland
    signal are emitted."""
    if not HAS_PLAYWRIGHT:
        print(f"      [priority-generic] {company_name}: Playwright not installed")
        return []

    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(
                viewport={"width": 1440, "height": 1000},
                locale="en-IE",
                timezone_id="Europe/Dublin",
            )
            page.goto(url, wait_until="domcontentloaded", timeout=45000)
            page.wait_for_timeout(1800)

            # Dismiss common consent banners without assuming a specific vendor.
            for consent_text in (
                "Accept all", "Accept All", "I agree", "I Agree",
                "Accept", "Allow all", "Allow All", "Got it", "OK",
            ):
                try:
                    btn = page.get_by_role("button", name=consent_text, exact=False)
                    if btn.count():
                        btn.first.click(timeout=1500)
                        page.wait_for_timeout(600)
                        break
                except Exception:
                    pass

            # Let lazy-loaded career results appear, but keep this bounded.
            last_count = -1
            stable = 0
            for _ in range(10):
                try:
                    count = page.locator("a[href]").count()
                except Exception:
                    count = 0
                if count == last_count:
                    stable += 1
                else:
                    stable = 0
                last_count = count
                if stable >= 2:
                    break
                page.mouse.wheel(0, 4500)
                page.wait_for_timeout(700)

            anchors = page.locator("a[href]")
            jobish = re.compile(
                r"(job|jobs|career|careers|vacanc|position|opening|opportunit|requisition|"
                r"apply|jobdetail|job-detail|jobdetailpage|searchresult|jobposting|"
                r"employment|talent)",
                re.I,
            )

            seen = set()
            candidate_count = 0
            for i in range(min(anchors.count(), 5000)):
                a = anchors.nth(i)
                try:
                    raw = a.get_attribute("href") or ""
                    href = urllib.parse.urljoin(page.url, raw).split("#")[0]
                    text = _browser_text(a)
                except Exception:
                    continue
                if not href or href in seen or href.startswith(("mailto:", "tel:", "javascript:")):
                    continue
                if not jobish.search(href) and not jobish.search(text):
                    continue
                # Skip obvious navigation/account/social links.
                if re.search(r"/(login|signin|register|account|privacy|terms|contact|about)(?:/|$)", href, re.I):
                    continue

                card = _browser_card(a)
                if not card:
                    card = text

                ireland = is_ireland_location(card)
                # If the page itself is explicitly Ireland-filtered, trust that
                # page-level signal when the card hides the location.
                page_text = _browser_text(page.locator("body"))[:12000]
                ireland_page = bool(re.search(r"\b(Ireland|Dublin|Cork|Galway|Limerick)\b", page_text, re.I))
                if not ireland and not ireland_page:
                    continue

                title = text.strip()
                if not title or len(title) > 300 or jobish.search(title):
                    lines = [x.strip() for x in card.splitlines() if x.strip()]
                    title = next(
                        (x for x in lines if 4 <= len(x) <= 180 and not is_ireland_location(x)
                         and not re.search(r"^(apply|view|learn more|read more)$", x, re.I)),
                        "",
                    )
                if not title:
                    continue

                seen.add(href)
                candidate_count += 1
                posted_text, posted_days = extract_posted_from_text(card)
                sponsorship, snippet = classify_sponsorship(card[:5000])
                location = _extract_location_from_card(card, "Ireland")
                results[href.rstrip("/").lower()] = {
                    "company": company_name,
                    "title": title[:300],
                    "location": location,
                    "posted_text": posted_text,
                    "posted_days_ago": posted_days,
                    "employment_type": normalize_employment_type(None, title),
                    "url": href,
                    "source": "priority_sheet2_generic",
                    "visa_sponsorship": sponsorship,
                    "visa_snippet": snippet,
                }

                if len(results) >= 80:
                    break

            print(f"      [priority-generic] {company_name}: {len(results)} Ireland candidates "
                  f"from {candidate_count} job-like links")
            browser.close()
    except Exception as e:
        print(f"      [priority-generic] {company_name} failed: {e}")
    return list(results.values())


def _extract_location_from_card(card_text, default="Ireland"):
    """Best-effort location extraction for already location-filtered career
    pages. Important: Google/Meta virtualized result cards do not always
    expose the location text in the same DOM subtree as the title/link.
    Because the page itself is explicitly filtered to Ireland, lack of
    visible location text is NOT a reason to discard the posting — this
    was the actual bug that made real Meta postings disappear (location
    hidden behind a collapsed '+N locations' control). Prefers a specific
    city when visible, otherwise safely falls back to the default.

    Real evidence (Avolon, AMCS, Auxilion, BioMarin) showed this returning
    huge blobs of raw CSS/JavaScript/JSON-LD as "location" — the original
    version returned a whole matching LINE unconditionally, which is fine
    for genuinely multi-line input but breaks badly once a caller has
    already collapsed everything to one giant line (common in newer
    functions that whitespace-normalize card text first). Now caps how
    much of a match is ever returned, and prefers a narrow "City, Ireland"
    -style substring over the raw line whenever the line looks suspiciously
    long to be a real location on its own."""
    lines = [x.strip() for x in (card_text or "").splitlines() if x.strip()]
    # Whitelist-based match, not "any capitalized word before the comma" —
    # that looser version still occasionally grabbed an adjacent word from
    # surrounding junk text (confirmed via direct test). Irish city names
    # are essentially all single-word, so no real need to risk it.
    city_pattern = re.compile(
        r"\b(Dublin|Cork|Galway|Limerick|Waterford|Kilkenny|Kildare|Athlone|"
        r"Sligo|Wexford|Wicklow|Drogheda|Dundalk|Bray|Navan|Ennis|Tralee|"
        r"Carlow|Naas|Athy|Portlaoise|Mullingar|Letterkenny)\s*,\s*"
        r"(?:Co\.?\s*)?(?:Ireland|IE)\b", re.I)
    ireland_word = re.compile(r"\bIreland\b", re.I)
    for line in lines:
        if not is_ireland_location(line):
            continue
        if len(line) <= 60:
            return line[:180]
        # The line technically contains an Ireland keyword but is far too
        # long to genuinely just be a location — look for a narrow,
        # bounded match inside it instead of returning the whole thing.
        m = city_pattern.search(line)
        if m:
            return f"{m.group(1).title()}, Ireland"
        m2 = ireland_word.search(line)
        if m2:
            return "Ireland"
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
    """Real evidence (a genuinely different, working reference) showed
    KPMG's live board is under /experiencedhires/, not /careers/ — and
    that individual pre-filtered category URLs (reverse-engineered facet
    IDs) return real results directly, unlike a blank search + clicking
    Search on the /careers/ path, which kept returning "No jobs found."
    Job links use /FolderDetail/ specifically. Belfast/Northern Ireland
    roles are explicitly excluded, since Avature can mix them into the
    same experienced-hire search.

    Speed: the first URL (folderOffset=0, no category filter) is the
    comprehensive "all jobs" view — the other 6 are just category-specific
    subsets of that same pool. Checking all 7 unconditionally roughly 7x'd
    this company's real cost for likely-redundant results. Try the
    comprehensive one first; only fall back to the category-specific URLs
    if it comes back thin, rather than always checking all 7."""
    if not HAS_PLAYWRIGHT:
        print("      [kpmg] playwright not installed — skipping")
        return []
    all_source_urls = [
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?folderOffset=0",
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?3_33_3=91",
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?3_33_3=92",
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?3_33_3=93",
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?3_33_3=95",
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?3_33_3=918",
        "https://kpmgireland.avature.net/experiencedhires/SearchJobs/?5339=1416336&5339_format=2564&listFilterMode=1",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1300}, locale="en-IE")
            for url_index, source_url in enumerate(all_source_urls):
                if url_index == 1 and len(results) >= 10:
                    print(f"      [kpmg] {len(results)} jobs from the comprehensive URL alone — "
                          f"skipping the 6 category-specific URLs as likely redundant")
                    break
                try:
                    page.goto(source_url, wait_until="domcontentloaded", timeout=45000)
                    page.wait_for_timeout(1200)
                    _browser_accept_consent(page)
                except Exception:
                    continue

                stagnant, prev = 0, len(results)
                for _ in range(20):
                    anchors = page.locator('a[href*="/FolderDetail/"]')
                    for i in range(anchors.count()):
                        a = anchors.nth(i)
                        try:
                            raw = a.get_attribute("href") or ""
                            href = urllib.parse.urljoin(page.url, raw).split("#")[0]
                        except Exception:
                            continue

                        title = _browser_text(a).strip()
                        node, card = a, ""
                        for _up in range(6):
                            try:
                                candidate = _browser_text(node)
                            except Exception:
                                candidate = ""
                            if candidate and len(candidate) <= 2800:
                                card = candidate
                            if re.search(r"\b(?:Dublin|Ireland|Cork|Galway|Limerick)\b", card, re.I):
                                break
                            try:
                                node = node.locator("..")
                            except Exception:
                                break

                        blob = f"{title}\n{card}\n{href}"
                        # Republic of Ireland only — Avature can mix Belfast
                        # vacancies into the same experienced-hire search.
                        if re.search(r"\bBelfast\b|\bNorthern Ireland\b", blob, re.I):
                            continue
                        if not re.search(r"\b(?:Dublin|Ireland|Cork|Galway|Limerick)\b", blob, re.I):
                            continue

                        if not title or len(title) > 300:
                            lines = [re.sub(r"\s+", " ", x).strip() for x in card.splitlines()
                                     if 4 <= len(x.strip()) <= 220]
                            title = next((x for x in lines
                                          if x.lower() not in {"dublin -", "dublin", "apply now", "view job"}), "")
                        if not title:
                            continue

                        location = "Ireland"
                        for city in ("Dublin", "Cork", "Galway", "Limerick"):
                            if re.search(rf"\b{city}\b", blob, re.I):
                                location = f"{city}, Ireland"
                                break

                        key = href.rstrip("/").lower()
                        posted_text, posted_days = extract_posted_from_text(card)
                        sponsorship, snippet = classify_sponsorship(card[:5000])
                        results[key] = {
                            "company": "KPMG Ireland",
                            "title": re.sub(r"\s+", " ", title).strip()[:300],
                            "location": location,
                            "posted_text": posted_text,
                            "posted_days_ago": posted_days,
                            "employment_type": normalize_employment_type(None, title),
                            "url": href,
                            "source": "kpmg_avature_folderdetail",
                            "visa_sponsorship": sponsorship,
                            "visa_snippet": snippet,
                        }

                    clicked = False
                    for selector in ('a:has-text("Next")', 'button:has-text("Next")', 'a[rel="next"]'):
                        try:
                            nxt = page.locator(selector)
                            if nxt.count() and nxt.first.is_visible():
                                nxt.first.click(timeout=1200)
                                page.wait_for_timeout(500)
                                clicked = True
                                break
                        except Exception:
                            pass

                    page.mouse.wheel(0, 3000)
                    page.wait_for_timeout(300)

                    cur = len(results)
                    stagnant = stagnant + 1 if cur == prev else 0
                    prev = cur
                    if stagnant >= 6 and not clicked:
                        break
            browser.close()
    except Exception as e:
        print(f"      [kpmg] browser scrape failed: {e}")
    print(f"      [kpmg] {len(results)} unique Ireland jobs accumulated")
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
    """Real evidence showed J&J's public careers.jnj.com site is
    Cloudflare-protected ("Just a moment..." never clearing even after a
    35s wait). Real evidence from a different reference showed J&J
    actually runs on Workday underneath (jj.wd5.myworkdayjobs.com) — the
    same pattern that already fixed NVIDIA and Eaton: the protected
    marketing site sits in front of an unprotected backend API. No
    browser needed at all, and genuinely faster than the old approach."""
    api = "https://jj.wd5.myworkdayjobs.com/wday/cxs/jj/JJ/jobs"
    headers = {"User-Agent": "Mozilla/5.0", "Accept": "application/json", "Content-Type": "application/json"}
    results = {}
    offset, limit = 0, 20
    try:
        while offset < 2000:
            payload = {"appliedFacets": {}, "limit": limit, "offset": offset, "searchText": ""}
            r = session.post(api, json=payload, headers=headers, timeout=30)
            if r.status_code != 200:
                print(f"      [jnj] Workday HTTP {r.status_code}")
                break
            data = r.json()
            postings = data.get("jobPostings") or []
            if not postings:
                break
            for job in postings:
                title = re.sub(r"\s+", " ", str(job.get("title") or "")).strip()
                external_path = str(job.get("externalPath") or "").strip()
                locations = re.sub(r"\s+", " ", str(job.get("locationsText") or "")).strip()
                if not title or not external_path:
                    continue
                if not re.search(r"\bIreland\b|\bIE0\d+\b", locations, re.I):
                    continue
                # Reject Northern Ireland-only results, keep Republic of Ireland.
                if (re.search(r"\bNorthern Ireland\b|\bBelfast\b", locations, re.I) and
                        not re.search(r"\bDublin\b|\bCork\b|\bGalway\b|\bLimerick\b|\bMayo\b|\bWestport\b|\bRingaskiddy\b",
                                      locations, re.I)):
                    continue
                location = "Ireland"
                for needle, normalized in [("Dublin", "Dublin, Ireland"), ("Ringaskiddy", "Ringaskiddy, Cork, Ireland"),
                                            ("Cork", "Cork, Ireland"), ("Galway", "Galway, Ireland"),
                                            ("Limerick", "Limerick, Ireland"), ("Westport", "Westport, Mayo, Ireland"),
                                            ("Mayo", "Mayo, Ireland")]:
                    if re.search(rf"\b{re.escape(needle)}\b", locations, re.I):
                        location = normalized
                        break
                url = urllib.parse.urljoin("https://jj.wd5.myworkdayjobs.com", external_path)
                m = re.search(r"(R-\d+)", external_path, re.I)
                key = m.group(1).upper() if m else url.lower()
                posted_text, posted_days = extract_posted_from_text(locations)
                sponsorship, snippet = classify_sponsorship(locations)
                results[key] = {
                    "company": "Johnson & Johnson",
                    "title": title[:300],
                    "location": location,
                    "posted_text": posted_text,
                    "posted_days_ago": posted_days,
                    "employment_type": normalize_employment_type(None, title),
                    "url": url,
                    "source": "jnj_workday",
                    "visa_sponsorship": sponsorship,
                    "visa_snippet": snippet,
                }
            total = data.get("total")
            offset += limit
            if isinstance(total, int) and offset >= total:
                break
    except Exception as e:
        print(f"      [jnj] Workday scrape failed: {e}")
    print(f"      [jnj] {len(results)} unique Ireland jobs accumulated (via Workday API)")
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
                    try:
                        all_links = page.locator("a[href]")
                        hrefs = [all_links.nth(i).get_attribute("href") or "" for i in range(all_links.count())]
                        matching = sum(1 for h in hrefs if re.search(r"jobs\.aon\.com/(?:jobs|signin/jobs|sign-up/jobs)/\d+", h, re.I))
                        print(f"      [aon] {url}: page title={page.title()!r}, total links={len(hrefs)}, matching={matching}")
                        print(f"      [aon] sample real hrefs: {[h for h in hrefs if h and 'aon' in h.lower()][:8]}")
                    except Exception as e:
                        print(f"      [aon] diagnostic read failed: {e}")
                    _browser_collect_job_links_with_retries(
                        page, "Aon", [r"jobs\.aon\.com/(?:jobs|signin/jobs|sign-up/jobs)/\d+"],
                        "aon_browser", results, "Ireland", rounds=35)
                    _collect_links_from_html(
                        page, "Aon", r"jobs\.aon\.com/(?:jobs|signin/jobs|sign-up/jobs)/\d+[^\"'<>?#]*",
                        "aon_browser_html", results, "Ireland")
                except Exception as e:
                    print(f"      [aon] page failed {url}: {e}")
            browser.close()
    except Exception as e:
        print(f"      [aon] browser scrape failed: {e}")
    print(f"      [aon] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_eaton_ireland(session):
    """Eaton's current Ireland careers entry point links to its Eightfold
    applicant portal (eaton.eightfold.ai) — real evidence this replaced
    what used to be direct access to eaton.com, which is why the old
    approach kept timing out. Use the existing Eightfold normalization
    path (already proven for Netflix/NVIDIA) and keep the Ireland
    client-side check."""
    results = []
    try:
        positions = try_eightfold("eaton", session)
        if positions:
            for job in positions:
                norm = normalize_eightfold_job("Eaton", "eaton", job)
                if norm:
                    results.append(norm)
    except Exception as e:
        print(f"      [eaton] Eightfold scrape failed: {e}")
    print(f"      [eaton] {len(results)} unique Ireland jobs accumulated")
    return results



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
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
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
def scrape_cognizant_ireland(session):
    """Real evidence disproved the earlier region-prefix approach: a
    genuine Dublin, Ireland job was found listed under the "india-en"
    URL prefix, and direct diagnostics showed candidates from "uki-en"
    pointing to Bhubaneswar and Bangalore, India. The uki-en/emea-en/
    global-en prefixes are purely LANGUAGE/DISPLAY settings, not location
    filters. The real filter is a keyword query parameter, confirmed
    directly from Cognizant's own site navigation ("See jobs" links for
    each office use ?keyword=<city>)."""
    search_urls = [
        "https://careers.cognizant.com/uki-en/jobs/?keyword=dublin&location=&radius=100&lat=&lng=&cname=&ccode=&pagesize=50",
        "https://careers.cognizant.com/uki-en/jobs/?keyword=cork&location=&radius=100&lat=&lng=&cname=&ccode=&pagesize=50",
        "https://careers.cognizant.com/uki-en/jobs/?keyword=ireland&location=&radius=100&lat=&lng=&cname=&ccode=&pagesize=50",
    ]
    results = {}
    links = []
    seen_candidates = set()
    for search_url in search_urls:
        try:
            resp = session.get(search_url, headers=HEADERS, timeout=20)
            if resp.status_code != 200:
                continue
            page = resp.text
        except Exception:
            continue
        for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', page, re.I | re.S):
            href = urllib.parse.urljoin(search_url, m.group(1))
            if re.search(r"/(?:global-en|emea-en|uki-en|india-en|us-en)/jobs/\d+/[^/?#]+/?$", href):
                if href not in seen_candidates:
                    seen_candidates.add(href)
                    links.append((href, _html_to_text(m.group(2))))
    print(f"      [cognizant] {len(links)} candidate job links found via keyword-filtered search")
    links = links[:200]

    diag_count = [0]

    def check_one(item):
        href, anchor_title = item
        try:
            resp2 = session.get(href, headers=HEADERS, timeout=15)
            if resp2.status_code != 200:
                return None
            text = _html_to_text(resp2.text)
        except Exception:
            return None
        if not is_ireland_location(text):
            if diag_count[0] < 3:
                diag_count[0] += 1
                loc_match = re.search(r".{40}Location\b.{80}", text, re.I)
                print(f"      [cognizant] diag (still non-Ireland): {href}")
                print(f"      [cognizant] diag: {loc_match.group(0)[:150] if loc_match else 'NOT FOUND'!r}")
            return None
        title = anchor_title or "Cognizant role"
        posted_text, posted_days = extract_posted_from_text(text)
        sponsorship, snippet = classify_sponsorship(text[:5000])
        return href, {
            "company": "Cognizant", "title": title[:300],
            "location": _extract_location_from_card(text, "Ireland"),
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "cognizant_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }

    if links:
        pool = ThreadPoolExecutor(max_workers=min(PROBE_WORKERS, len(links)))
        try:
            future_map = {pool.submit(check_one, item): item for item in links}
            for fut, item in future_map.items():
                try:
                    result = fut.result(timeout=20)
                except Exception:
                    result = None
                if result:
                    href, job = result
                    results[href] = job
        finally:
            pool.shutdown(wait=False)
    print(f"      [cognizant] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())




def scrape_aib_ireland(session):
    """AIB's real jobs board, filtered defensively for genuine Irish
    locations and against UK-only postings that might otherwise slip in."""
    if not HAS_PLAYWRIGHT:
        print("      [aib] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://jobs.aib.ie/go/Search-All-Jobs/3834700/", wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1200)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "AIB (Allied Irish Banks)", [r"jobs\.aib\.ie/aib/job/"],
                "aib_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [aib] browser scrape failed: {e}")
    cleaned = {}
    for href, j in results.items():
        text = f"{j.get('title','')} {j.get('location','')}".lower()
        irish = bool(re.search(r"\b(dublin|cork|galway|limerick|waterford|kildare|ireland)\b", text))
        uk_only = bool(re.search(r"\b(london|belfast|england|scotland|wales|united kingdom)\b", text)) and not irish
        if irish and not uk_only:
            cleaned[href] = j
    print(f"      [aib] {len(cleaned)} unique Ireland jobs accumulated")
    return list(cleaned.values())


def scrape_bnp_paribas_ireland(session):
    """BNP's Dublin listing is server-rendered — plain HTTP first, real
    browser fallback only if that comes back empty."""
    company = "BNP Paribas Ireland"
    urls = ["https://group.bnpparibas/en/careers/all-job-offers/county-dublin",
            "https://group.bnpparibas/en/careers/all-job-offers/dublin",
            "https://group.bnpparibas/en/careers/all-job-offers/permanent/ireland"]
    results = {}
    for url in urls:
        try:
            resp = session.get(url, headers=HEADERS, timeout=20)
            if resp.status_code != 200:
                continue
            page = resp.text
        except Exception:
            continue
        for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', page, re.I | re.S):
            href = urllib.parse.urljoin(url, m.group(1))
            title = _html_to_text(m.group(2))
            if not title or len(title) < 4:
                continue
            start, end = max(0, m.start() - 1500), min(len(page), m.end() + 1500)
            card = _html_to_text(page[start:end])
            if not is_ireland_location(f"{title} {card}"):
                continue
            if not ("/careers/" in href or "/jobs/" in href):
                continue
            if any(x in title.lower() for x in ("create email alert", "display job offers", "apply now")):
                continue
            posted_text, posted_days = extract_posted_from_text(card)
            sponsorship, snippet = classify_sponsorship(card[:5000])
            results[href] = {
                "company": company, "title": title[:300], "location": "Dublin, Ireland",
                "posted_text": posted_text, "posted_days_ago": posted_days,
                "employment_type": normalize_employment_type(None, title),
                "url": href, "source": "bnp_direct",
                "visa_sponsorship": sponsorship, "visa_snippet": snippet,
            }
    if not results and HAS_PLAYWRIGHT:
        try:
            with sync_playwright() as pw:
                browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
                page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
                page.goto(urls[0], wait_until="domcontentloaded", timeout=30000)
                page.wait_for_timeout(1200)
                _browser_accept_consent(page)
                _browser_collect_job_links_with_retries(
                    page, company, [r"group\.bnpparibas/en/careers/"],
                    "bnp_browser", results, "Dublin, Ireland", rounds=25)
                browser.close()
        except Exception as e:
            print(f"      [bnp] browser fallback failed: {e}")
    print(f"      [bnp] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_blackrock_ireland(session):
    """BlackRock runs on Phenom (same platform as Citi, which already
    works via real browser automation — the widget/refNum API approach
    never worked all session, browser automation reading the rendered
    page is the technique that actually succeeds for Phenom sites)."""
    if not HAS_PLAYWRIGHT:
        print("      [blackrock] playwright not installed — skipping")
        return []
    urls = [
        "https://careers.blackrock.com/location/dublin-jobs/45831/2963597-7521314-2964574/4",
        "https://careers.blackrock.com/search-jobs?location=Dublin%2C%20Ireland",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=30000)
                    page.wait_for_timeout(1200)
                    _browser_accept_consent(page)
                    _browser_collect_job_links_with_retries(
                        page, "BlackRock", [r"careers\.blackrock\.com/job/dublin/"],
                        "blackrock_browser", results, "Dublin, Ireland", rounds=30)
                except Exception as e:
                    print(f"      [blackrock] page failed {url}: {e}")
            browser.close()
    except Exception as e:
        print(f"      [blackrock] browser scrape failed: {e}")
    for j in results.values():
        j["title"] = re.split(r"\s*Location:\s*", j.get("title", ""), maxsplit=1, flags=re.I)[0].strip()
        j["location"] = "Dublin, Ireland"
    print(f"      [blackrock] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_bank_of_ireland_direct(session):
    """Bank of Ireland's own jobs board, filtered against UK-only postings."""
    if not HAS_PLAYWRIGHT:
        print("      [boi] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://careers.bankofireland.com/jobs/search", wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1200)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Bank of Ireland", [r"careers\.bankofireland\.com/jobs/"],
                "boi_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [boi] browser scrape failed: {e}")
    cleaned = {}
    for href, j in results.items():
        title = (j.get("title") or "").strip()
        text = f"{title} {j.get('location','')}".lower()
        if not title or title.lower().startswith("skip to") or "#jobs_search_results" in href:
            continue
        irish = bool(re.search(r"\b(dublin|cork|galway|limerick|waterford|kilkenny|ireland)\b", text))
        uk_only = bool(re.search(r"\b(bristol|london|belfast|england|scotland|wales|united kingdom|\buk\b)\b", text)) and not irish
        if irish and not uk_only:
            cleaned[href] = j
    print(f"      [boi] {len(cleaned)} unique Ireland jobs accumulated")
    return list(cleaned.values())


def scrape_ing_ireland(session):
    """ING also runs on Phenom — same technique as Citi/BlackRock."""
    if not HAS_PLAYWRIGHT:
        print("      [ing] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://careers.ing.com/en/location/dublin-jobs/2618/2963597-7521314-2964574/4",
                       wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1200)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "ING", [r"careers\.ing\.com/en/job/dublin/"],
                "ing_browser", results, "Dublin, Ireland", rounds=30)
            browser.close()
    except Exception as e:
        print(f"      [ing] browser scrape failed: {e}")
    print(f"      [ing] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_deutsche_bank_ireland(session):
    """Deutsche Bank's professional roles search, real browser rendering."""
    if not HAS_PLAYWRIGHT:
        print("      [deutsche-bank] playwright not installed — skipping")
        return []
    urls = ["https://careers.db.com/professionals/search-roles/"]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                page.goto(url, wait_until="domcontentloaded", timeout=30000)
                page.wait_for_timeout(1800)
                _browser_accept_consent(page)
                _collect_verified_ireland_page_jobs(
                    page, "Deutsche Bank", r"careers\.db\.com/professionals/job/",
                    "deutsche_bank_browser", results, "Ireland")
            browser.close()
    except Exception as e:
        print(f"      [deutsche-bank] browser scrape failed: {e}")
    print(f"      [deutsche-bank] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_arup_ireland(session):
    """Arup's real dedicated Ireland jobs page, lightweight regex parse —
    no browser needed."""
    source_url = "https://jobs.arup.com/page/jobs-in-ireland-252"
    results = {}
    try:
        resp = session.get(source_url, headers=HEADERS, timeout=20)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []
    for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']*?/jobs/[^"\']+)["\'][^>]*>(.*?)</a>', page, re.I | re.S):
        href = urllib.parse.urljoin(source_url, m.group(1)).split("?")[0]
        title = _html_to_text(m.group(2)).strip()
        if "/other-jobs-matching/" in href.lower():
            continue
        if not re.search(r"/jobs/[a-z0-9][^/]*-\d+$", href, re.I):
            continue
        if not title or title.lower() in {"learn more", "jobs", "search jobs"}:
            continue
        if title.startswith("\U0001F50D"):
            continue
        if href in results:
            continue
        start, end = max(0, m.start() - 800), min(len(page), m.end() + 800)
        card = _html_to_text(page[start:end])
        posted_text, posted_days = extract_posted_from_text(card)
        sponsorship, snippet = classify_sponsorship(card[:5000])
        results[href] = {
            "company": "Arup", "title": title[:300],
            "location": _extract_location_from_card(card, "Ireland"),
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "arup_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [arup] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_central_bank_ireland_direct(session):
    """Central Bank of Ireland's real Candidate Manager vacancies board —
    genuinely new company, not previously in the pipeline at all."""
    if not HAS_PLAYWRIGHT:
        print("      [central-bank] playwright not installed — skipping")
        return []
    url = "https://www.candidatemanager.net/cm/p/pJobs.aspx?a=1bqO7eBaJhQ%3D&mid=YUYF&sid=BDCXCX"
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1400, "height": 1000}, locale="en-IE")
            page.goto(url, wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(900)
            body = _browser_text(page.locator("body"))
            if "no jobs were found" not in body.lower():
                anchors = page.locator("a[href*='pJobDetails.aspx']")
                for i in range(anchors.count()):
                    a = anchors.nth(i)
                    href = urllib.parse.urljoin(page.url, a.get_attribute("href") or "")
                    title = _browser_text(a)
                    if href and title and href not in results:
                        sponsorship, snippet = classify_sponsorship(title)
                        results[href] = {
                            "company": "Central Bank of Ireland", "title": title[:300],
                            "location": "Dublin, Ireland", "posted_text": "Unknown", "posted_days_ago": None,
                            "employment_type": normalize_employment_type(None, title),
                            "url": href, "source": "central_bank_direct",
                            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
                        }
            browser.close()
    except Exception as e:
        print(f"      [central-bank] browser scrape failed: {e}")
    print(f"      [central-bank] {len(results)} current vacancies")
    return list(results.values())




def scrape_irish_life_ireland(session):
    """Irish Life's real careers board (life-careers.com)."""
    if not HAS_PLAYWRIGHT:
        print("      [irish-life] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://life-careers.com/irishlife/go/irishlife/3805801",
                       wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1500)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Irish Life", [r"life-careers\.com/irishlife/job/"],
                "irish_life_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [irish-life] browser scrape failed: {e}")
    print(f"      [irish-life] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_ups_ireland(session):
    """UPS Ireland's real jobs board, filtered to genuine Irish locations."""
    if not HAS_PLAYWRIGHT:
        print("      [ups] playwright not installed — skipping")
        return []
    url = ("https://www.jobs-ups.com/global/en/search-results"
           "?p=ChIJ5QX6zvnKd0gRYREw9umce3I&location=Ireland%2C%20Shefford%2C%20UK"
           "&latitude=53.40833676721639&longitude=-6.160288504069749")
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto(url, wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1800)
            _browser_accept_consent(page)
            _collect_verified_ireland_page_jobs(
                page, "UPS Ireland", r"jobs-ups\.com/global/en/job/",
                "ups_browser", results, "Ireland")
            browser.close()
    except Exception as e:
        print(f"      [ups] browser scrape failed: {e}")
    print(f"      [ups] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_three_ireland_direct(session):
    """Three Ireland's real Cornerstone OnDemand careers site."""
    if not HAS_PLAYWRIGHT:
        print("      [three-ireland] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://three-ireland.csod.com/ux/ats/careersite/5/home?c=three-ireland&country=ie",
                       wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1800)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Three Ireland", [r"three-ireland\.csod\.com/.*ats/careersite/.*job"],
                "three_ireland_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [three-ireland] browser scrape failed: {e}")
    print(f"      [three-ireland] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_aiven_ireland(session):
    """Aiven's careers listing, lightweight regex parse — no browser needed."""
    listing = "https://aiven.io/careers/job"
    results = {}
    try:
        resp = session.get(listing, headers=HEADERS, timeout=20)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []
    for m in re.finditer(r'href=["\']([^"\']*/careers/job/\d+[^"\']*)["\']', page, re.I):
        href = urllib.parse.urljoin(listing, m.group(1)).split("?")[0]
        if href in results:
            continue
        start, end = max(0, m.start() - 800), min(len(page), m.end() + 800)
        card = _html_to_text(page[start:end])
        if not is_ireland_location(card):
            continue
        title_m = re.search(r'>([^<]{4,180})</a>', page[m.start():m.start() + 500])
        title = title_m.group(1).strip() if title_m else "Aiven role"
        posted_text, posted_days = extract_posted_from_text(card)
        sponsorship, snippet = classify_sponsorship(card[:5000])
        results[href] = {
            "company": "Aiven", "title": title[:300],
            "location": _extract_location_from_card(card, "Ireland"),
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "aiven_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [aiven] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_huawei_ireland(session):
    """Huawei Ireland's Teamtailor board."""
    if not HAS_PLAYWRIGHT:
        print("      [huawei] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://huaweiireland.teamtailor.com/jobs", wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1200)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Huawei", [r"huaweiireland\.teamtailor\.com/jobs/\d+"],
                "huawei_browser", results, "Ireland", rounds=20)
            browser.close()
    except Exception as e:
        print(f"      [huawei] browser scrape failed: {e}")
    print(f"      [huawei] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_ge_healthcare_ireland(session):
    """GE HealthCare runs on Phenom — same technique as BlackRock/Citi/ING."""
    if not HAS_PLAYWRIGHT:
        print("      [ge-healthcare] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://careers.gehealthcare.com/global/en/search-results?keywords=Ireland",
                       wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1500)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "GE HealthCare", [r"careers\.gehealthcare\.com/global/en/job/"],
                "ge_healthcare_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [ge-healthcare] browser scrape failed: {e}")
    print(f"      [ge-healthcare] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_exl_ireland(session):
    """EXL runs Oracle Recruiting Cloud — reuses the same real API technique
    already proven for JPMorgan/Oracle, just a different tenant."""
    return scrape_oracle_candidate_experience(
        "EXL", "https://fa-ewjt-saasfaprod1.fa.ocs.oraclecloud.com", "CX_2", session)


def scrape_ntt_data_ireland(session):
    """NTT DATA's official SuccessFactors board — same technique as EY."""
    if not HAS_PLAYWRIGHT:
        print("      [ntt-data] playwright not installed — skipping")
        return []
    base = "https://careers-inc.nttdata.com"
    urls = [f"{base}/search/?q=&locationsearch=Ireland", f"{base}/search/?q=&locationsearch=Dublin"]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                page.goto(url, wait_until="domcontentloaded", timeout=30000)
                page.wait_for_timeout(1200)
                _browser_accept_consent(page)
                _collect_filtered_page_jobs(
                    page, "NTT DATA", rf"{re.escape(base)}/job/",
                    "ntt_data_browser", results, "Ireland")
            browser.close()
    except Exception as e:
        print(f"      [ntt-data] browser scrape failed: {e}")
    print(f"      [ntt-data] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_guidewire_ireland(session):
    """Guidewire's official careers listing."""
    if not HAS_PLAYWRIGHT:
        print("      [guidewire] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://www.guidewire.com/about/careers/jobs", wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1500)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Guidewire", [r"guidewire\.com/about/careers/jobs/"],
                "guidewire_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [guidewire] browser scrape failed: {e}")
    print(f"      [guidewire] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_hcltech_ireland(session):
    """HCLTech's Ireland-filtered search page."""
    if not HAS_PLAYWRIGHT:
        print("      [hcltech] playwright not installed — skipping")
        return []
    urls = [
        "https://careers.hcltech.com/search/?q=&locationsearch=Ireland",
        "https://careers.hcltech.com/search/?q=&locationsearch=Dublin",
    ]
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            for url in urls:
                page.goto(url, wait_until="domcontentloaded", timeout=30000)
                page.wait_for_timeout(1200)
                _browser_accept_consent(page)
                _collect_filtered_page_jobs(
                    page, "HCLTech", r"careers\.hcltech\.com/job/",
                    "hcltech_browser", results, "Ireland")
            browser.close()
    except Exception as e:
        print(f"      [hcltech] browser scrape failed: {e}")
    print(f"      [hcltech] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_allianz_ireland(session):
    """Allianz Ireland's real careers page."""
    if not HAS_PLAYWRIGHT:
        print("      [allianz] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://careers.allianz.com/ie/en/allianz-ireland", wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1500)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Allianz", [r"careers\.allianz\.com/.*/job/"],
                "allianz_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [allianz] browser scrape failed: {e}")
    print(f"      [allianz] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_siemens_ireland(session):
    """Siemens' Avature-powered search."""
    if not HAS_PLAYWRIGHT:
        print("      [siemens] playwright not installed — skipping")
        return []
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto("https://jobs.siemens.com/en_US/externaljobs/SearchJobs/?jobRecordsPerPage=25&searchKeyword=Ireland",
                       wait_until="domcontentloaded", timeout=30000)
            page.wait_for_timeout(1800)
            _browser_accept_consent(page)
            _browser_collect_job_links_with_retries(
                page, "Siemens", [r"jobs\.siemens\.com/en_US/externaljobs/JobDetail/"],
                "siemens_browser", results, "Ireland", rounds=25)
            browser.close()
    except Exception as e:
        print(f"      [siemens] browser scrape failed: {e}")
    print(f"      [siemens] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_pepsico_ireland(session):
    """Real evidence found a properly Ireland-filtered search URL
    (location=Ireland&woe=12&regionCode=IE) that works with plain HTTP
    requests — no browser needed at all, faster and more reliable than
    the previous Playwright-based approach (which had been hitting
    intermittent 403s). A handful of known-good job IDs are checked
    too as a supplement, in case the search index is temporarily
    incomplete — real, current jobs either way, deduplicated by URL."""
    ireland_url = ("https://www.pepsicojobs.com/main/jobs"
                   "?stretchUnit=MILES&stretch=10&location=Ireland&woe=12&regionCode=IE")
    fallback_urls = [
        "https://www.pepsicojobs.com/main/jobs/451831?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/443247?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/447137?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/415897?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/457279?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/462258?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/401833?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/461086?lang=en-us",
        "https://www.pepsicojobs.com/main/jobs/456011?lang=en-us",
    ]
    results = {}

    def add_detail(href):
        try:
            r = session.get(href, timeout=20, headers={
                "User-Agent": "Mozilla/5.0", "Accept-Language": "en-IE,en;q=0.9", "Referer": ireland_url})
        except Exception:
            return
        if r.status_code != 200:
            return
        html_text = r.text or ""
        body = _html_to_text(html_text)
        if re.search(r"\bNorthern Ireland\b|\bBelfast\b", body, re.I):
            return
        if not re.search(r"\bIreland\b|\bDublin\b|\bCork\b", body, re.I):
            return
        title = ""
        hm = re.search(r"<h1\b[^>]*>(.*?)</h1>", html_text, re.I | re.S)
        if hm:
            title = re.sub(r"\s+", " ", _html_to_text(hm.group(1))).strip()
        if not title:
            tm = re.search(r'Pepsico Global is hiring a (.*?) in .*?Ireland', body, re.I | re.S)
            if tm:
                title = re.sub(r"\s+", " ", tm.group(1)).strip()
        if not title:
            return
        location = "Ireland"
        if re.search(r"\bDublin(?: 2)?\b", body, re.I):
            location = "Dublin, Ireland"
        elif re.search(r"\bCork\b", body, re.I):
            location = "Cork, Ireland"
        canonical = href.split("?")[0]
        posted_text, posted_days = extract_posted_from_text(body)
        sponsorship, snippet = classify_sponsorship(body[:5000])
        results[canonical.rstrip("/").lower()] = {
            "company": "PepsiCo",
            "title": title[:300],
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": canonical,
            "source": "pepsico_direct",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }

    try:
        r = session.get(ireland_url, timeout=20, headers={"User-Agent": "Mozilla/5.0", "Accept-Language": "en-IE,en;q=0.9"})
    except Exception:
        r = None
    if r is not None and r.status_code == 200:
        html_text = r.text or ""
        for mm in re.finditer(r'href=["\']([^"\']*/main/jobs/\d+[^"\']*)["\']', html_text, re.I):
            href = urllib.parse.urljoin(ireland_url, mm.group(1))
            start, end = max(0, mm.start() - 1800), min(len(html_text), mm.end() + 2200)
            card_text = _html_to_text(html_text[start:end])
            if not re.search(r"\bIreland\b|\bDublin\b|\bCork\b", card_text, re.I):
                continue
            add_detail(href)

    for href in fallback_urls:
        add_detail(href)

    print(f"      [pepsico] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())




def scrape_esb_ireland(session):
    """ESB (Ireland's national utility) — real SuccessFactors board, no
    browser needed. Excludes Northern Ireland/UK-only postings."""
    base = "https://careers.esb.ie"
    urls = [
        f"{base}/go/All-Jobs/882102/",
        f"{base}/go/All-Jobs/882102/20/",
        f"{base}/search/?q=&q2=&locationsearch=ireland&location=dublin",
    ]
    results = {}
    for url in urls:
        try:
            resp = session.get(url, headers=HEADERS, timeout=20)
            if resp.status_code != 200:
                continue
            page = resp.text
        except Exception:
            continue
        for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']*?/job/[^"\']+)["\'][^>]*>(.*?)</a>', page, re.I | re.S):
            href = urllib.parse.urljoin(base, m.group(1)).split("?")[0]
            raw_anchor_text = re.sub(r"\s+", " ", _html_to_text(m.group(2))).strip()
            # Real evidence: ESB's markup wraps a whole table row in the
            # link, not just the title — but the genuine title appears
            # twice in a row within that blob (a SuccessFactors quirk).
            # Detect that repeat and use just one copy of it.
            repeat_match = re.search(r'([A-Z][A-Za-z0-9,&()/\- ]{4,120}?)\s+\1(?=\s|$)', raw_anchor_text)
            title = repeat_match.group(1).strip() if repeat_match else raw_anchor_text
            if not href or not title:
                continue
            start, end = max(0, m.start() - 1000), min(len(page), m.end() + 1800)
            card = re.sub(r"\s+", " ", _html_to_text(page[start:end])).strip()
            if not is_ireland_location(card):
                continue
            if re.search(r"\bBelfast\b|\bNorthern Ireland\b", card, re.I) and not re.search(r"\bIE\b|\bIreland\b", card, re.I):
                continue
            # Real evidence: the generic card-text location extraction can
            # pick up an unrelated Dublin mention from elsewhere in the
            # same blob (a Cork/Wilton job was showing "Dublin" as its
            # location). The URL's own slug reliably encodes the real
            # location as its first segment instead.
            slug = href.rsplit("/job/", 1)[-1].split("/")[0] if "/job/" in href else ""
            first_token = slug.split("-")[0] if slug else ""
            non_place_tokens = {"flexible", "remote", "various", "multiple", "national"}
            if first_token and first_token.lower() not in non_place_tokens:
                location = f"{first_token}, Ireland"
            else:
                location = "Ireland"
            key = href.rstrip("/").lower()
            posted_text, posted_days = extract_posted_from_text(card)
            sponsorship, snippet = classify_sponsorship(card[:5000])
            results[key] = {
                "company": "ESB", "title": title[:300], "location": location,
                "posted_text": posted_text, "posted_days_ago": posted_days,
                "employment_type": normalize_employment_type(None, title),
                "url": href, "source": "esb_successfactors",
                "visa_sponsorship": sponsorship, "visa_snippet": snippet,
            }
    print(f"      [esb] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_irish_rail_ireland(session):
    """Irish Rail (Iarnród Éireann) — direct, server-rendered careers page."""
    company = "Irish Rail (Iarnród Éireann)"
    base = "https://www.irishrail.ie"
    source_url = f"{base}/en-ie/about-us/company-information/career-opportunities-at-iarnrod-eireann"
    results = {}
    try:
        resp = session.get(source_url, headers=HEADERS, timeout=20)
        if resp.status_code != 200:
            print("      [irish-rail] page failed to load")
            return []
        resp.encoding = "utf-8"  # real evidence: server doesn't declare charset correctly,
        # causing requests to guess wrong and produce mojibake in titles
        page = resp.text
    except Exception as e:
        print(f"      [irish-rail] failed: {e}")
        return []
    skip_titles = {"career opportunities", "graduate programme", "apprenticeship programme",
                    "print page", "company information", "safety and security"}
    role_words = re.compile(r"\b(analyst|architect|engineer|manager|specialist|officer|administrator|"
                             r"supervisor|planner|technician|advisor|executive|controller|accountant|"
                             r"lead|director|coordinator|project|commercial|security|revenue)\b", re.I)
    for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', page, re.I | re.S):
        href = urllib.parse.urljoin(base, m.group(1))
        title = re.sub(r"\s+", " ", _html_to_text(m.group(2))).strip()
        if not href or not title or title.lower() in skip_titles:
            continue
        if "/career-opportunities-at-iarnrod-eireann/" not in href.lower():
            continue
        if not role_words.search(f"{title} {href}"):
            continue
        key = href.split("#")[0].rstrip("/").lower()
        sponsorship, snippet = classify_sponsorship(title)
        results[key] = {
            "company": company, "title": title[:300], "location": "Ireland",
            "posted_text": "Unknown", "posted_days_ago": None,
            "employment_type": normalize_employment_type(None, title),
            "url": href.split("#")[0], "source": "irish_rail_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [irish-rail] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_avolon_ireland(session):
    """Avolon (aircraft leasing) — real Salesforce-hosted job listings."""
    url = "https://www.avolon.aero/careers"
    results = {}
    try:
        resp = session.get(url, headers=HEADERS, timeout=25)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []
    for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>', page, re.I):
        href = urllib.parse.urljoin(url, m.group(1))
        if "mytribe.my.salesforce-sites.com" not in href or "vacancyNo=" not in href:
            continue
        start, end = max(0, m.start() - 1200), min(len(page), m.end() + 800)
        raw_slice = page[start:end]
        # Real evidence: a fixed-offset slice can cut through the middle of
        # an HTML tag, leaving a broken fragment (no opening '<') that then
        # leaks through as if it were visible text. Trim to the first
        # genuine tag boundary instead of using the raw offset directly.
        first_tag = raw_slice.find("<")
        if first_tag > 0:
            raw_slice = raw_slice[first_tag:]
        card = re.sub(r"\s+", " ", _html_to_text(raw_slice)).strip()
        if not re.search(r"\bDublin\b|\bIreland\b", card, re.I):
            continue
        title_m = re.search(r"(.+?)\s+Dublin\s*,\s*Ireland", card, re.I)
        title = title_m.group(1).strip() if title_m else ""
        # Strip leaked table-header words (e.g. "TITLE LOCATION" preceding
        # the real title in some card layouts) rather than including them.
        title = re.sub(r"^(?:TITLE|LOCATION|JOB TITLE)\s+", "", title, flags=re.I).strip()
        if not title:
            lines = [x.strip() for x in card.splitlines() if 4 <= len(x.strip()) <= 180]
            title = lines[0] if lines else ""
        if not title:
            continue
        key = href.split("?")[0].rstrip("/").lower() + "?" + (re.search(r"vacancyNo=(\d+)", href) or [None, ""])[1]
        posted_text, posted_days = extract_posted_from_text(card)
        sponsorship, snippet = classify_sponsorship(card[:5000])
        results[key] = {
            "company": "Avolon", "title": title[:300], "location": "Dublin, Ireland",
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "avolon_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [avolon] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_bloomberg_ireland(session):
    """Bloomberg — real Avature board with pagination."""
    base = "https://bloomberg.avature.net"
    search_base = (f"{base}/careers/SearchJobs/?1845=%5B162465%5D&1845_format=3996"
                    f"&listFilterMode=1&jobRecordsPerPage=12")
    results = {}
    for offset in range(0, 300, 12):
        url = f"{search_base}&jobOffset={offset}"
        try:
            resp = session.get(url, headers=HEADERS, timeout=20)
            if resp.status_code != 200:
                break
            page = resp.text
        except Exception:
            break
        before = len(results)
        matches = re.findall(r'bloomberg\.avature\.net/careers/JobDetail/([^/"<>]+)/(\d+)', page, re.I)
        matches += re.findall(r'href=["\']\/careers\/JobDetail\/([^/"\']+)\/(\d+)["\']', page, re.I)
        for slug, job_id in matches:
            key = job_id
            if key in results:
                continue
            title = re.sub(r"[-_]+", " ", urllib.parse.unquote(slug)).strip()
            href = f"{base}/careers/JobDetail/{slug}/{job_id}"
            idx = page.find(job_id)
            start, end = max(0, idx - 800), min(len(page), idx + 800)
            card = re.sub(r"\s+", " ", _html_to_text(page[start:end])).strip()
            posted_text, posted_days = extract_posted_from_text(card)
            sponsorship, snippet = classify_sponsorship(card[:5000])
            results[key] = {
                "company": "Bloomberg", "title": title[:300], "location": "Dublin, Ireland",
                "posted_text": posted_text, "posted_days_ago": posted_days,
                "employment_type": normalize_employment_type(None, title),
                "url": href, "source": "bloomberg_avature",
                "visa_sponsorship": sponsorship, "visa_snippet": snippet,
            }
        if len(results) == before:
            break
    print(f"      [bloomberg] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_amcs_ireland(session):
    """AMCS Group — verifies Ireland on each individual vacancy page,
    not just the listing card, since neighbouring cards could otherwise
    leak their location into another job."""
    base = "https://www.amcsgroup.com/careers/"
    results = {}
    candidate_urls = set()
    for page_no in range(1, 6):
        url = base if page_no == 1 else f"{base}page/{page_no}/"
        try:
            resp = session.get(url, headers=HEADERS, timeout=20)
            if resp.status_code != 200:
                break
            page = resp.text
        except Exception:
            break
        found = 0
        for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\']', page, re.I):
            href = urllib.parse.urljoin(url, m.group(1)).split("?")[0].split("#")[0]
            if re.match(r"^https://www\.amcsgroup\.com/careers/[^/]+/?$", href, re.I) and href.rstrip("/") != base.rstrip("/"):
                if href not in candidate_urls:
                    candidate_urls.add(href)
                    found += 1
        if found == 0:
            break
    for href in list(candidate_urls)[:80]:
        try:
            resp = session.get(href, headers=HEADERS, timeout=15)
            if resp.status_code != 200:
                continue
            text = re.sub(r"\s+", " ", _html_to_text(resp.text)).strip()
        except Exception:
            continue
        if not is_ireland_location(text):
            continue
        title_m = re.search(r"<h1\b[^>]*>(.*?)</h1>", resp.text, re.I | re.S)
        title = re.sub(r"\s+", " ", _html_to_text(title_m.group(1))).strip() if title_m else ""
        if not title:
            continue
        location = _extract_location_from_card(text, "Ireland")
        key = href.rstrip("/").lower()
        posted_text, posted_days = extract_posted_from_text(text)
        sponsorship, snippet = classify_sponsorship(text[:5000])
        results[key] = {
            "company": "AMCS Group", "title": title[:300], "location": location,
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "amcs_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [amcs] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_dawn_meats_ireland(session):
    """Dawn Meats — real iCIMS-hosted board."""
    sources = [
        "https://c-12895-20230316-www-dawnmeats-com.i.icims.com/careers/current-opportunities/",
    ]
    results = {}
    for url in sources:
        try:
            resp = session.get(url, headers=HEADERS, timeout=25, allow_redirects=True)
            if resp.status_code >= 400:
                print(f"      [dawn-meats] {url}: HTTP {resp.status_code}")
                continue
            page = resp.text
            final_url = resp.url
            job_link_count = len(re.findall(r'/jobs?/[^"\']+', page, re.I))
            print(f"      [dawn-meats] {url} -> {final_url}: {len(page)} chars, "
                  f"{job_link_count} raw job-path mentions")
        except Exception as e:
            print(f"      [dawn-meats] {url}: failed ({e})")
            continue
        for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']*?/jobs?/[^"\']+)["\'][^>]*>(.*?)</a>', page, re.I | re.S):
            href = urllib.parse.urljoin(final_url, m.group(1)).split("?")[0]
            title = re.sub(r"\s+", " ", _html_to_text(m.group(2))).strip()
            if not title or len(title) < 4:
                continue
            start, end = max(0, m.start() - 800), min(len(page), m.end() + 800)
            card = re.sub(r"\s+", " ", _html_to_text(page[start:end])).strip()
            if not is_ireland_location(card):
                continue
            key = href.rstrip("/").lower()
            posted_text, posted_days = extract_posted_from_text(card)
            sponsorship, snippet = classify_sponsorship(card[:5000])
            results[key] = {
                "company": "Dawn Meats", "title": title[:300],
                "location": _extract_location_from_card(card, "Ireland"),
                "posted_text": posted_text, "posted_days_ago": posted_days,
                "employment_type": normalize_employment_type(None, title),
                "url": href, "source": "dawn_meats_icims",
                "visa_sponsorship": sponsorship, "visa_snippet": snippet,
            }
    print(f"      [dawn-meats] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_auxilion_ireland(session):
    """Auxilion — Irish IT services company, direct careers page."""
    source = "https://www.auxilion.com/auxilion-careers"
    results = {}
    try:
        resp = session.get(source, headers=HEADERS, timeout=20)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []
    candidates = set()
    for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\']', page, re.I):
        href = urllib.parse.urljoin(source, m.group(1)).split("?")[0].split("#")[0]
        if "/careers/" in href and href.rstrip("/") != source.rstrip("/"):
            candidates.add(href)
    for href in list(candidates)[:40]:
        try:
            resp = session.get(href, headers=HEADERS, timeout=15)
            if resp.status_code >= 400:
                continue
            text = re.sub(r"\s+", " ", _html_to_text(resp.text)).strip()
        except Exception:
            continue
        if not is_ireland_location(text):
            continue
        title_m = re.search(r"<h1\b[^>]*>(.*?)</h1>", resp.text, re.I | re.S)
        title = re.sub(r"\s+", " ", _html_to_text(title_m.group(1))).strip() if title_m else ""
        if not title:
            continue
        key = href.rstrip("/").lower()
        posted_text, posted_days = extract_posted_from_text(text)
        sponsorship, snippet = classify_sponsorship(text[:5000])
        results[key] = {
            "company": "Auxilion", "title": title[:300],
            "location": _extract_location_from_card(text, "Ireland"),
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "auxilion_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [auxilion] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_biomarin_ireland(session):
    """BioMarin — real careers listing (biomarin.com/job/<slug>)."""
    source = "https://www.biomarin.com/careers/jobs/"
    results = {}
    try:
        resp = session.get(source, headers=HEADERS, timeout=20)
        if resp.status_code != 200:
            return []
        page = resp.text
    except Exception:
        return []
    job_links = set()
    for m in re.finditer(r'href=["\']([^"\']+)["\']', page, re.I):
        href = urllib.parse.urljoin(source, m.group(1))
        if re.search(r"https://www\.biomarin\.com/job/[^/?#]+/?$", href, re.I):
            job_links.add(href.split("?")[0].split("#")[0])
    for href in list(job_links)[:60]:
        try:
            resp = session.get(href, headers=HEADERS, timeout=15)
            if resp.status_code >= 400:
                continue
            text = re.sub(r"\s+", " ", _html_to_text(resp.text)).strip()
        except Exception:
            continue
        if not is_ireland_location(text):
            continue
        title_m = re.search(r"<h1\b[^>]*>(.*?)</h1>", resp.text, re.I | re.S)
        title = re.sub(r"\s+", " ", _html_to_text(title_m.group(1))).strip() if title_m else ""
        if not title:
            slug = href.rstrip("/").rsplit("/", 1)[-1]
            title = re.sub(r"[-_]+", " ", slug).strip().title()
        key = href.rstrip("/").lower()
        posted_text, posted_days = extract_posted_from_text(text)
        sponsorship, snippet = classify_sponsorship(text[:5000])
        results[key] = {
            "company": "BioMarin", "title": title[:300],
            "location": _extract_location_from_card(text, "Ireland"),
            "posted_text": posted_text, "posted_days_ago": posted_days,
            "employment_type": normalize_employment_type(None, title),
            "url": href, "source": "biomarin_direct",
            "visa_sponsorship": sponsorship, "visa_snippet": snippet,
        }
    print(f"      [biomarin] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())


def scrape_asl_aviation_ireland(session):
    """ASL Aviation Holdings — Cezanne OnDemand ATS. Real evidence showed
    a plain HTTP fetch only returns JavaScript tracking code, not real
    vacancy content — this site genuinely requires browser rendering,
    unlike the other lightweight companies. Only accepts a vacancy when
    its own detail page explicitly names an Irish city — corporate
    boilerplate mentioning Dublin/Ireland elsewhere is not sufficient."""
    if not HAS_PLAYWRIGHT:
        print("      [asl-aviation] playwright not installed — skipping")
        return []
    base = "https://cezanneondemand.intervieweb.it/aslaviationgroup/en/career"
    results = {}
    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--disable-http2"])
            page = browser.new_page(viewport={"width": 1440, "height": 1100}, locale="en-IE")
            page.goto(base, wait_until="domcontentloaded", timeout=45000)
            page.wait_for_timeout(2500)
            _browser_accept_consent(page)
            vacancy_urls = set()
            for _ in range(15):
                anchors = page.locator("a[href]")
                for i in range(anchors.count()):
                    try:
                        raw = anchors.nth(i).get_attribute("href") or ""
                    except Exception:
                        continue
                    href = urllib.parse.urljoin(page.url, raw).split("#")[0].split("?")[0]
                    if re.search(r"/career/\w*job\w*/", href, re.I) or re.search(r"/career/[^/]+/\d+", href):
                        vacancy_urls.add(href)
                page.mouse.wheel(0, 3000)
                page.wait_for_timeout(400)
            print(f"      [asl-aviation] {len(vacancy_urls)} candidate vacancy links found")
            for href in list(vacancy_urls)[:60]:
                try:
                    resp2 = session.get(href, headers=HEADERS, timeout=15)
                    if resp2.status_code >= 400:
                        continue
                    text = re.sub(r"\s+", " ", _html_to_text(resp2.text)).strip()
                except Exception:
                    continue
                loc_match = re.search(r"\b(Dublin|Cork|Shannon|Galway)\b", text, re.I)
                if not loc_match:
                    continue
                title_m = re.search(r"<h1\b[^>]*>(.*?)</h1>", resp2.text, re.I | re.S)
                title = re.sub(r"\s+", " ", _html_to_text(title_m.group(1))).strip() if title_m else ""
                if not title:
                    continue
                key = href.rstrip("/").lower()
                posted_text, posted_days = extract_posted_from_text(text)
                sponsorship, snippet = classify_sponsorship(text[:5000])
                results[key] = {
                    "company": "ASL Aviation Holdings", "title": title[:300],
                    "location": f"{loc_match.group(1)}, Ireland",
                    "posted_text": posted_text, "posted_days_ago": posted_days,
                    "employment_type": normalize_employment_type(None, title),
                    "url": href, "source": "asl_aviation_cezanne_browser",
                    "visa_sponsorship": sponsorship, "visa_snippet": snippet,
                }
            browser.close()
    except Exception as e:
        print(f"      [asl-aviation] browser scrape failed: {e}")
    print(f"      [asl-aviation] {len(results)} unique Ireland jobs accumulated")
    return list(results.values())



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
PROBE_WORKERS = int(os.environ.get("PROBE_WORKERS", "12"))
WORKDAY_WORKERS = int(os.environ.get("WORKDAY_WORKERS", "3"))  # deliberately small — a shared
# CDN/WAF across Workday tenants can rate-limit based on aggregate request volume from one IP,
# confirmed by the deliberate 1-second-per-company sleep this replaces; full-speed parallelism
# here risks making the already-stuck cluster of ~16 companies worse, not just faster

# Deliberately SEPARATE from PROBE_VERSION — these two caches were sharing
# one version number, which meant every ATS-platform fix (Workable, etc.)
# was also silently wiping the entire JobPosting structured-data cache and
# forcing an expensive full 342-company recheck for something completely
# unrelated. Only bump this when the JSON-LD scraping logic itself changes.
JSONLD_CACHE_VERSION = 1


def _probe_one_company_platform(entry):
    """Runs in a worker thread — creates its OWN session (requests.Session
    is not guaranteed safe to share across threads; each worker gets its
    own connection pool/cookie jar to avoid subtle race conditions).
    Returns (entry, platform, slug) — never mutates shared state directly,
    so the parallel phase has nothing to race on."""
    local_session = requests.Session()
    name = entry["company"]
    platform, slug = None, None

    if name in KNOWN_PHENOM_DOMAINS:
        known_domain, known_path = KNOWN_PHENOM_DOMAINS[name]
        ref_num, jobs_found = try_phenom_domain(known_domain, local_session, exact_path=known_path, verbose=False)
        if jobs_found:
            platform, slug = "phenom", f"{known_domain}|{ref_num}"
    if platform is None and name in KNOWN_WORKABLE_SLUGS:
        known_slug = KNOWN_WORKABLE_SLUGS[name]
        if try_workable(known_slug, local_session) is not None:
            platform, slug = "workable", known_slug
    if platform is None:
        for candidate in candidate_slugs(name):
            if try_greenhouse(candidate, local_session) is not None:
                platform, slug = "greenhouse", candidate
                break
            if try_lever(candidate, local_session) is not None:
                platform, slug = "lever", candidate
                break
            if try_smartrecruiters_probe(candidate, local_session) is not None:
                platform, slug = "smartrecruiters", candidate
                break
            if try_ashby(candidate, local_session) is not None:
                platform, slug = "ashby", candidate
                break
            if try_recruitee(candidate, local_session) is not None:
                platform, slug = "recruitee", candidate
                break
            if try_personio(candidate, local_session) is not None:
                platform, slug = "personio", candidate
                break
            if try_pinpoint(candidate, local_session) is not None:
                platform, slug = "pinpoint", candidate
                break
            if try_eightfold(candidate, local_session) is not None:
                platform, slug = "eightfold", candidate
                break
    return entry, platform, slug


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
    Confirmed real matches are never discarded, only re-checked misses.

    The expensive part — guessing a platform for companies with no cache
    hit yet — now runs in PARALLEL. This was previously fully sequential:
    up to 4 name-guesses x 7 platforms = up to 28 requests, one company
    at a time, for every one of ~500 manual companies. With 174 newly
    added companies this session that have never been probed before, this
    was very likely the real multi-hour bottleneck — not any individual
    company's code. Learned from an earlier threading mistake this
    session: each worker gets its own requests.Session (not guaranteed
    thread-safe to share), and no shared state is mutated from inside the
    parallel phase — results are merged back in afterward, single-threaded."""
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
    cache_hits_matched, cache_hits_none = 0, 0

    confirmed_platform_entries = []  # (entry, platform, slug) — ready to fetch jobs for
    needs_probe = []  # entries with no cache hit at all

    for entry in manual_companies:
        name = entry["company"]
        cached = cache.get(name)
        if cached and cached.get("platform") in known_platforms:
            confirmed_platform_entries.append((entry, cached["platform"], cached["slug"]))
            cache_hits_matched += 1
        elif cached and cached.get("platform") == "none":
            still_manual.append(entry)
            cache_hits_none += 1
        else:
            needs_probe.append(entry)

    freshly_probed = len(needs_probe)
    print(f"  {cache_hits_matched} companies served from cache (confirmed platform), "
          f"{cache_hits_none} served from cache (confirmed no match), "
          f"{freshly_probed} need a fresh probe this run"
          f"{' — running in parallel' if freshly_probed else ''}...")

    if needs_probe:
        pool = ThreadPoolExecutor(max_workers=PROBE_WORKERS)
        try:
            futures = {pool.submit(_probe_one_company_platform, e): e for e in needs_probe}
            done_count = 0
            for fut in futures:
                entry = futures[fut]
                try:
                    _, platform, slug = fut.result(timeout=90)
                except FuturesTimeoutError:
                    print(f"      [probe] {entry['company']}: timed out after 90s, treating as no match")
                    platform, slug = None, None
                except Exception as exc:
                    print(f"      [probe] {entry['company']}: failed ({exc}), treating as no match")
                    platform, slug = None, None

                name = entry["company"]
                cache[name] = {"platform": platform or "none", "slug": slug}
                if platform is None:
                    still_manual.append(entry)
                else:
                    confirmed_platform_entries.append((entry, platform, slug))

                done_count += 1
                if done_count % 50 == 0:
                    print(f"      [probe] {done_count}/{freshly_probed} companies checked so far...")
        finally:
            pool.shutdown(wait=False)

    # Fetch confirmed platform boards concurrently. Each worker gets its own
    # requests.Session, so there is no shared-session race and the per-company
    # normalization logic/results are unchanged. This removes a large serial
    # bottleneck when many companies have already been matched in the cache.
    def _fetch_confirmed(entry_platform_slug):
        entry, platform, slug = entry_platform_slug
        local_session = requests.Session()
        name, url = entry["company"], entry["url"]
        company_jobs = []
        if platform == "greenhouse":
            jobs = try_greenhouse(slug, local_session) or []
            for job in jobs:
                norm = normalize_greenhouse_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "lever":
            jobs = try_lever(slug, local_session) or []
            for job in jobs:
                norm = normalize_lever_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "smartrecruiters":
            jobs = try_smartrecruiters(slug, local_session) or []
            for job in jobs:
                norm = normalize_smartrecruiters_job(name, job, slug, local_session, fetch_descriptions)
                if norm:
                    company_jobs.append(norm)
        elif platform == "ashby":
            jobs = try_ashby(slug, local_session) or []
            for job in jobs:
                norm = normalize_ashby_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "recruitee":
            jobs = try_recruitee(slug, local_session) or []
            for job in jobs:
                norm = normalize_recruitee_job(name, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "personio":
            jobs = try_personio(slug, local_session) or []
            for job in jobs:
                norm = normalize_personio_job(name, slug, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "pinpoint":
            jobs = try_pinpoint(slug, local_session) or []
            for job in jobs:
                norm = normalize_pinpoint_job(name, slug, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "eightfold":
            jobs = try_eightfold(slug, local_session) or []
            for job in jobs:
                norm = normalize_eightfold_job(name, slug, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "phenom":
            domain, ref_num = slug.split("|", 1)
            jobs = fetch_phenom_jobs_by_refnum(domain, ref_num, local_session)
            for job in jobs:
                norm = normalize_phenom_job(name, domain, job)
                if norm:
                    company_jobs.append(norm)
        elif platform == "workable":
            jobs = try_workable(slug, local_session) or []
            for job in jobs:
                norm = normalize_workable_job(name, job)
                if norm:
                    company_jobs.append(norm)
        return entry, platform, slug, company_jobs

    if confirmed_platform_entries:
        print(f"  Fetching {len(confirmed_platform_entries)} confirmed ATS boards in parallel "
              f"(plain HTTP requests, not browsers — using higher concurrency)...")
        pool = ThreadPoolExecutor(max_workers=min(PROBE_WORKERS, len(confirmed_platform_entries)))
        try:
            future_map = {
                pool.submit(_fetch_confirmed, item): item
                for item in confirmed_platform_entries
            }
            for fut, original in future_map.items():
                try:
                    entry, platform, slug, company_jobs = fut.result(timeout=30)
                except FuturesTimeoutError:
                    entry, platform, slug = original
                    company_jobs = []
                    print(f"      [ATS] {entry['company']}: timed out after 30s")
                except Exception as exc:
                    # Preserve the existing behavior for a failed board: it remains manual.
                    entry, platform, slug = original
                    company_jobs = []
                    print(f"      [ATS] {entry['company']}: fetch failed ({exc})")
                name, url = entry["company"], entry["url"]
                if company_jobs:
                    discovered_jobs.extend(company_jobs)
                else:
                    still_manual.append({"company": name, "url": url,
                                          "platform": f"{platform} (no Ireland postings found right now)"})
        finally:
            pool.shutdown(wait=False)

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
        "cognizant": lambda: scrape_cognizant_ireland(session),
        "pepsico": lambda: scrape_pepsico_ireland(session),
        "esb": lambda: scrape_esb_ireland(session),
        "irish rail": lambda: scrape_irish_rail_ireland(session),
        "avolon": lambda: scrape_avolon_ireland(session),
        "bloomberg": lambda: scrape_bloomberg_ireland(session),
        "amcs": lambda: scrape_amcs_ireland(session),
        "dawn meats": lambda: scrape_dawn_meats_ireland(session),
        "auxilion": lambda: scrape_auxilion_ireland(session),
        "biomarin": lambda: scrape_biomarin_ireland(session),
        "asl aviation": lambda: scrape_asl_aviation_ireland(session),
        "aib": lambda: scrape_aib_ireland(session),
        "bnp paribas": lambda: scrape_bnp_paribas_ireland(session),
        "blackrock": lambda: scrape_blackrock_ireland(session),
        "bank of ireland": lambda: scrape_bank_of_ireland_direct(session),
        "ing": lambda: scrape_ing_ireland(session),
        "deutsche bank": lambda: scrape_deutsche_bank_ireland(session),
        "arup": lambda: scrape_arup_ireland(session),
        "central bank": lambda: scrape_central_bank_ireland_direct(session),
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

    priority_sheet2_names = {
        "axa ireland", "aldi ireland", "alvarez & marsal", "aviva ireland", "bdo ireland",
        "bny mellon", "bain & company", "baker tilly ireland", "boston consulting group (bcg)",
        "cantor fitzgerald ireland", "capgemini", "coca-cola hbc ireland", "databricks", "davy",
        "dunnes stores", "dynatrace", "fbd insurance", "fti consulting", "factset",
        "fidelity investments", "fiserv", "fitch ratings", "forvis mazars ireland",
        "glanbia / tirlán", "goldman sachs",
    }
    if row["company_name"].strip().lower() in priority_sheet2_names:
        print(f"Matched Sheet 2 priority coverage (generic Ireland-first browser fallback).\n")
        jobs = scrape_priority_sheet2_generic(row["company_name"], url, session)
        for j in jobs:
            normalize_posted_age(j)
        print(f"\n=== RESULT: {len(jobs)} Ireland postings found for '{name}' ===")
        for j in jobs[:10]:
            print(f"  - {j['title']} | {j['location']} | posted_days_ago={j['posted_days_ago']} | {j['url']}")
        if len(jobs) > 10:
            print(f"  ... and {len(jobs) - 10} more")
        return

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
    live_jobs, manual_check, errors = [], [], []

    workday_rows = [row for row in companies if classify_url(row["career_url"].strip()) == "workday"]
    other_rows = [row for row in companies if classify_url(row["career_url"].strip()) != "workday"]

    print(f"\n  Fetching {len(workday_rows)} Workday companies (modest parallelism — kept small "
          f"deliberately, since a shared CDN/WAF across Workday tenants can rate-limit based on "
          f"aggregate request volume from one IP, not just per-tenant. Full-speed parallelism here "
          f"risks making that worse, not just faster)...")

    def _fetch_one_workday(row):
        name = row["company_name"].strip()
        url = row["career_url"].strip()
        local_workday_session = make_workday_session()
        jobs, err = fetch_workday_jobs(name, url, local_workday_session, fetch_descriptions=not args.no_descriptions)
        return name, url, jobs, err

    if workday_rows:
        pool = ThreadPoolExecutor(max_workers=min(WORKDAY_WORKERS, len(workday_rows)))
        try:
            futures = {pool.submit(_fetch_one_workday, row): row for row in workday_rows}
            done = 0
            for fut in futures:
                row = futures[fut]
                try:
                    name, url, jobs, err = fut.result(timeout=120)
                except FuturesTimeoutError:
                    name, url = row["company_name"].strip(), row["career_url"].strip()
                    jobs, err = [], "timed out after 120s"
                except Exception as exc:
                    name, url = row["company_name"].strip(), row["career_url"].strip()
                    jobs, err = [], str(exc)
                live_jobs.extend(jobs)
                if err:
                    errors.append(err)
                done += 1
                print(f"      [workday {done}/{len(workday_rows)}] {name} -> {len(jobs)} Ireland postings")
                if not jobs:
                    reason = "fetch error, verify manually" if err else "no Ireland postings found right now"
                    manual_check.append({"company": name, "url": url, "platform": f"workday ({reason})"})
        finally:
            pool.shutdown(wait=False)

    for row in other_rows:
        name = row["company_name"].strip()
        url = row["career_url"].strip()
        kind = classify_url(url)
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

    # ------------------------------------------------------------------
    # All dedicated company scrapers run CONCURRENTLY, not one after
    # another — this is the real runtime fix. Timeout is enforced via
    # future.result(timeout=X), NOT signal.alarm() — that only works in
    # the main thread and crashed every single one of these companies the
    # first time this was parallelized. Confirmed fixed this time with a
    # direct reproduction test before shipping.
    # ------------------------------------------------------------------
    dedicated_company_specs = [
        ("prefix", "apple", scrape_apple_ireland, 180, "direct HTML scrape"),
        ("exact", "google", scrape_google_ireland, 240, "real browser automation"),
        ("prefix", "amazon", scrape_amazon_ireland, 180, "internal jobs search endpoint"),
        ("prefix", "meta", scrape_meta_ireland, 240, "real browser automation"),
        ("prefix", "ey", scrape_ey_ireland, 240, "SuccessFactors via browser automation"),
        ("prefix", "kpmg", scrape_kpmg_ireland, 240, "Avature via browser automation"),
        ("prefix", "tiktok", scrape_tiktok_ireland, 240, "searchable board"),
        ("exact", "boston scientific", scrape_boston_scientific_ireland, 240, "SuccessFactors, office pages"),
        ("exact", "johnson & johnson", scrape_jnj_ireland, 240, "first-party board"),
        ("exact", "johnson controls", scrape_johnson_controls_ireland, 240, "Algolia-style board"),
        ("exact", "hsbc ireland", scrape_hsbc_ireland, 240, "SuccessFactors"),
        ("exact", "dxc technology", scrape_dxc_ireland, 240, "bypasses stuck Workday tenant"),
        ("exact", "grant thornton ireland", scrape_grant_thornton_direct, 240, "real current careers site"),
        ("exact", "nvidia", scrape_nvidia_ireland, 240, "public Eightfold feed"),
        ("exact", "aon", scrape_aon_ireland, 240, "first-party jobs.aon.com"),
        ("exact", "eaton", scrape_eaton_ireland, 240, "first-party jobs.eaton.com"),
        ("exact", "cognizant", scrape_cognizant_ireland, 240, "verifies Ireland per job detail page"),
        ("exact", "aib (allied irish banks)", scrape_aib_ireland, 240, "filtered against UK-only postings"),
        ("exact", "bnp paribas ireland", scrape_bnp_paribas_ireland, 240, "first-party Dublin jobs page"),
        ("exact", "blackrock", scrape_blackrock_ireland, 240, "Phenom platform"),
        ("exact", "bank of ireland", scrape_bank_of_ireland_direct, 240, "first-party jobs board"),
        ("exact", "ing", scrape_ing_ireland, 240, "Phenom platform"),
        ("exact", "deutsche bank", scrape_deutsche_bank_ireland, 240, "first-party roles search"),
        ("exact", "arup", scrape_arup_ireland, 240, "no browser needed"),
        ("exact", "central bank of ireland", scrape_central_bank_ireland_direct, 240, "Candidate Manager board"),
        ("exact", "microsoft", scrape_microsoft_ireland, 240, "Dublin/Ireland rendered search"),
        ("exact", "citi", scrape_citi_ireland, 240, "Dublin paginated search"),
        ("exact", "red hat", scrape_red_hat_ireland, 240, "rendered Ireland search"),
        ("exact", "netflix", scrape_netflix_ireland, 120, "Eightfold, custom-branded domain"),
        ("exact", "irish life", scrape_irish_life_ireland, 180, "real careers board"),
        ("exact", "ups ireland", scrape_ups_ireland, 180, "real jobs board"),
        ("exact", "three ireland", scrape_three_ireland_direct, 180, "Cornerstone OnDemand"),
        ("exact", "aiven", scrape_aiven_ireland, 60, "lightweight, no browser needed"),
        ("exact", "huawei", scrape_huawei_ireland, 180, "Teamtailor board"),
        ("exact", "ge healthcare", scrape_ge_healthcare_ireland, 180, "Phenom platform"),
        ("exact", "exl", scrape_exl_ireland, 180, "Oracle Recruiting Cloud"),
        ("exact", "ntt data", scrape_ntt_data_ireland, 180, "SuccessFactors"),
        ("exact", "guidewire", scrape_guidewire_ireland, 180, "official careers listing"),
        ("exact", "hcltech", scrape_hcltech_ireland, 180, "Ireland-filtered search"),
        ("exact", "allianz", scrape_allianz_ireland, 180, "real careers page"),
        ("exact", "siemens", scrape_siemens_ireland, 180, "Avature-powered search"),
        ("exact", "pepsico", scrape_pepsico_ireland, 180, "official careers search"),
    ]

    task_list = []
    matched_entries = {}
    for match_type, key, scraper_fn, timeout_s, description in dedicated_company_specs:
        if match_type == "exact":
            entry = next((c for c in manual_check if c["company"].strip().lower() == key), None)
        else:
            entry = next((c for c in manual_check if c["company"].strip().lower().startswith(key)), None)
        if not entry:
            continue
        company_name = entry["company"]
        matched_entries[company_name] = entry

        def make_task(fn=scraper_fn, name=company_name):
            return lambda: cached_browser_scrape(browser_cache, name, lambda: fn(session), 0, name)

        actual_timeout = effective_timeout(browser_cache, company_name, timeout_s)
        if actual_timeout < timeout_s:
            failures = (browser_cache.get(company_name) or {}).get("consecutive_failures", 0)
            print(f"  [{company_name}] {failures} consecutive failures — reduced budget "
                  f"{timeout_s}s -> {actual_timeout}s this run")
        task_list.append((key, company_name, make_task(), actual_timeout))

    oracle_cx_targets = [
        ("jpmorgan chase", "JPMorgan Chase", "https://jpmc.fa.oraclecloud.com", "CX_1001"),
        ("oracle", "Oracle", "https://eeho.fa.us2.oraclecloud.com", "CX_1"),
    ]
    for exact_name, display_name, host, site_number in oracle_cx_targets:
        entry = next((c for c in manual_check if c["company"].strip().lower() == exact_name), None)
        if not entry:
            continue
        company_name = entry["company"]
        matched_entries[company_name] = entry

        def make_oracle_task(h=host, s=site_number, name=company_name):
            return lambda: cached_browser_scrape(
                browser_cache, name, lambda: scrape_oracle_candidate_experience(name, h, s, session), 0, name)

        task_list.append(("oracle_cx", company_name, make_oracle_task(), 180))

    # 9 new companies, all lightweight (plain HTTP requests, no browser) —
    # deliberately chosen this way to avoid adding real cost to runtime.
    lightweight_specs = [
        ("esb", "ESB", scrape_esb_ireland, 60),
        ("irish rail", "Irish Rail (Iarnród Éireann)", scrape_irish_rail_ireland, 45),
        ("avolon", "Avolon", scrape_avolon_ireland, 60),
        ("bloomberg", "Bloomberg", scrape_bloomberg_ireland, 90),
        ("amcs group", "AMCS Group", scrape_amcs_ireland, 90),
        ("dawn meats", "Dawn Meats", scrape_dawn_meats_ireland, 60),
        ("auxilion", "Auxilion", scrape_auxilion_ireland, 60),
        ("biomarin", "BioMarin", scrape_biomarin_ireland, 90),
        ("asl aviation holdings", "ASL Aviation Holdings", scrape_asl_aviation_ireland, 150),
    ]
    for key, display_name, scraper_fn, base_timeout in lightweight_specs:
        entry = next((c for c in manual_check if c["company"].strip().lower() == key), None)
        if not entry:
            continue
        company_name = entry["company"]
        matched_entries[company_name] = entry

        def make_light_task(fn=scraper_fn, name=company_name):
            return lambda: cached_browser_scrape(browser_cache, name, lambda: fn(session), 0, name)

        actual_timeout = effective_timeout(browser_cache, company_name, base_timeout)
        task_list.append((key, company_name, make_light_task(), actual_timeout))

    # SHEET 2 PRIORITY COVERAGE
    # These are the first 25 Tier-1 companies from the user's
    # "2. Not Live Yet - Keep" sheet that do not already have a dedicated
    # scraper above. They get an Ireland-first browser fallback so they can
    # move from manual_check into the live job list when the career page
    # exposes current Ireland vacancies.
    PRIORITY_SHEET2_COMPANIES = {
        "axa ireland",
        "aldi ireland",
        "alvarez & marsal",
        "aviva ireland",
        "bdo ireland",
        "bny mellon",
        "bain & company",
        "baker tilly ireland",
        "boston consulting group (bcg)",
        "cantor fitzgerald ireland",
        "capgemini",
        "coca-cola hbc ireland",
        "databricks",
        "davy",
        "dunnes stores",
        "dynatrace",
        "fbd insurance",
        "fti consulting",
        "factset",
        "fidelity investments",
        "fiserv",
        "fitch ratings",
        "forvis mazars ireland",
        "glanbia / tirlán",
        "goldman sachs",
    }

    priority_entries = [
        entry for entry in manual_check
        if entry["company"].strip().lower() in PRIORITY_SHEET2_COMPANIES
    ]
    for entry in priority_entries:
        company_name = entry["company"].strip()
        matched_entries[company_name] = entry

        def make_priority_task(name=company_name, u=entry["url"]):
            return lambda: cached_browser_scrape(
                browser_cache,
                name,
                lambda: scrape_priority_sheet2_generic(name, u, session),
                0,
                name,
            )

        actual_timeout = effective_timeout(browser_cache, company_name, 150)
        task_list.append(("sheet2_priority", company_name, make_priority_task(), actual_timeout))

    print(
        f"\n=== Sheet 2 priority coverage: {len(priority_entries)}/25 selected companies "
        f"queued for Ireland browser fallback ==="
    )
    if priority_entries:
        print("  -> " + ", ".join(e["company"] for e in priority_entries))


    print(f"\n=== Running {len(task_list)} dedicated company scrapers in parallel "
          f"(up to {PARALLEL_WORKERS} at once) ===")
    parallel_results, parallel_errors = run_company_tasks_in_parallel(task_list)

    for company_name, jobs in parallel_results:
        if jobs:
            for job in jobs:
                job["company"] = company_name
            live_jobs.extend(jobs)
            entry = matched_entries.get(company_name)
            if entry is not None:
                manual_check = [c for c in manual_check if c is not entry]
    if parallel_errors:
        errors.extend(parallel_errors)

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
    # JSON-LD checks are independent per company. Run only the actual network
    # checks concurrently; cache bookkeeping remains single-threaded so output
    # and cache semantics stay unchanged.
    jsonld_tasks = []
    for entry in manual_check:
        name = entry["company"]
        cached = jsonld_cache.get(name)
        if cached is not None:
            if cached.get("has_data"):
                jsonld_tasks.append((entry, True))
            else:
                still_manual_after_jsonld.append(entry)
            continue

        if not entry.get("url"):
            still_manual_after_jsonld.append(entry)
            jsonld_cache[name] = {"has_data": False}
            continue

        jsonld_checked_this_run += 1
        jsonld_tasks.append((entry, False))

    def _run_jsonld(item):
        entry, had_cached_data = item
        local_session = requests.Session()
        return entry, had_cached_data, scrape_jsonld_jobpostings(
            entry["url"], entry["company"], local_session
        )

    if jsonld_tasks:
        print(f"  Checking {len(jsonld_tasks)} companies for JobPosting structured data "
              f"(plain HTTP requests, not browsers — using higher concurrency than the "
              f"dedicated-company phase)...")
        pool = ThreadPoolExecutor(max_workers=min(PROBE_WORKERS, len(jsonld_tasks)))
        try:
            future_map = {pool.submit(_run_jsonld, item): item for item in jsonld_tasks}
            done = 0
            for fut, item in future_map.items():
                entry = item[0]
                try:
                    entry, had_cached_data, jsonld_jobs = fut.result(timeout=20)
                except FuturesTimeoutError:
                    print(f"      [jsonld] {entry['company']}: timed out, treating as no data this run")
                    had_cached_data, jsonld_jobs = item[1], []
                except Exception as exc:
                    print(f"      [jsonld] {entry['company']}: failed ({exc})")
                    had_cached_data, jsonld_jobs = item[1], []
                name = entry["company"]
                done += 1
                if done % 50 == 0:
                    print(f"      [jsonld] {done}/{len(jsonld_tasks)} checked so far...")
                if jsonld_jobs:
                    live_jobs.extend(jsonld_jobs)
                    jsonld_found_companies.append(name)
                    jsonld_cache[name] = {"has_data": True}
                else:
                    still_manual_after_jsonld.append(entry)
                    # Preserve an existing positive cache only if the refresh
                    # failed to produce jobs; this matches the prior behavior
                    # of leaving the company manual for this run.
                    jsonld_cache[name] = {"has_data": had_cached_data}
        finally:
            pool.shutdown(wait=False)

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
    print("\n=== Forcing process exit now — any abandoned background thread from a "
          "timed-out company (confirmed via real log evidence: DXC kept printing "
          "output minutes after 'Done.' and the final summary) will NOT be waited "
          "on. All files are already safely written by this point. ===")
    sys.stdout.flush()
    os._exit(0)
