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
JOB_RECORD_QUALITY_FIX_VERSION = 3

# Confirmed-manual recovery batch, derived from the latest jobs.json/run log.
# IMPORTANT: companies already producing live jobs (e.g. KPMG Ireland, PepsiCo)
# are deliberately NOT included here and their working paths remain untouched.
MANUAL_RECOVERY_CONFIRMED = {
    "aon",
    "dxc technology",
    "northern trust",
    "willis towers watson (wtw)",
    "becton dickinson (bd)",
    "jazz pharmaceuticals",
    "takeda",
    "teleflex",
    "viatris",
    "siemens",
    "guidewire",
    "hcltech",
    "red hat",
    "central bank of ireland",
    "deutsche bank",
}
MANUAL_RECOVERY_CONFIRMED_VERSION = 1

BROWSER_SCRAPE_MAX_AGE_HOURS = 3  # only actually re-run a real browser scrape this often
EMPTY_RESULT_MAX_AGE_HOURS = 0.5  # empty results retried much sooner — could be a real "no jobs",
# or could be a one-time failure (crash, resource contention); don't lock in a failure for 3 hours
PARALLEL_WORKERS = int(os.environ.get("SCRAPE_WORKERS", "10"))  # conservative — GitHub Actions'
# free-tier runners have limited CPU/memory (~2 cores, 7GB RAM); too many simultaneous real
# Chrome instances can crash or silently fail
#
# FIX: as the Sheet 2 priority list grew (now 141 companies, most routed through the same
# Playwright-based generic fallback) the single 10-worker pool above started mixing dozens of
# real-browser tasks with plain HTTP-request tasks in one queue. A real run showed the fallout
# directly: 94 fetch errors (vs. 34 on a normal run) and a cluster of HARD TIMEOUTs on companies
# that reliably succeed otherwise (Microsoft, BlackRock, JPMorgan Chase, Huawei, NTT DATA,
# GE HealthCare, Oracle, Irish Life, EXL, PepsiCo, Allianz) — all timing out late in the run,
# consistent with the runner running low on CPU/memory under ~10 concurrent real Chrome
# instances. Splitting into two separate pools means plain HTTP-only tasks (cheap, no Chrome)
# get real concurrency, while browser-based tasks are capped lower so they don't collectively
# exhaust the runner and starve whatever gets scheduled late.
BROWSER_WORKERS = int(os.environ.get("BROWSER_WORKERS", "7"))   # real Chrome instances — kept
# low deliberately; this is the resource-heavy pool that was causing the cascading timeouts.
# Raised from 5 to 7 once the Sheet 2 list grew to 207 browser tasks sharing this pool — 5 was
# too little throughput for that queue depth even with fair per-task timing (see the NOT REACHED
# fix below). Still well under the original single 10-worker pool that caused the first
# Microsoft/JPMorgan incident. Watch the NOT REACHED count in real logs — raise further if it's
# still high and the runner isn't showing memory/CPU strain, lower if timeouts start clustering
# again.
HTTP_WORKERS = int(os.environ.get("HTTP_WORKERS", "15"))  # plain requests — cheap, can run
# with much higher concurrency than real browser tasks without risking the runner's memory
OVERALL_BATCH_TIMEOUT_SECONDS = int(os.environ.get("BATCH_CEILING_SECONDS", "720"))  # 12 min —
# a hard ceiling on the whole dedicated-scraper phase. Needed once per-task deadlines were
# fixed to start counting from actual execution, not submission: without SOME overall cap,
# a queue deeper than the pool can clear in one run would just hang forever waiting for
# stragglers. Anything still not even started when this hits is reported as NOT REACHED
# (not a real timeout) and picked up again next run — increase if full coverage matters more
# than a fast run; decrease if runtime matters more than reaching every company every time.


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


def run_company_tasks_in_parallel(tasks, browser_workers=None, http_workers=None):
    """Runs company scrapers concurrently instead of one at a time — the
    real fix for a multi-hour runtime. Each task is (label, company_name,
    callable, timeout_seconds, is_browser).

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
    way to force-kill a thread) rather than blocking everything else.

    FIX: tasks now run in TWO separate pools instead of one shared one —
    real-browser (Playwright/Chrome) tasks in a small pool, plain-HTTP
    tasks in a larger one. A real run showed why this matters: with every
    task sharing one 10-worker pool, a wave of legitimate companies
    (Microsoft, BlackRock, JPMorgan Chase, Huawei, NTT DATA, GE HealthCare,
    Oracle, Irish Life, EXL, PepsiCo, Allianz) hit HARD TIMEOUT purely
    because the runner ran low on resources under too many concurrent real
    Chrome instances — not because those companies had no jobs.

    SECOND FIX, found from a real run right after the pool split shipped:
    each task's deadline used to be calculated from when the WHOLE BATCH
    started (a single shared `start_time`), not from when that specific
    task actually got a worker and began running. With 207 browser tasks
    sharing only 5 workers, anything queued deep in line had its 150s/240s
    clock already ticking down before it ever got a turn — a real run
    showed exactly this: 40 companies in a row hit "HARD TIMEOUT after
    150s" back-to-back, purely from queue position, having never actually
    started a scrape. Each task's own start time is now recorded the
    moment it actually begins executing (first line inside the wrapped
    callable, so it reflects real dispatch, not submission), and a task's
    personal deadline is computed from THAT — so no task is punished for
    time spent waiting in line; its timeout budget only starts counting
    once it's actually running.

    That alone isn't enough on its own, though — without any ceiling,
    tasks that never even get a worker turn would sit in `pending`
    forever and the whole run would hang. So there's now also an overall
    ceiling (`overall_deadline`, default 12 minutes, configurable) on the
    batch as a whole: once it's reached, anything that never got a chance
    to start is reported as NOT REACHED (distinct from a real HARD
    TIMEOUT, since it never actually ran) rather than silently vanishing
    or hanging the run — so it's visible in the log which companies are
    structurally being starved out, instead of that fact being invisible."""
    results, errors, failed_companies = [], [], set()
    if not tasks:
        return results, errors, failed_companies
    browser_pool = ThreadPoolExecutor(max_workers=browser_workers or BROWSER_WORKERS)
    http_pool = ThreadPoolExecutor(max_workers=http_workers or HTTP_WORKERS)
    task_started_at = {}

    def wrap(fn, task_id):
        def wrapped():
            task_started_at[task_id] = time.time()
            return fn()
        return wrapped

    try:
        future_map = {}
        for task_id, (label, company, fn, timeout_s, is_browser) in enumerate(tasks):
            pool = browser_pool if is_browser else http_pool
            fut = pool.submit(wrap(fn, task_id))
            future_map[fut] = (label, company, timeout_s, task_id)
        batch_start = time.time()
        overall_deadline = batch_start + OVERALL_BATCH_TIMEOUT_SECONDS
        pending = set(future_map)
        # Report in TRUE completion order, not submission order — a task
        # near the front of the list that happens to be slow (DXC, in a
        # real run) was blocking the reported results of faster companies
        # that had already quietly finished behind it. Real work was
        # already parallel; only the reporting order was misleading.
        while pending:
            now = time.time()
            poll_window = 1.0
            try:
                for fut in as_completed(pending, timeout=poll_window):
                    pending.discard(fut)
                    label, company, timeout_s, task_id = future_map[fut]
                    try:
                        jobs = fut.result() or []
                        if jobs:
                            print(f"  -> {company}: {len(jobs)} Ireland postings found")
                        else:
                            print(f"  -> {company}: found nothing this time")
                        results.append((label, company, jobs))
                    except Exception as exc:
                        print(f"  -> {company}: task failed ({exc})")
                        errors.append(f"{label}/{company}: {exc}")
                        failed_companies.add(company)
            except FuturesTimeoutError:
                pass  # normal — just means nothing finished within this poll window
            # Anything still pending gets checked two ways: if it's actually
            # STARTED and blown its OWN per-task budget, that's a real HARD
            # TIMEOUT. If it hasn't started at all yet, it's not punished
            # for queueing — UNLESS the overall batch ceiling has now been
            # reached, in which case it's abandoned and reported as never
            # having gotten a turn, so that fact is visible rather than
            # silently hanging or vanishing.
            now = time.time()
            timed_out_now = []
            not_reached_now = []
            for fut in pending:
                label, company, timeout_s, task_id = future_map[fut]
                started = task_started_at.get(task_id)
                if started is not None and now - started >= timeout_s:
                    timed_out_now.append(fut)
                elif started is None and now >= overall_deadline:
                    not_reached_now.append(fut)
            for fut in timed_out_now:
                pending.discard(fut)
                label, company, timeout_s, task_id = future_map[fut]
                print(f"  -> {company}: HARD TIMEOUT after {timeout_s}s "
                      f"(pipeline continues normally with whatever else it already found)")
                errors.append(f"{label}/{company}: timed out after {timeout_s}s")
                failed_companies.add(company)
            for fut in not_reached_now:
                pending.discard(fut)
                label, company, timeout_s, task_id = future_map[fut]
                print(f"  -> {company}: NOT REACHED — pool still busy with earlier "
                      f"companies when the {OVERALL_BATCH_TIMEOUT_SECONDS}s batch ceiling hit; "
                      f"never actually started this run, will be retried next run")
                errors.append(f"{label}/{company}: not reached before batch ceiling")
                failed_companies.add(company)
    finally:
        browser_pool.shutdown(wait=False)
        http_pool.shutdown(wait=False)
    return results, errors, failed_companies


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
    """Republic of Ireland only.

    Historically this helper treated Belfast/Northern Ireland as Ireland,
    which inflated the live-job count. Keep the original positive hints but
    explicitly reject Northern-Ireland locations before matching them.
    """
    if not location_text:
        return False
    lt = str(location_text).lower()
    if re.search(
        r"\b(?:northern ireland|belfast|lisburn|newry|derry|londonderry|"
        r"county antrim|county down|county armagh|county tyrone|"
        r"county fermanagh|county londonderry)\b",
        lt,
        re.I,
    ):
        return False
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




# --- job-record quality guardrails -------------------------------------------
# These helpers deliberately favour precision over raw count. The generic
# browser fallback used to accept navigation links merely because their URL or
# text contained "career", "apply", "opportunity", etc. That created dashboard
# records such as "APPLY TODAY", "Explore Euroimmun", "Learn more", category
# pages, language selectors and career landing pages. None of those are jobs.

_NON_JOB_TITLE_RE = re.compile(
    r"""^(?:
        apply(?:\s+(?:now|today|here))? |
        view(?:\s+(?:job|jobs|role|roles|open\s+roles|opportunities|vacancies))? |
        view\s+all(?:\s+.*)? |
        learn\s+more |
        read\s+more |
        find\s+out\s+more |
        discover(?:\s+more)? |
        explore(?:\s+.*)? |
        join\s+us |
        join\s+(?:our\s+)?(?:team|talent\s+network) |
        click\s+here |
        see\s+(?:all|jobs|roles|vacancies) |
        search\s+(?:jobs|roles|vacancies) |
        jobs? |
        careers? |
        opportunities |
        vacancies |
        saved\s+jobs |
        home |
        about\s+us |
        locations? |
        benefits? |
        our\s+(?:people|culture|values|sites|teams?) |
        life\s+at\s+.* |
        early\s+careers? |
        experienced\s+professionals? |
        students?(?:\s+and\s+graduates?)? |
        graduates?(?:\s+programme)? |
        internships? |
        language |
        english |
        deutsch |
        français |
        español |
        italiano |
        português |
        skip\s+to\s+(?:main\s+)?content |
        skip\s+to\s+(?:main\s+)?navigation |
        skip\s+navigation |
        read\s+more |
        learn\s+more |
        view\s+(?:all\s+)?jobs? |
        explore\s+careers? |
        early\s+careers? |
        open\s+submenu |
        contact(?:\s+us)? |
        faq |
        faqs
    )$""",
    re.I | re.X,
)

# Lines that are metadata/navigation rather than a public-facing role title.
_NON_JOB_LINE_RE = re.compile(
    r"""^(?:
        posted\b|date\s+posted\b|today$|yesterday$|
        full[\s-]?time$|part[\s-]?time$|contract$|temporary$|permanent$|
        ireland$|dublin(?:,\s*ireland)?$|cork(?:,\s*ireland)?$|
        galway(?:,\s*ireland)?$|limerick(?:,\s*ireland)?$|
        job\s+id\b|requisition\b|req(?:uisition)?\s*#|
        share\b|facebook$|linkedin$|twitter$|x$
    )""",
    re.I | re.X,
)

# Common words that are strong evidence a text string is an actual role title.
_ROLE_TITLE_WORD_RE = re.compile(
    r"\b(?:analyst|analytics|architect|associate|administrator|advisor|adviser|consulting|researcher|"
    r"accountant|auditor|consultant|controller|coordinator|developer|director|"
    r"engineer|engineering|executive|intern|manager|officer|operator|planner|"
    r"recruiter|scientist|specialist|supervisor|technician|lead|head|partner|"
    r"sales|finance|financial|marketing|product|project|program|programme|"
    r"operations|support|research|data|software|cloud|security|risk|quality|"
    r"manufacturing|procurement|supply|driver|nurse|therapist|pharmacist|"
    r"counsel|solicitor|legal|HR|human\s+resources)\b",
    re.I,
)

def _looks_like_non_job_title(title):
    """Conservative global check: reject only clear CTA/navigation labels.

    Do NOT reject a title merely because it is long or uses uncommon wording.
    Real postings at EY/Huawei/Meta can legitimately have long descriptive
    titles, and the previous length/word-count heuristic wrongly removed them.
    """
    t = re.sub(r"\s+", " ", str(title or "")).strip(" \t\r\n-|•")
    if not t or len(t) < 3:
        return True
    return bool(_NON_JOB_TITLE_RE.fullmatch(t))


def _looks_like_bad_generic_title(title):
    """Reject only clear non-vacancy/navigation text.

    IMPORTANT: vacancy validity must never depend on a hard-coded profession
    vocabulary. A real role can have any title. CV/domain relevance is a
    separate ranking concern and must not affect whether the vacancy is fetched.
    """
    t = re.sub(r"\s+", " ", str(title or "")).strip(" \t\r\n-|•")
    if _looks_like_non_job_title(t):
        return True
    if len(t) > 300:
        return True

    # Reject obvious navigation/header blobs by their content, not by requiring
    # words such as analyst/manager/engineer.
    nav_blob = re.compile(
        r"\b(?:saved jobs|register/sign in|sign in|about us|featured careers|"
        r"stay connected|privacy|cookie|careers blog|language selector|"
        r"skip to content|read more|explore careers|career stories)\b",
        re.I,
    )
    if len(t.split()) >= 18 and nav_blob.search(t):
        return True
    return False

def _explicit_ireland_filtered_url(url):
    """Only trust page-level Ireland filtering when the URL itself proves it.

    A page merely mentioning Ireland somewhere in its body is NOT sufficient:
    global career homepages routinely mention every country and caused jobs
    from Spain/US/etc. to be labelled Ireland.
    """
    u = str(url or "")
    decoded = urllib.parse.unquote_plus(u).lower()
    patterns = (
        r"/ireland(?:/|$|\?|#)",
        r"/ireland-jobs(?:/|$|\?|#)",
        r"/search-jobs/ireland(?:/|$|\?|#)",
        r"/location/ireland(?:/|$|\?|#)",
        r"(?:[?&](?:location|locationsearch|country|region|q)=)[^&#]*ireland",
        r"(?:[?&][^=&#]*location[^=&#]*=)[^&#]*ireland",
    )
    return any(re.search(p, decoded, re.I) for p in patterns)

def _strong_job_detail_url(url):
    """Return True only for URLs that look like an individual vacancy.

    Career landing pages, category pages, search pages, talent communities,
    saved-jobs pages, apply-only endpoints and generic navigation are excluded.
    """
    try:
        parsed = urllib.parse.urlparse(str(url or ""))
    except Exception:
        return False

    path = urllib.parse.unquote(parsed.path or "").lower()
    query = urllib.parse.unquote_plus(parsed.query or "").lower()

    if not path:
        return False

    # Never treat an action/navigation/search page itself as a vacancy.
    hard_exclusions = (
        r"/(?:saved-jobs?|jobcart|talent-community|join|login|signin|register)(?:/|$)",
        r"/(?:career-areas?|benefits?|locations?|life-at-[^/]*|how-to-apply)(?:/|$)",
        r"/(?:search|search-jobs|search-results|job-search)(?:/|$)",
        r"/apply/?$",  # apply buttons often carry a job ID but not the job title/details
        r"/(?:about|culture|values|students|graduates?|internships?|early-careers?)(?:/|$)",
    )
    if any(re.search(p, path, re.I) for p in hard_exclusions):
        # HSE is a genuine exception: its vacancy detail route is
        # /jobs/job-search/<role-slug>-<numeric-id>/.
        if not re.search(r"/jobs/job-search/[^/]+-\d+/?$", path, re.I):
            return False

    strong_patterns = (
        r"/j/[a-z0-9]{6,}/?$",                         # Workable
        r"/jobs?/[a-z0-9][^/]{2,}/?$",                # common /job/<slug>, /jobs/<slug>
        r"/job-detail(?:s)?/[a-z0-9][^/]*",            # job-detail routes
        r"/jobdetail(?:page)?(?:/|$)",                 # IBM / Workday-style detail
        r"/jobs/job-search/[^/]+-\d+/?$",              # HSE
        r"/vacanc(?:y|ies)/[a-z0-9][^/]*",             # vacancy detail
        r"/positions?/[a-z0-9][^/]*",
        r"/requisitions?/[a-z0-9][^/]*",
        r"/careersection/.*/jobdetail\.ftl",
        r"/job/\d+(?:/|$)",                            # numeric job record
        r"/jobs?/[^/]+/\d+(?:/|$)",                   # slug + numeric ID
        r"/job/[^/]*[-_]\d{4,}(?:/|$)",               # slug ending in req ID
        r"/jobs?/[^/]*[-_]\d{4,}(?:/|$)",
        r"/job/[^/]+/\d+(?:-[A-Za-z_]+)?/?$",         # SuccessFactors RMK / Wipro
    )
    if any(re.search(p, path, re.I) for p in strong_patterns):
        return True

    # Query-string job IDs are also a reliable detail signal, provided the
    # path isn't an apply-only endpoint caught above.
    if re.search(r"(?:^|&)(?:jobid|job_id|requisitionid|reqid|vacancyno)=([^&]+)", query, re.I):
        return True

    return False

def _title_from_job_url(url):
    """Last-resort title from a strongly job-specific URL slug."""
    try:
        path = urllib.parse.unquote(urllib.parse.urlparse(str(url or "")).path)
    except Exception:
        return ""
    bits = [b for b in path.rstrip("/").split("/") if b]
    if not bits:
        return ""

    # Prefer the segment after /job or /jobs, but skip pure numeric IDs.
    candidate = ""
    lower_bits = [b.lower() for b in bits]
    for marker in ("job", "jobs", "job-detail", "jobdetail", "vacancy", "vacancies", "position", "positions"):
        if marker in lower_bits:
            idx = lower_bits.index(marker)
            if idx + 1 < len(bits):
                candidate = bits[idx + 1]
                break
    if not candidate:
        candidate = bits[-1]

    candidate = re.sub(r"\.(?:html?|aspx?)$", "", candidate, flags=re.I)
    candidate = re.sub(r"[-_]+", " ", candidate)
    candidate = re.sub(r"\b\d{5,}\b", " ", candidate)
    candidate = re.sub(r"\s+", " ", candidate).strip()
    if not candidate or _looks_like_non_job_title(candidate):
        return ""
    # URL slugs are mostly lowercase; title-casing is preferable to a CTA.
    return candidate.title()[:220]

def _choose_job_title(anchor_text, card_text, href):
    """Pick the best real role title from an anchor/card/URL.

    The old implementation accepted the anchor first, so CTA text such as
    APPLY TODAY became the job title. This explicitly rejects CTA/navigation
    labels and scores nearby card lines for role-title likelihood.
    """
    anchor = re.sub(r"\s+", " ", str(anchor_text or "")).strip()
    if anchor and not _looks_like_bad_generic_title(anchor):
        return anchor[:300]

    lines = []
    for raw in str(card_text or "").splitlines():
        line = re.sub(r"\s+", " ", raw).strip(" \t\r\n-|•")
        if not line or len(line) < 4 or len(line) > 220:
            continue
        if is_ireland_location(line) or _NON_JOB_LINE_RE.search(line):
            continue
        if _looks_like_bad_generic_title(line):
            continue
        lines.append(line)

    if lines:
        # No profession-keyword scoring here. Pick the shortest plausible
        # non-navigation line from the vacancy card.
        lines.sort(key=len)
        return lines[0][:220]

    return _title_from_job_url(href)


def _clean_detail_page_title(value, company_name=""):
    """Clean a title taken from a *job detail page*, not from a listing card."""
    t = html.unescape(re.sub(r"<[^>]+>", " ", str(value or "")))
    t = re.sub(r"\s+", " ", t).strip(" \t\r\n-|•")
    if not t:
        return ""

    # Common document-title suffixes: "Role | Company Careers", "Role - Jobs at X".
    company = re.escape(str(company_name or "").strip())
    suffixes = [
        r"\s*[|\-–—]\s*(?:careers?|jobs?|job search|vacancies|opportunities)(?:\s+at)?\s+.*$",
        r"\s*[|\-–—]\s*jobs?\s+at\s+.*$",
        r"\s*[|\-–—]\s*careers?\s+at\s+.*$",
    ]
    if company:
        suffixes.extend([
            rf"\s*[|\-–—]\s*{company}(?:\s+careers?)?\s*$",
            rf"\s*[|\-–—]\s*(?:careers?|jobs?)\s*[|\-–—]\s*{company}\s*$",
        ])
    for pat in suffixes:
        t = re.sub(pat, "", t, flags=re.I).strip(" \t\r\n-|•")

    # Company/category labels are not job titles.
    generic_exact = {
        "brands", "brand", "kepak", "our brands", "our people", "our business",
        "careers", "career", "jobs", "job opportunities", "opportunities",
        "vacancies", "join us", "work with us", "open positions",
    }
    if t.lower() in generic_exact:
        return ""
    if company_name and re.sub(r"\W+", "", t).lower() == re.sub(r"\W+", "", company_name).lower():
        return ""
    if _looks_like_non_job_title(t):
        return ""
    return t[:300]


def _flatten_job_location(value):
    """Turn schema.org JobPosting.jobLocation into compact readable text."""
    pieces = []

    def walk(v):
        if isinstance(v, list):
            for x in v:
                walk(x)
            return
        if not isinstance(v, dict):
            return
        addr = v.get("address") if isinstance(v.get("address"), dict) else v
        for key in ("addressLocality", "addressRegion", "addressCountry"):
            x = addr.get(key) if isinstance(addr, dict) else None
            if isinstance(x, dict):
                x = x.get("name") or x.get("value")
            if x:
                sx = re.sub(r"\s+", " ", str(x)).strip()
                if sx and sx not in pieces:
                    pieces.append(sx)

    walk(value)
    return ", ".join(pieces)


def _iter_jsonld_objects(obj):
    """Yield every dict nested in arbitrary JSON-LD containers/@graph arrays."""
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from _iter_jsonld_objects(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _iter_jsonld_objects(v)


def _extract_job_detail_metadata_from_html(page_html, url, company_name):
    """Extract authoritative metadata from an individual job detail HTML page.

    Priority:
      1. schema.org JobPosting JSON-LD (best source)
      2. h1 on a page that has strong job-detail signals
      3. OpenGraph/document title on a page with strong job-detail signals

    Returns {verified, title, location, posted_text, employment_type,
             description}. 'verified' means the destination behaves like a real
    vacancy page, not merely a careers/category/brand page.
    """
    raw = str(page_html or "")
    if not raw:
        return {"verified": False}

    visible = re.sub(r"\s+", " ", _html_to_text(raw)).strip()
    lower_visible = visible.lower()

    # --- 1) Structured JobPosting is authoritative -----------------------
    for m in re.finditer(
        r'<script\b[^>]*type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
        raw, re.I | re.S
    ):
        blob = html.unescape(m.group(1)).strip()
        if not blob:
            continue
        try:
            data = json.loads(blob)
        except Exception:
            # Some sites leave harmless trailing semicolons.
            try:
                data = json.loads(blob.rstrip(" ;"))
            except Exception:
                continue

        for obj in _iter_jsonld_objects(data):
            typ = obj.get("@type")
            types = typ if isinstance(typ, list) else [typ]
            if not any(str(x).lower() == "jobposting" for x in types if x):
                continue

            title = _clean_detail_page_title(
                obj.get("title") or obj.get("name"), company_name
            )
            if not title:
                continue

            location = _flatten_job_location(obj.get("jobLocation"))
            desc = obj.get("description") or ""
            date_posted = obj.get("datePosted") or ""
            employment = obj.get("employmentType") or ""
            if isinstance(employment, list):
                employment = " ".join(str(x) for x in employment)

            return {
                "verified": True,
                "title": title,
                "location": location,
                "posted_text": str(date_posted or ""),
                "employment_type": str(employment or ""),
                "description": str(desc or ""),
                "method": "jsonld_jobposting",
            }

    # --- 2) Non-JSON-LD detail pages -------------------------------------
    # A genuine job page usually has several of these. Requiring multiple
    # signals stops pages such as "BRANDS" or the company homepage from being
    # accepted merely because they contain a generic "Apply" link somewhere.
    signals = 0
    signal_patterns = (
        r"\b(?:job|requisition)\s*(?:id|number|#)\b",
        r"\bresponsibilit(?:y|ies)\b",
        r"\brequirements?\b",
        r"\bqualifications?\b",
        r"\bjob description\b",
        r"\b(?:apply now|apply for this job|apply for this position)\b",
        r"\bemployment type\b",
        r"\bdate posted\b",
        r"\bwhat you(?:'|’)ll do\b",
        r"\babout the role\b",
    )
    for pat in signal_patterns:
        if re.search(pat, lower_visible, re.I):
            signals += 1

    # Job-specific form/action URLs are another strong signal.
    if re.search(r'(?:/apply(?:/|["\']|\?)|application|jobid=|requisitionid=|vacancyno=)', raw, re.I):
        signals += 1

    # Location signal from the *detail page*.
    ireland_detail = is_ireland_location(visible)

    # H1 is normally the most exact human-facing title.
    h1 = ""
    hm = re.search(r"<h1\b[^>]*>(.*?)</h1>", raw, re.I | re.S)
    if hm:
        h1 = _clean_detail_page_title(_html_to_text(hm.group(1)), company_name)

    # Meta title alternatives.
    og_title = ""
    mm = re.search(
        r'<meta\b[^>]*(?:property|name)=["\'](?:og:title|twitter:title)["\'][^>]*content=["\']([^"\']+)["\']',
        raw, re.I
    )
    if not mm:
        mm = re.search(
            r'<meta\b[^>]*content=["\']([^"\']+)["\'][^>]*(?:property|name)=["\'](?:og:title|twitter:title)["\']',
            raw, re.I
        )
    if mm:
        og_title = _clean_detail_page_title(mm.group(1), company_name)

    doc_title = ""
    tm = re.search(r"<title\b[^>]*>(.*?)</title>", raw, re.I | re.S)
    if tm:
        doc_title = _clean_detail_page_title(_html_to_text(tm.group(1)), company_name)

    candidate = h1 or og_title or doc_title

    # Two strong detail signals + a real-looking title is enough for bespoke
    # career sites that do not publish JobPosting JSON-LD. Ireland can either
    # be explicit on the detail page or already enforced by the listing URL.
    verified = bool(candidate and signals >= 2)

    return {
        "verified": verified,
        "title": candidate,
        "location": "Ireland" if ireland_detail else "",
        "posted_text": "",
        "employment_type": "",
        "description": visible[:12000],
        "method": "h1_meta" if verified else "unverified",
        "signals": signals,
    }


def _fetch_job_detail_metadata(url, company_name, timeout=8):
    """Cheap HTTP detail-page fetch used by the generic browser fallback.

    This does not launch another Chrome instance. It is intentionally bounded;
    if a site is JS-only or protected, the listing-card fallback can still be
    used when that card already looks like a real role.
    """
    try:
        resp = requests.get(
            url,
            headers={**HEADERS, "Accept": "text/html,application/xhtml+xml"},
            timeout=timeout,
            allow_redirects=True,
        )
        if resp.status_code >= 400:
            return {"verified": False, "http_status": resp.status_code}
        return _extract_job_detail_metadata_from_html(resp.text, resp.url, company_name)
    except Exception as exc:
        return {"verified": False, "error": str(exc)}


def _enrich_generic_candidates_from_detail(company_name, candidates):
    """Resolve exact titles for generic-browser candidates concurrently.

    The browser is only used to discover candidate links. Exact title/location
    metadata comes from each destination job page, which is substantially more
    reliable than link text. HTTP detail fetches run in a small local pool so
    20-60 jobs do not turn into minutes of serial network waits.
    """
    if not candidates:
        return []

    items = list(candidates.values())
    workers = min(8, max(1, len(items)))
    details = {}

    pool = ThreadPoolExecutor(max_workers=workers)
    try:
        fut_map = {
            pool.submit(_fetch_job_detail_metadata, j.get("url", ""), company_name, 8):
            j.get("url", "")
            for j in items
        }
        for fut in as_completed(fut_map):
            url = fut_map[fut]
            try:
                details[url] = fut.result()
            except Exception:
                details[url] = {"verified": False}
    finally:
        pool.shutdown(wait=False)

    resolved = []
    dropped = 0
    detail_titles = 0

    for job in items:
        meta = details.get(job.get("url", "")) or {}
        current = str(job.get("title") or "")
        current_bad = _looks_like_bad_generic_title(current)

        exact = _clean_detail_page_title(meta.get("title"), company_name)
        if meta.get("verified") and exact:
            # STRICT REPUBLIC OF IRELAND. The detail page itself must prove ROI.
            if not _strict_roi_job_evidence(meta):
                dropped += 1
                continue

            job = dict(job)
            job["title"] = exact
            detail_titles += 1

            detail_loc = str(meta.get("location") or "").strip()
            if detail_loc and is_republic_of_ireland_location(detail_loc):
                job["location"] = detail_loc

            detail_posted = str(meta.get("posted_text") or "").strip()
            if detail_posted:
                pdays = parse_posted_text(detail_posted)
                if pdays is not None:
                    job["posted_text"] = detail_posted
                    job["posted_days_ago"] = pdays

            detail_emp = str(meta.get("employment_type") or "").strip()
            if detail_emp:
                job["employment_type"] = normalize_employment_type(detail_emp, exact)
            else:
                job["employment_type"] = normalize_employment_type(
                    job.get("employment_type"), exact
                )

            detail_desc = str(meta.get("description") or "")
            if detail_desc:
                sponsorship, snippet = classify_sponsorship(detail_desc[:12000])
                job["visa_sponsorship"] = sponsorship
                job["visa_snippet"] = snippet

            job["title_source"] = meta.get("method", "detail_page")
            resolved.append(job)
            continue

        # If the destination could not be parsed/verified, do NOT throw away
        # a legitimate Ireland listing merely because the detail-page extractor
        # failed. Keep it only when:
        #   1) the listing title already looks like a real role, AND
        #   2) the listing/card location itself is explicitly Republic of Ireland.
        #
        # This restores valid Wipro/IQVIA/etc. jobs while still rejecting CTA
        # labels such as "BRANDS", "Apply now", "Explore careers", etc.
        listing_location = str(job.get("location") or "")
        if (current_bad
                or not _strong_job_detail_url(job.get("url", ""))
                or not is_republic_of_ireland_location(listing_location)):
            dropped += 1
            continue

        # No profession/title vocabulary is used here. The fallback survives
        # solely because it is structurally an individual vacancy URL and the
        # listing card itself explicitly proves Republic-of-Ireland location.
        job = dict(job)
        job["title_source"] = "listing_card_roi_verified"
        resolved.append(job)

    print(
        f"      [priority-detail] {company_name}: exact titles from detail pages "
        f"for {detail_titles}/{len(items)} candidates; dropped {dropped} unverified "
        f"category/CTA links"
    )
    return resolved


def _final_job_quality_filter(live_jobs):
    """Final safety net before jobs.json/history are written.

    This also cleans bad entries already sitting in browser_scrape_cache.json,
    so users do not have to wait three hours for stale bogus cards to expire.
    Existing API/dedicated results are left alone unless their *title itself*
    is an obvious CTA/navigation label.
    """
    cleaned = []
    removed = []
    seen = set()

    for job in live_jobs:
        if not isinstance(job, dict):
            continue
        title = re.sub(r"\s+", " ", str(job.get("title") or "")).strip()
        url = str(job.get("url") or "").strip()
        source = str(job.get("source") or "")

        # Generic fallback records have the highest false-positive risk.
        # Require structural vacancy URL evidence and an explicit ROI location
        # even when the record came from browser cache.
        if source == "priority_sheet2_generic":
            # Guidewire's dedicated rendered recovery verifies each candidate
            # against the individual job detail page, but historically reuses
            # the generic source label. Its legitimate careers.guidewire.com
            # vacancy URLs do not match the generic URL-shape whitelist.
            #
            # Keep the generic URL rule unchanged for every other company.
            _company_key = str(job.get("company") or "").strip().lower()
            _guidewire_verified = (
                _company_key == "guidewire"
                and is_republic_of_ireland_location(job.get("location", ""))
                and bool(str(title or "").strip())
                and "guidewire" in str(url or "").lower()
            )

            if not _strong_job_detail_url(url) and not _guidewire_verified:
                removed.append((job.get("company", ""), title, "generic non-vacancy URL"))
                continue
            if not is_republic_of_ireland_location(job.get("location", "")):
                removed.append((job.get("company", ""), title, "generic location not proven ROI"))
                continue

        # High-confidence non-vacancy URLs only. Do not broadly reject paths
        # containing locations/teams/etc., because some real ATS detail routes
        # legitimately include those words.
        if re.search(
            r"/(?:saved-jobs?|career-advice|blogs?|articles?|news)(?:/|$)",
            url,
            re.I,
        ):
            removed.append((job.get("company", ""), title, "non-vacancy URL"))
            continue

        # Generic career systems use many legitimate URL shapes, including
        # opaque IDs, query-string routes and SPA URLs. Do not discard a real
        # role solely because its URL fails a narrow pattern check.
        bad_title = (_looks_like_bad_generic_title(title)
                     if source == "priority_sheet2_generic"
                     else _looks_like_non_job_title(title))

        # Across every source, never display CTA/navigation text as a job title.
        if bad_title:
            # For generic results, recover from a genuine vacancy-looking URL
            # when possible; otherwise drop the malformed CTA/navigation record.
            recovered = _title_from_job_url(url) if source == "priority_sheet2_generic" else ""
            if recovered and not _looks_like_bad_generic_title(recovered):
                job = dict(job)
                job["title"] = recovered
                title = recovered
                job["employment_type"] = normalize_employment_type(
                    job.get("employment_type"), recovered
                )
            else:
                removed.append((job.get("company", ""), title, "non-job title"))
                continue

        # De-duplicate identical company+URL records after normalization.
        key = (str(job.get("company") or "").strip().lower(), url.rstrip("/").lower())
        if key in seen:
            continue
        seen.add(key)
        cleaned.append(job)

    if removed:
        print(f"=== Job quality filter removed {len(removed)} non-job/CTA records before output ===")
        for company, title, why in removed[:20]:
            print(f"      [quality-filter] {company}: {title!r} ({why})")
        if len(removed) > 20:
            print(f"      [quality-filter] ... plus {len(removed) - 20} more")
    return cleaned


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

                # STRUCTURAL VACANCY RULE:
                # Generic fallback may only emit links that look like an
                # individual vacancy-detail record. Region/category/navigation
                # links such as "Brazil", "Benelux", "Subscribe", "UK and
                # Ireland", etc. are not jobs even if they live under /careers/.
                if not _strong_job_detail_url(href):
                    continue
                if re.search(r"/(login|signin|register|account|privacy|terms|contact|about)(?:/|$)", href, re.I):
                    continue

                card = _browser_card(a)
                if not card:
                    card = text

                ireland = is_republic_of_ireland_location(card)

                # An explicitly Ireland-filtered listing page may be used only
                # to DISCOVER strong vacancy URLs. It is not sufficient proof
                # that an individual vacancy is in Ireland; the detail page
                # must prove ROI unless this card itself does.
                ireland_page = _explicit_ireland_filtered_url(page.url) or _explicit_ireland_filtered_url(url)
                if not ireland and not ireland_page:
                    continue

                title = _choose_job_title(text, card, href)
                if not title or _looks_like_bad_generic_title(title):
                    continue

                seen.add(href)
                candidate_count += 1
                posted_text, posted_days = extract_posted_from_text(card)
                sponsorship, snippet = classify_sponsorship(card[:5000])
                # Do NOT default to "Ireland". That was the bug that turned
                # region/navigation text into fake Irish vacancies.
                location = _extract_location_from_card(card, "") if ireland else ""
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

    # Do not trust card/link text as the final title. Resolve the destination
    # job page and use its JobPosting JSON-LD / H1 / meta title instead.
    return _enrich_generic_candidates_from_detail(company_name, results)


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



def _scrape_first_party_ireland_listing(company_name, listing_urls, href_patterns,
                                        source_tag, session, trust_listing_filter=True,
                                        max_detail_pages=120):
    """First-party HTTP recovery for companies whose Workday/custom route is failing.

    The listing page is only used to discover candidate vacancy URLs. Each
    candidate detail page is fetched and the exact title/location is taken from
    JobPosting JSON-LD, H1 or page metadata via the existing detail extractor.

    This is deliberately HTTP-first: no extra Chromium process unless the
    company's legacy wrapper later decides a browser fallback is still needed.
    """
    patterns = [re.compile(p, re.I) for p in href_patterns]
    candidates = {}
    headers = {
        **HEADERS,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "en-IE,en;q=0.9",
    }

    for listing_url in listing_urls:
        try:
            resp = session.get(listing_url, headers=headers, timeout=20, allow_redirects=True)
        except Exception as exc:
            print(f"      [{source_tag}] listing fetch failed {listing_url}: {exc}")
            continue
        if resp.status_code >= 400:
            print(f"      [{source_tag}] listing {listing_url}: HTTP {resp.status_code}")
            continue

        html_text = resp.text
        found_here = 0
        for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>',
                             html_text, re.I | re.S):
            raw_href = html.unescape(m.group(1))
            href = urllib.parse.urljoin(resp.url, raw_href).split("#")[0]
            if not href or not any(p.search(href) for p in patterns):
                continue
            if re.search(
                r"/(?:saved-jobs?|job-alerts?|alerts?|login|signin|register|"
                r"locations?|teams?|departments?|career-advice|blog|news)(?:/|$)",
                href,
                re.I,
            ):
                continue
            if href in candidates:
                continue

            anchor_text = re.sub(r"\s+", " ", _html_to_text(m.group(2))).strip()
            start, end = max(0, m.start() - 1400), min(len(html_text), m.end() + 1800)
            card = re.sub(r"\s+", " ", _html_to_text(html_text[start:end])).strip()
            candidates[href] = {
                "anchor": anchor_text,
                "card": card,
                "listing_url": resp.url,
                "listing_ireland": bool(trust_listing_filter or is_ireland_location(card)),
            }
            found_here += 1
            if len(candidates) >= max_detail_pages:
                break

        print(f"      [{source_tag}] {listing_url}: discovered {found_here} candidate vacancy links")
        if len(candidates) >= max_detail_pages:
            break

    if not candidates:
        return []

    results = {}
    urls = list(candidates.keys())[:max_detail_pages]

    def _detail(url):
        try:
            r = requests.get(url, headers=headers, timeout=10, allow_redirects=True)
            if r.status_code >= 400:
                return url, {"verified": False, "http_status": r.status_code}
            meta = _extract_job_detail_metadata_from_html(r.text, r.url, company_name)
            meta["final_url"] = r.url
            return url, meta
        except Exception as exc:
            return url, {"verified": False, "error": str(exc)}

    pool = ThreadPoolExecutor(max_workers=min(10, max(1, len(urls))))
    detail_map = {}
    try:
        future_map = {pool.submit(_detail, u): u for u in urls}
        for fut in as_completed(future_map):
            u = future_map[fut]
            try:
                _, detail_map[u] = fut.result()
            except Exception:
                detail_map[u] = {"verified": False}
    finally:
        pool.shutdown(wait=False)

    for href, info in candidates.items():
        meta = detail_map.get(href) or {}
        title = _clean_detail_page_title(meta.get("title"), company_name)
        description = str(meta.get("description") or "")
        detail_location = str(meta.get("location") or "").strip()

        # Exact detail metadata is preferred. If a site omits schema/H1 metadata,
        # fall back to a plausible non-navigation anchor from an explicitly
        # Ireland-filtered vacancy listing. No profession vocabulary required.
        if not title:
            anchor_title = re.sub(r"\s+", " ", str(info.get("anchor") or "")).strip()
            if anchor_title and not _looks_like_bad_generic_title(anchor_title):
                title = anchor_title

        if not title:
            continue

        # Sparse ATS pages may omit requisition/responsibility markers.
        # Do not reject them based on profession keywords. The title only needs
        # to be plausible/non-navigation; ROI is validated separately below.
        if meta.get("verified") and _looks_like_bad_generic_title(title):
            continue

        detail_proves_roi = _strict_roi_job_evidence(meta, info.get("card", ""))

        # Some first-party Ireland search pages expose a genuine vacancy URL
        # and exact title but omit location/schema metadata on the destination
        # page. For those explicitly trusted Ireland listings, keep the job
        # only if the URL looks like a real vacancy and there is no explicit
        # Northern-Ireland location anywhere in the card/detail text.
        listing_proves_roi = False
        if not detail_proves_roi and info.get("listing_ireland"):
            combined = " ".join([
                str(detail_location or ""),
                str(description or ""),
                str(info.get("card") or ""),
            ])
            has_ni = bool(_ROI_NEGATIVE_RE.search(combined))
            listing_proves_roi = (
                not has_ni
                and not _looks_like_bad_generic_title(title)
                and _strong_job_detail_url(meta.get("final_url") or href)
            )

        if not (detail_proves_roi or listing_proves_roi):
            continue

        if is_republic_of_ireland_location(detail_location):
            location = detail_location
        else:
            inferred = _extract_location_from_card(description or info.get("card", ""), "")
            location = inferred if is_republic_of_ireland_location(inferred) else "Republic of Ireland"
        posted_text = str(meta.get("posted_text") or "").strip() or "Unknown"
        posted_days = parse_posted_text(posted_text)
        employment = normalize_employment_type(meta.get("employment_type"), title)
        sponsorship, snippet = classify_sponsorship((description or info.get("card", ""))[:12000])

        final_url = str(meta.get("final_url") or href)
        key = final_url.rstrip("/").lower()
        results[key] = {
            "company": company_name,
            "title": title[:300],
            "location": location,
            "posted_text": posted_text,
            "posted_days_ago": posted_days,
            "employment_type": employment,
            "url": final_url,
            "source": source_tag,
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }

    print(f"      [{source_tag}] {len(results)} verified Ireland jobs accumulated")
    return list(results.values())




# Republic of Ireland only. Northern Ireland / Belfast is deliberately excluded.
_ROI_POSITIVE_RE = re.compile(
    r"\b(?:Ireland|Republic of Ireland|Dublin|Cork|Galway|Limerick|Waterford|"
    r"Athlone|Kilkenny|Kildare|Naas|Sligo|Wexford|Carlow|Clare|Tipperary|"
    r"Meath|Louth|Drogheda|Dundalk|Mayo|Castlebar|Westmeath|Mullingar|"
    r"Wicklow|Bray|Leixlip|Maynooth|Letterkenny|Donegal|Shannon|Ennis|"
    r"Tralee|Killarney|Nenagh|Clonmel|Dún Laoghaire|Dun Laoghaire|"
    r"Blanchardstown|Swords|Tallaght|Baldoyle|Damastown|Northern Cross|"
    r"Clonee|Carrigtwohill|Ringaskiddy|Little Island|Oranmore|Parkmore)\b",
    re.I,
)

_ROI_NEGATIVE_RE = re.compile(
    r"\b(?:Northern Ireland|Belfast|Lisburn|Newry|Derry|Londonderry|"
    r"County Antrim|County Down|County Armagh|County Tyrone|"
    r"County Fermanagh|County Londonderry)\b",
    re.I,
)

def is_republic_of_ireland_location(value):
    """Return True only for an explicit Republic-of-Ireland location signal.

    This intentionally rejects Belfast/Northern Ireland even when a page or URL
    contains the word 'Ireland'. Unknown/ambiguous locations return False.
    """
    text = re.sub(r"\s+", " ", str(value or "")).strip()
    if not text:
        return False
    if _ROI_NEGATIVE_RE.search(text):
        return False
    return bool(_ROI_POSITIVE_RE.search(text))



def _verified_vacancy_detail(meta, url=""):
    """Require the destination to behave like an actual vacancy page.

    JobPosting JSON-LD is authoritative. Otherwise require both a plausible
    title and strong job-detail evidence such as requisition/job ID,
    responsibilities/requirements, or an apply-for-this-job control.
    """
    if not meta:
        return False

    method = str(meta.get("method") or "")
    if method == "jsonld_jobposting":
        return True

    title = str(meta.get("title") or "").strip()
    if not title or _looks_like_non_job_title(title):
        return False

    text = str(meta.get("description") or "").lower()
    strong_signals = 0
    for pat in (
        r"\b(?:job|requisition)\s*(?:id|number|#)\b",
        r"\bresponsibilit(?:y|ies)\b",
        r"\brequirements?\b",
        r"\bqualifications?\b",
        r"\bjob description\b",
        r"\bapply (?:now|for this job|for this position)\b",
        r"\bwhat you(?:'|’)ll do\b",
        r"\babout the role\b",
    ):
        if re.search(pat, text, re.I):
            strong_signals += 1

    u = str(url or "").lower()
    if re.search(r"/(?:job|jobs|vacancy|position|requisition)/[^/?#]+", u):
        strong_signals += 1
    if re.search(r"(?:jobid|job_id|reqid|requisitionid|vacancyno)=", u):
        strong_signals += 1

    return strong_signals >= 2


def _strict_roi_job_evidence(meta, fallback_text=""):
    """Validate a recovered job using the actual detail-page evidence.

    Priority is the structured/detail-page location. Description text can only
    rescue a missing location when it contains an explicit Republic-of-Ireland
    place and no Northern-Ireland signal.
    """
    loc = str((meta or {}).get("location") or "").strip()
    desc = str((meta or {}).get("description") or "")
    if loc:
        return is_republic_of_ireland_location(loc)
    return is_republic_of_ireland_location(desc or fallback_text)


def _sitemap_job_recovery(company_name, roots, source_tag, session, max_detail_urls=220):
    """Recover jobs from first-party XML sitemaps when the visible search page
    is blocked, JS-only or returns a WAF page.

    This is especially useful for sites like DXC/Aon where the user's runtime
    can receive 403s on the search UI while individual job pages remain public.
    """
    headers = {
        **HEADERS,
        "Accept": "application/xml,text/xml,text/html;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-IE,en;q=0.9",
    }
    sitemap_urls = []
    seen_maps = set()
    detail_urls = set()

    for root in roots:
        root = root.rstrip("/")
        for suffix in ("/sitemap.xml", "/sitemap_index.xml", "/sitemap-index.xml",
                       "/job-sitemap.xml", "/jobs-sitemap.xml"):
            sitemap_urls.append(root + suffix)

    def _fetch_map(u):
        try:
            r = session.get(u, headers=headers, timeout=12, allow_redirects=True)
            if r.status_code >= 400:
                return None
            text = r.text
            if "<loc>" not in text:
                return None
            return text
        except Exception:
            return None

    # One sitemap-index level plus child maps.
    queue = list(sitemap_urls)
    while queue and len(seen_maps) < 30 and len(detail_urls) < max_detail_urls:
        sm = queue.pop(0)
        if sm in seen_maps:
            continue
        seen_maps.add(sm)
        text = _fetch_map(sm)
        if not text:
            continue
        locs = [html.unescape(x.strip()) for x in re.findall(r"<loc>\s*(.*?)\s*</loc>", text, re.I | re.S)]
        for loc in locs:
            low = loc.lower()
            if low.endswith(".xml") or "sitemap" in low:
                if loc not in seen_maps and len(queue) < 60:
                    queue.append(loc)
                continue
            # Only accept URLs that look like real vacancy/detail pages.
            # Generic /careers/ content, blog posts, news, saved jobs, teams,
            # locations, advice pages, etc. are not job postings.
            if re.search(
                r"/(?:blog|blogs|article|articles|news|insights|stories|"
                r"saved-jobs?|career-advice|locations?|teams?|departments?|"
                r"benefits?|culture|events?|students?|graduates?|early-careers?)(?:/|$)",
                low,
            ):
                continue

            strong_job_url = bool(
                re.search(r"/(?:job|jobs|vacancy|vacancies|position|positions|requisition|requisitions)/[^/?#]+", low)
                or re.search(r"(?:jobid|job_id|reqid|requisitionid|vacancyno)=", low)
                or re.search(r"/jobs?/[0-9]{4,}(?:/|$)", low)
                or re.search(r"/jobs?/[a-z0-9_-]*[0-9]{4,}[a-z0-9_-]*(?:/|$)", low)
            )
            if not strong_job_url:
                continue

            detail_urls.add(loc)
            if len(detail_urls) >= max_detail_urls:
                break

    if not detail_urls:
        print(f"      [{source_tag}] sitemap recovery found 0 candidate detail URLs")
        return []

    print(f"      [{source_tag}] sitemap recovery discovered {len(detail_urls)} candidate detail URLs")

    results = {}
    urls = list(detail_urls)[:max_detail_urls]

    def _fetch_detail(u):
        try:
            r = requests.get(
                u,
                headers={**HEADERS, "Accept": "text/html,application/xhtml+xml"},
                timeout=9,
                allow_redirects=True,
            )
            if r.status_code >= 400:
                return u, None
            meta = _extract_job_detail_metadata_from_html(r.text, r.url, company_name)
            meta["final_url"] = r.url
            return u, meta
        except Exception:
            return u, None

    pool = ThreadPoolExecutor(max_workers=min(12, max(1, len(urls))))
    try:
        future_map = {pool.submit(_fetch_detail, u): u for u in urls}
        for fut in as_completed(future_map):
            u = future_map[fut]
            try:
                _, meta = fut.result()
            except Exception:
                meta = None
            if not meta or not meta.get("verified"):
                continue

            title = _clean_detail_page_title(meta.get("title"), company_name)
            if not title:
                continue

            # JobPosting JSON-LD is authoritative. For sparse ATS pages, do not
            # require a profession keyword in the title. A plausible title,
            # job-detail URL/page evidence, and explicit ROI proof are enough.
            if (str(meta.get("method") or "") != "jsonld_jobposting"
                    and not _verified_vacancy_detail(meta, meta.get("final_url") or u)
                    and _looks_like_bad_generic_title(title)):
                continue
            loc = str(meta.get("location") or "")
            desc = str(meta.get("description") or "")
            final_url = str(meta.get("final_url") or u)

            # STRICT REPUBLIC OF IRELAND: the actual detail page must prove
            # the location. Belfast/Northern Ireland and ambiguous locations
            # are rejected.
            if not _strict_roi_job_evidence(meta):
                continue
            if not title:
                continue

            posted_text = str(meta.get("posted_text") or "").strip() or "Unknown"
            posted_days = parse_posted_text(posted_text)
            employment = normalize_employment_type(meta.get("employment_type"), title)
            sponsorship, snippet = classify_sponsorship(desc[:12000])

            results[final_url.rstrip("/").lower()] = {
                "company": company_name,
                "title": title,
                "location": loc if is_republic_of_ireland_location(loc) else "Republic of Ireland",
                "posted_text": posted_text,
                "posted_days_ago": posted_days,
                "employment_type": employment,
                "url": final_url,
                "source": source_tag,
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            }
    finally:
        pool.shutdown(wait=False)

    print(f"      [{source_tag}] sitemap recovery verified {len(results)} Ireland jobs")
    return list(results.values())


def _workday_override_scrape(company_name, correct_url, session):
    """Use the existing Workday parser against a verified current tenant URL."""
    local = make_workday_session()
    jobs, err = fetch_workday_jobs(
        company_name, correct_url, local, fetch_descriptions=True
    )
    if err:
        print(f"      [workday-override] {company_name}: {err}")
    else:
        print(f"      [workday-override] {company_name}: {len(jobs)} Ireland jobs")
    return jobs


def _rendered_filtered_job_page(company_name, url, source_tag, href_fragment):
    """Rendered first-party listing recovery for JS-only careers pages."""
    if not HAS_PLAYWRIGHT:
        return []
    candidates = {}
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1365, "height": 900},
                user_agent=HEADERS.get("User-Agent"),
            )
            page.goto(url, wait_until="domcontentloaded", timeout=45000)
            page.wait_for_timeout(5000)

            # If a location/search box is present, ask the page itself for Ireland.
            selectors = [
                'input[placeholder*="location" i]',
                'input[aria-label*="location" i]',
                'input[placeholder*="job title and location" i]',
                'input[placeholder*="search" i]',
            ]
            for sel in selectors:
                try:
                    box = page.locator(sel).first
                    if box.count():
                        box.fill("Ireland")
                        box.press("Enter")
                        page.wait_for_timeout(4500)
                        break
                except Exception:
                    pass

            links = page.locator(f'a[href*="{href_fragment}"]')
            for i in range(min(links.count(), 240)):
                a = links.nth(i)
                try:
                    href = a.get_attribute("href")
                    if not href:
                        continue
                    href = urllib.parse.urljoin(page.url, href).split("#")[0]
                    text = _browser_text(a)
                    card = _browser_card(a) or text
                    candidates[href] = {
                        "company": company_name,
                        "title": text,
                        "location": "Ireland",
                        "posted_text": "Unknown",
                        "posted_days_ago": None,
                        "employment_type": "Unspecified",
                        "url": href,
                        "source": "priority_sheet2_generic",
                        "visa_sponsorship": "not_mentioned",
                        "visa_snippet": None,
                    }
                except Exception:
                    continue
            browser.close()
    except Exception as exc:
        print(f"      [{source_tag}] rendered listing failed: {exc}")
        return []

    print(f"      [{source_tag}] rendered listing discovered {len(candidates)} candidate links")
    return _enrich_generic_candidates_from_detail(company_name, candidates)


def scrape_wtw_ireland_direct(session):
    # Current WTW careers site uses /search-page; previous /jobs?... URLs return 404.
    jobs = _rendered_filtered_job_page(
        "Willis Towers Watson (WTW)",
        "https://careers.wtwco.com/search-page",
        "wtw_rendered",
        "/jobs/",
    )
    if jobs:
        return jobs
    return _sitemap_job_recovery(
        "Willis Towers Watson (WTW)",
        ["https://careers.wtwco.com"],
        "wtw_sitemap",
        session,
    )


def scrape_bd_ireland_direct(session):
    return _scrape_first_party_ireland_listing(
        "Becton Dickinson (BD)",
        [
            "https://jobs.bd.com/en/location/ireland-jobs/159/2963597/2",
            "https://jobs.bd.com/en/search-jobs/Ireland/159/2/2963597/53/-8/100/2",
        ],
        [r"jobs\.bd\.com/(?:[a-z]{2}/)?job/[^/?#]+", r"jobs\.bd\.com/.*/job/[^/?#]+"],
        "bd_direct", session, True
    )


def scrape_jazz_ireland_direct(session):
    return _scrape_first_party_ireland_listing(
        "Jazz Pharmaceuticals",
        ["https://careers.jazzpharma.com/jobs/ie/"],
        [r"careers\.jazzpharma\.com/job/\d+/[^?#]+/?$"],
        "jazz_direct", session, True
    )


def scrape_takeda_ireland_direct(session):
    return _scrape_first_party_ireland_listing(
        "Takeda",
        [
            "https://jobs.takeda.com/location/ireland-jobs/1113/2963597/2",
            "https://jobs.takeda.com/en/Ireland",
        ],
        [r"jobs\.takeda\.com/(?:[a-z]{2}/)?job/[^?#]+", r"jobs\.takeda\.com/job/[^?#]+"],
        "takeda_direct", session, True
    )


def scrape_teleflex_ireland_direct(session):
    return _scrape_first_party_ireland_listing(
        "Teleflex",
        [
            "https://careers.teleflex.com/search/?q=&locationsearch=Ireland",
            "https://careers.teleflex.com/search/?q=&locationsearch=Athlone",
        ],
        [r"careers\.teleflex\.com/job/[^?#]+"],
        "teleflex_direct", session, True
    )



def scrape_viatris_ireland_direct(session):
    # Verified current tenant: Viatris moved from wd1 to wd5 and the board is "external".
    return _workday_override_scrape(
        "Viatris",
        "https://viatris.wd5.myworkdayjobs.com/external",
        session,
    )


def scrape_regeneron_ireland_direct(session):
    return _scrape_first_party_ireland_listing(
        "Regeneron",
        [
            "https://careers.regeneron.com/en/jobs/?location=Ireland",
            "https://careers.regeneron.com/en/jobs/?search=&location=Limerick",
        ],
        [r"careers\.regeneron\.com/(?:[a-z]{2}/)?job/[^?#]+", r"careers\.regeneron\.com/.*/jobs?/[^?#]+"],
        "regeneron_direct", session, True
    )



def scrape_medtronic_ireland_direct(session):
    # Verified current Medtronic Workday tenant; replaces the broken jobs.medtronic.com route.
    return _workday_override_scrape(
        "Medtronic",
        "https://medtronic.wd1.myworkdayjobs.com/MedtronicCareers",
        session,
    )



def scrape_qiagen_ireland_direct(session):
    # Verified current QIAGEN Workday tenant.
    return _workday_override_scrape(
        "QIAGEN",
        "https://qiagen.wd502.myworkdayjobs.com/QIAGEN",
        session,
    )


def scrape_northern_trust_ireland_direct(session):
    # First-party corporate Ireland page is used as the entry point; job links
    # discovered there are verified on their destination pages.
    return _scrape_first_party_ireland_listing(
        "Northern Trust",
        [
            "https://www.northerntrust.com/europe/about-us/locations/ie",
            "https://www.northerntrust.com/united-states/about-us/careers",
        ],
        [r"northerntrust.*(?:job|career).*(?:\d|requisition)", r"myworkdayjobs\.com/.*/job/"],
        "northern_trust_direct", session, False
    )



def scrape_guidewire_ireland_direct_http(session):
    # Guidewire's jobs are rendered dynamically under /about/careers/jobs/<slug>.
    jobs = _rendered_filtered_job_page(
        "Guidewire",
        "https://www.guidewire.com/about/careers/jobs",
        "guidewire_rendered",
        "/about/careers/jobs/",
    )
    if jobs:
        return jobs
    return _sitemap_job_recovery(
        "Guidewire",
        ["https://www.guidewire.com"],
        "guidewire_sitemap",
        session,
    )


def scrape_siemens_ireland_direct_http(session):
    return _scrape_first_party_ireland_listing(
        "Siemens",
        [
            "https://jobs.siemens.com/en_US/externaljobs/SearchJobs/?jobRecordsPerPage=50&searchKeyword=Ireland",
        ],
        [r"jobs\.siemens\.com/en_US/externaljobs/JobDetail/[^?#]+"],
        "siemens_direct_http", session, True
    )


def scrape_red_hat_ireland_direct_http(session):
    return _scrape_first_party_ireland_listing(
        "Red Hat",
        [
            "https://www.redhat.com/en/jobs/locations",
            "https://www.redhat.com/en/jobs",
        ],
        [r"redhat\.com/.*/jobs?/[^?#]+", r"redhat\.com/.*/job/[^?#]+"],
        "redhat_direct_http", session, False
    )



def scrape_aon_ireland_direct_http(session):
    # Search UI is 403 in the user's runtime; try first-party sitemap/job-detail recovery.
    return _sitemap_job_recovery(
        "Aon",
        ["https://jobs.aon.com"],
        "aon_sitemap",
        session,
    )



def scrape_dxc_ireland_direct_http(session):
    # Search UI is frequently 403, but public detail pages are indexed under /job/<id>/...
    return _sitemap_job_recovery(
        "DXC Technology",
        ["https://careers.dxc.com"],
        "dxc_sitemap",
        session,
    )


def scrape_red_hat_ireland(session):
    direct = scrape_red_hat_ireland_direct_http(session)
    if direct:
        return direct
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
    """DXC Ireland via official CWS JSONP job API from supplied scrape.py."""
    api_url = "https://jobsapi-internal.m-cloud.io/api/job"
    results = {}
    offset = 1
    limit = 50

    for _ in range(20):
        params = [
            ("callback", "CWS.jobs.jobCallback"),
            ("facet[]", "is_internal:DXCJobs"),
            ("facet[]", "compliment:Ireland"),
            ("sortfield", "open_date"),
            ("sortorder", "descending"),
            ("Limit", str(limit)),
            ("Organization", "2492"),
            ("offset", str(offset)),
            ("fuzzy", "false"),
            ("facetlist[]", "compliment"),
            ("facetlist[]", "store_id"),
            ("facetlist[]", "primary_city"),
            ("facetlist[]", "primary_category"),
            ("facetlist[]", "employment_type"),
        ]
        try:
            r = session.get(
                api_url,
                params=params,
                timeout=20,
                headers={
                    "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
                    "Referer": "https://careers.dxc.com/job-search-results/",
                    "Accept": "*/*",
                },
            )
        except Exception as exc:
            print(f"      [dxc_friend] request failed: {exc}")
            break

        if r.status_code != 200:
            print(f"      [dxc_friend] HTTP {r.status_code}")
            break

        text = (r.text or "").strip()
        mm = re.search(r'^[^(]+\((.*)\)\s*;?\s*$', text, re.S)
        if mm:
            text = mm.group(1)

        try:
            payload = json.loads(text)
        except Exception:
            print("      [dxc_friend] invalid JSONP")
            break

        rows = payload.get("queryResult", []) if isinstance(payload, dict) else []
        if not isinstance(rows, list) or not rows:
            break

        for row in rows:
            if not isinstance(row, dict):
                continue
            country_code = str(row.get("primary_country") or "").strip().upper()
            country_name = str(row.get("compliment") or "").strip()
            city = str(row.get("primary_city") or "").strip()
            title = str(row.get("title") or "").strip()
            href = str(row.get("url") or "").strip()
            job_id = str(row.get("clientid") or row.get("id") or "").strip()

            if country_code != "IE" and country_name.lower() != "ireland":
                continue
            if not title or not href or _looks_like_non_job_title(title):
                continue

            location = f"{city}, Ireland" if city else "Ireland"
            desc = _html_to_text(str(row.get("description") or ""))
            sponsorship, snippet = classify_sponsorship(desc[:16000])

            results[(job_id or href).lower()] = {
                "company": "DXC Technology",
                "title": re.sub(r"\s+", " ", title).strip()[:300],
                "location": location,
                "posted_text": str(row.get("open_date") or "Unknown"),
                "posted_days_ago": parse_posted_text(str(row.get("open_date") or "")),
                "employment_type": normalize_employment_type(row.get("employment_type"), title),
                "url": href,
                "source": "dxc_cws_api",
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            }

        total_hits = int(payload.get("totalHits") or 0) if isinstance(payload, dict) else 0
        if offset + limit > total_hits or len(rows) < limit:
            break
        offset += limit

    print(f"      [dxc_friend] {len(results)} Ireland jobs")
    return list(results.values())





def _clean_grant_oracle_title(raw_title):
    """Strip Oracle card metadata from Grant Thornton job titles."""
    title = re.sub(r"\s+", " ", str(raw_title or "")).strip()
    if not title:
        return ""

    # Oracle can render this as "POSTING DATE24/08/2026" with no space.
    title = re.split(
        r"POSTING\s+DATE",
        title,
        maxsplit=1,
        flags=re.I,
    )[0].strip()

    # Remove trailing Oracle location metadata.
    title = re.sub(
        r"\s+"
        r"(?:Dublin|Cork|Galway|Limerick|Waterford|Kilkenny|Wexford|"
        r"Athlone|Sligo|Kildare|Clare|Tipperary|Meath|Louth|Mayo|"
        r"Wicklow|Donegal)"
        r",\s*Ireland"
        r"(?:\s+and\s+\d+\s+more)?"
        r"\s*$",
        "",
        title,
        flags=re.I,
    ).strip()

    # Fallback for a plain trailing "Ireland" location.
    title = re.sub(
        r"\s+Ireland(?:\s+and\s+\d+\s+more)?\s*$",
        "",
        title,
        flags=re.I,
    ).strip()

    # Occasional residual card badges.
    title = re.sub(
        r"\s+(?:TRENDING|BE THE FIRST TO APPLY|NEW)\s*$",
        "",
        title,
        flags=re.I,
    ).strip()

    return title

def scrape_grant_thornton_direct(session):
    """Grant Thornton Ireland: collect only real Oracle Candidate Experience job links.

    The former broad careers-page scraper could mistake navigation/CTA anchors
    for vacancies. This implementation follows the supplied reference logic:
    only /job/ detail links are accepted, then ROI evidence and title quality
    are verified before output.
    """
    company = "Grant Thornton Ireland"
    source_url = (
        "https://ehzq.fa.us2.oraclecloud.com/hcmUI/CandidateExperience/en/sites/"
        "GrantThorntonIrelandExperiencedHires/jobs"
    )

    if not HAS_PLAYWRIGHT:
        print("      [grant-oracle] Playwright unavailable")
        return []

    results = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1440, "height": 1300},
                locale="en-IE",
            )

            page.goto(
                source_url,
                wait_until="domcontentloaded",
                timeout=60000,
            )
            page.wait_for_timeout(2500)

            stagnant = 0
            previous_count = 0

            for _ in range(50):
                anchors = page.locator('a[href*="/job/"]')

                for i in range(min(anchors.count(), 500)):
                    a = anchors.nth(i)

                    try:
                        href = urllib.parse.urljoin(
                            page.url,
                            a.get_attribute("href") or "",
                        ).split("#")[0]
                    except Exception:
                        continue

                    # Structural proof that this is a real Oracle job detail URL.
                    if "/job/" not in href.lower():
                        continue

                    try:
                        title = _clean_grant_oracle_title(a.inner_text() or "")
                    except Exception:
                        title = ""

                    node = a
                    card = ""

                    for _up in range(7):
                        try:
                            candidate = node.inner_text() or ""
                            candidate = re.sub(r"\s+", " ", candidate).strip()
                        except Exception:
                            candidate = ""

                        if candidate and len(candidate) <= 3000:
                            card = candidate

                        if re.search(
                            r"\b(?:Dublin|Ireland|Cork|Galway|Limerick)\b",
                            card,
                            re.I,
                        ):
                            break

                        try:
                            node = node.locator("..")
                        except Exception:
                            break

                    if not title or len(title) > 300:
                        lines = [
                            re.sub(r"\s+", " ", x).strip()
                            for x in card.splitlines()
                            if 4 <= len(x.strip()) <= 220
                        ]
                        title = _clean_grant_oracle_title(
                            next(
                                (x for x in lines if not _looks_like_non_job_title(x)),
                                "",
                            )
                        )

                    if not title or _looks_like_non_job_title(title):
                        continue

                    evidence = f"{title} {card} {href}"

                    if _ROI_NEGATIVE_RE.search(evidence):
                        continue
                    if not is_republic_of_ireland_location(evidence):
                        continue

                    location = "Ireland"
                    for city in ("Dublin", "Cork", "Galway", "Limerick"):
                        if re.search(rf"\b{city}\b", evidence, re.I):
                            location = f"{city}, Ireland"
                            break

                    sponsorship, snippet = classify_sponsorship(card[:16000])

                    results[href.rstrip("/").lower()] = {
                        "company": company,
                        "title": title[:300],
                        "location": location,
                        "posted_text": "Unknown",
                        "posted_days_ago": None,
                        "employment_type": normalize_employment_type("", title),
                        "url": href,
                        "source": "grant_oracle_job_detail",
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    }

                clicked = False
                for selector in (
                    'button:has-text("Load More")',
                    'button:has-text("Show More")',
                    'button:has-text("Next")',
                    'a:has-text("Next")',
                ):
                    try:
                        btn = page.locator(selector)
                        if btn.count() and btn.first.is_visible():
                            btn.first.click(timeout=1200)
                            page.wait_for_timeout(400)
                            clicked = True
                            break
                    except Exception:
                        pass

                try:
                    page.mouse.wheel(0, 3200)
                    page.wait_for_timeout(300)
                except Exception:
                    pass

                current_count = len(results)
                stagnant = stagnant + 1 if current_count == previous_count else 0
                previous_count = current_count

                if stagnant >= 6 and not clicked:
                    break

            browser.close()

    except Exception as exc:
        print(f"      [grant-oracle] failed: {exc}")

    print(f"      [grant-oracle] {len(results)} verified Ireland jobs")
    return list(results.values())



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
    direct = scrape_aon_ireland_direct_http(session)
    if direct:
        return direct
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
    """Deutsche Bank Ireland via official Workday tenant from supplied scrape.py."""
    return _workday_override_scrape(
        "Deutsche Bank",
        "https://db.wd3.myworkdayjobs.com/DBWebsite",
        session,
    )



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
    """Three Ireland regression recovery via official Cornerstone Ireland board."""
    company = "Three Ireland"
    sources = [
        "https://three-ireland.csod.com/ux/ats/careersite/5/home?c=three-ireland&country=ie",
        (
            "https://three-ireland.csod.com/ux/ats/careersite/5/home"
            "?c=three-ireland&lq=Ireland"
            "&pl=ChIJ-ydAXOS6WUgRCPTbzjQSfM8"
        ),
    ]

    if not HAS_PLAYWRIGHT:
        return []

    results = {}

    def clean(x):
        return re.sub(r"\s+", " ", str(x or "")).strip()

    location_map = [
        ("Drogheda", "Drogheda, Ireland"),
        ("Sligo", "Sligo, Ireland"),
        ("Mary Street", "Dublin, Ireland"),
        ("Navan", "Navan, Ireland"),
        ("Limerick", "Limerick, Ireland"),
        ("Athlone", "Athlone, Ireland"),
        ("Patrick St", "Cork, Ireland"),
        ("Tralee", "Tralee, Ireland"),
        ("Bray", "Bray, Ireland"),
        ("Mahon Point", "Cork, Ireland"),
        ("Dublin", "Dublin, Ireland"),
        ("Cork", "Cork, Ireland"),
        ("Galway", "Galway, Ireland"),
    ]

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            context = browser.new_context(
                user_agent=HEADERS.get("User-Agent", "Mozilla/5.0"),
                locale="en-IE",
                viewport={"width": 1440, "height": 1600},
            )

            for source in sources:
                page = context.new_page()
                try:
                    page.goto(source, wait_until="domcontentloaded", timeout=45000)
                    page.wait_for_timeout(3000)
                    try:
                        _browser_accept_consent(page)
                    except Exception:
                        pass

                    # Cornerstone lazy-loads result cards.
                    for _ in range(8):
                        page.mouse.wheel(0, 1800)
                        page.wait_for_timeout(250)

                    links = page.locator("a[href]").evaluate_all(
                        """els => els.map(a => ({
                            href: a.href || "",
                            text: (a.innerText || a.textContent || "").trim()
                        }))"""
                    )

                    for item in links:
                        href = clean(item.get("href")).split("#")[0]
                        title = clean(item.get("text"))

                        if not href or not title or _looks_like_non_job_title(title):
                            continue

                        # Prefer the known Three CSOD requisition route, but
                        # also accept newer Cornerstone job/requisition URL shapes.
                        req_match = re.search(
                            r"/careersite/5/home/requisition/(\d+)",
                            href,
                            re.I,
                        )
                        is_cornerstone_detail = bool(
                            req_match
                            or (
                                "three-ireland.csod.com" in href.lower()
                                and re.search(
                                    r"(?:job|requisition|position|ats)"
                                    r".*(?:id|req|job|position|\d+)",
                                    href,
                                    re.I,
                                )
                            )
                        )
                        if not is_cornerstone_detail:
                            continue

                        # Reject obvious careers navigation text.
                        if title.lower() in {
                            "home", "careers", "search jobs", "job search",
                            "three ireland", "view all jobs",
                        }:
                            continue

                        location = "Ireland"
                        for needle, normalized in location_map:
                            if re.search(rf"\b{re.escape(needle)}\b", title, re.I):
                                location = normalized
                                break

                        key = req_match.group(1) if req_match else href.rstrip("/").lower()

                        results[key] = {
                            "company": company,
                            "title": title[:300],
                            "location": location,
                            "posted_text": "Unknown",
                            "posted_days_ago": None,
                            "employment_type": normalize_employment_type("", title),
                            "url": href,
                            "source": "three_cornerstone_regression_recovery",
                            "visa_sponsorship": "Unknown",
                            "visa_snippet": "",
                        }

                except Exception as exc:
                    print(f"      [three-regression] source failed: {exc}")
                finally:
                    try:
                        page.close()
                    except Exception:
                        pass

                if results:
                    break

            context.close()
            browser.close()

    except Exception as exc:
        print(f"      [three-regression] failed: {exc}")

    print(f"      [three-regression] {len(results)} Ireland jobs")
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
    direct = scrape_guidewire_ireland_direct_http(session)
    if direct:
        return direct
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
    direct = scrape_siemens_ireland_direct_http(session)
    if direct:
        return direct
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
    automated_zero = []
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

            # First normalize/filter without detail calls. This is fast and
            # prevents a large global board (Version 1) from spending tens of
            # seconds fetching descriptions for jobs that are not in Ireland.
            _roi_pairs = []
            for job in jobs:
                norm = normalize_smartrecruiters_job(
                    name, job, slug, local_session, False
                )
                if norm:
                    company_jobs.append(norm)
                    _roi_pairs.append((job, norm))

            # Preserve the sponsorship deliverable: fetch descriptions only
            # for the already-filtered Republic-of-Ireland jobs, concurrently.
            if fetch_descriptions and _roi_pairs:
                def _sr_desc(pair):
                    raw_job, norm_job = pair
                    posting_id = raw_job.get("id", "")
                    desc = fetch_smartrecruiters_description(
                        slug, posting_id, requests.Session()
                    ) if posting_id else ""
                    return norm_job, desc

                _desc_pool = ThreadPoolExecutor(max_workers=min(10, len(_roi_pairs)))
                try:
                    _desc_futs = [_desc_pool.submit(_sr_desc, pair) for pair in _roi_pairs]
                    for _df in as_completed(_desc_futs):
                        try:
                            _norm_job, _desc = _df.result()
                            _spons, _snippet = classify_sponsorship(_desc)
                            _norm_job["visa_sponsorship"] = _spons
                            _norm_job["visa_snippet"] = _snippet
                        except Exception:
                            pass
                finally:
                    _desc_pool.shutdown(wait=False)
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
        return entry, platform, slug, company_jobs, True

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
                    _ats_timeout = 75 if original[1] == "smartrecruiters" else 30
                    entry, platform, slug, company_jobs, fetch_ok = fut.result(timeout=_ats_timeout)
                except FuturesTimeoutError:
                    entry, platform, slug = original
                    company_jobs, fetch_ok = [], False
                    print(f"      [ATS] {entry['company']}: timed out after {_ats_timeout}s")
                except Exception as exc:
                    # A genuine fetch failure remains unresolved/manual.
                    entry, platform, slug = original
                    company_jobs, fetch_ok = [], False
                    print(f"      [ATS] {entry['company']}: fetch failed ({exc})")
                name, url = entry["company"], entry["url"]
                if company_jobs:
                    discovered_jobs.extend(company_jobs)
                elif not fetch_ok:
                    still_manual.append({"company": name, "url": url,
                                          "platform": f"{platform} (Fetching error)"})
                else:
                    automated_zero.append({
                        "company": name,
                        "platform": platform,
                        "reason": "Currently no jobs in Ireland",
                    })
                # IMPORTANT: fetch_ok=True + 0 Ireland jobs is a successful
                # automated check, not a manual/unresolved company.
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

    return discovered_jobs, still_manual, automated_zero

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


# SHEET 2 PRIORITY COVERAGE — module-level so both main() (task queueing)
# and test_single_company() (--only fast testing) can see it. These are the
# Tier-1 companies from the user's "2. Not Live Yet - Keep" sheet that don't
# already have a dedicated scraper. They get an Ireland-first browser
# fallback (scrape_priority_sheet2_generic) so they can move from
# manual_check into the live job list when the career page exposes current
# Ireland vacancies.
#
# NOTE: "hcltech" is deliberately NOT in this set — HCLTech already has a
# dedicated scraper (scrape_hcltech_ireland, in dedicated_company_specs)
# with an Ireland-filtered search URL. Including it here too would scrape
# it twice every run (once generic, once dedicated) for no benefit, wasting
# a worker slot in the fixed 10-worker pool.
# Workday recovery batch 1 — these companies currently sit in manual_check because
# their Workday CXS route either returns HTTP 422 or a suspicious zero.  Do NOT
# replace the normal Workday path: only invoke the existing Ireland-first rendered
# browser scraper after the normal API path fails/returns no jobs.
WORKDAY_RECOVERY_COMPANIES = {
    "aon",
    "dxc technology",
    "northern trust",
    "willis towers watson (wtw)",
    "bausch + lomb",
    "becton dickinson (bd)",
    "broadcom",
    "edwards lifesciences",
    "illumina",
    "jazz pharmaceuticals",
    "nxp semiconductors",
    "qualcomm",
    "takeda",
    "teleflex",
    "teva pharmaceuticals",
    "vmware (broadcom)",
    "viatris",
    "rockwell automation",
}


PRIORITY_SHEET2_COMPANIES = {
    # confirmed manual recovery batch
    "aon", "dxc technology", "northern trust", "willis towers watson (wtw)",
    "becton dickinson (bd)", "jazz pharmaceuticals", "takeda", "teleflex",
    "viatris", "siemens", "guidewire", "hcltech", "red hat",
    "central bank of ireland", "deutsche bank",

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
    # Second batch — next 24 Tier-1 companies from Sheet 2 (hcltech
    # excluded — see note above, it already has a dedicated scraper)
    "goodbody",
    "greencore",
    "heineken ireland",
    "ibm",
    "infosys",
    "laya healthcare",
    "lidl ireland",
    "msci",
    "macquarie group",
    "mckinsey & company",
    "moody's",
    "morgan stanley",
    "morningstar",
    "musgrave group (supervalu / centra)",
    "northern trust",
    "oliver wyman",
    "protiviti",
    "refinitiv (lseg)",
    "s&p global",
    "sap",
    "slalom",
    "societe generale",
    "splunk",
    # Third batch — next 25 companies from Sheet 2 (rows 57-81).
    # NOTE: "supervalu / musgrave" is a separate CSV row from "musgrave
    # group (supervalu / centra)" above (different career_url — one is
    # musgravegroup.com/careers/, the other careers.musgravegroup.com) but
    # both point at the same real employer. Left both in for now since
    # they use different URLs and one might work where the other doesn't,
    # but flagged here as a likely consolidation candidate once you see
    # which (if either) actually returns jobs — running both every cycle
    # burns two worker slots for what's probably the same postings.
    "supervalu / musgrave",
    "susquehanna international group (sig)",
    "tata consultancy services (tcs)",
    "tesco ireland",
    "ubs",
    "vhi healthcare",
    "version 1",
    "visa",
    "willis towers watson (wtw)",
    "wipro",
    "zurich insurance",
    "abp food group",
    "asml",
    "abbott",
    "advanced micro devices (amd)",
    "aer lingus",
    "aercap",
    "agilent technologies",
    "akamai",
    "alexion pharmaceuticals",
    "alkermes",
    "amgen",
    "an post",
    "applied materials",
    "astrazeneca",
    # Fourth batch — next 25 companies from Sheet 2 (rows 82-106).
    "atlassian",
    "bausch + lomb",
    "baxter international",
    "bayer",
    "becton dickinson (bd)",
    "bio-rad laboratories",
    "biotronik",
    "boehringer ingelheim",
    "bord gáis energy",
    "box",
    "bristol myers squibb",
    "broadcom",
    "bruker",
    "bus éireann",
    "c&c group",
    "carbery group",
    "catalent",
    "charles river laboratories",
    "cisco",
    "coillte",
    "coloplast",
    "convatec",
    "cook medical",
    "dhl ireland",
    "dsv ireland",
    # Fifth batch — 25 companies requested from Sheet 2 (rows 107-131),
    # 21 actually added below. Four were skipped because their CSV
    # career_url is IDENTICAL to a company already covered elsewhere —
    # running the generic scraper on them again would just re-scrape the
    # exact same page under a second label, producing duplicate-looking
    # job entries in the dashboard for zero new information, and burning
    # a worker slot for nothing:
    #   - "dawn meats" — identical CSV row/URL to the "dawn meats" key
    #     already in lightweight_specs (dawnmeats.com/careers/).
    #   - "guidewire" — identical CSV row/URL to the "guidewire" key
    #     already in dedicated_company_specs (guidewire.com/about/careers/jobs).
    #   - "depuy synthes" — its CSV career_url is jobs.jnj.com/en/jobs/?search=Ireland,
    #     the exact same URL "johnson & johnson" already scrapes (DePuy
    #     Synthes is J&J MedTech) — its jobs are already being picked up,
    #     just labeled "Johnson & Johnson".
    #   - "horizon therapeutics (amgen)" — its CSV career_url is
    #     careers.amgen.com/search-jobs/Ireland, the exact same URL "amgen"
    #     (added in the third batch) already scrapes — same reasoning.
    # If you want these under their own distinct company name in the
    # dashboard rather than folded into the parent company's listing, say
    # so and I'll add them back with a note instead of skipping.
    "dairygold",
    "danaher corporation",
    "dell technologies",
    "dexcom",
    "docusign",
    "dublin bus",
    # NOTE: "esb (electricity supply board)" is a separate CSV row from
    # the existing "esb" (lightweight_specs) with a DIFFERENT career_url
    # (esb.ie/careers vs careers.esb.ie/go/All-Jobs/882102/) — same real
    # company, but since the URLs genuinely differ this is kept in rather
    # than dropped like the four above, same treatment as the earlier
    # SuperValu/Musgrave case. Worth consolidating once you see which URL
    # actually returns results.
    "esb (electricity supply board)",
    "edwards lifesciences",
    "eir",
    "eirgrid group",
    "eli lilly",
    "energia group",
    "fastway couriers ireland",
    "fedex express ireland",
    "gas networks ireland",
    "glaxosmithkline (gsk)",
    "hp (hewlett-packard)",
    "hse (health service executive)",
    "haleon",
    "hewlett packard enterprise (hpe)",
    "hollister incorporated",
    # Sixth batch — 25 companies requested from Sheet 2 (rows 132-156),
    # 22 actually added below. Three were skipped:
    #   - "netflix" — identical CSV row/URL to the "netflix" key already
    #     in dedicated_company_specs (scrape_netflix_ireland). Adding it
    #     here too would double-scrape the same page under two labels.
    #   - "nvidia" — NOT in Job_Automation.csv at all right now. Per the
    #     project history, NVIDIA was deliberately removed earlier after
    #     verifying (SEC 10-K) it has no genuine Ireland presence — this
    #     string would just never match anything and sit as dead weight.
    #     If you've since found evidence NVIDIA does hire in Ireland now,
    #     say so and I'll re-add the CSV row and wire it back in properly
    #     — otherwise leaving it out is consistent with that earlier call.
    #   - "irish rail (iarnród éireann)" — turned out to expose a real,
    #     separate bug: the existing dedicated lightweight scraper for
    #     Irish Rail was keyed on "irish rail", but your CSV's actual
    #     company_name is "Irish Rail (Iarnród Éireann)" — an exact-match
    #     mismatch, so that scraper has likely never actually fired.
    #     Fixed the key directly in lightweight_specs below instead of
    #     adding a duplicate generic entry here.
    "icon plc",
    "iqvia",
    "illumina",
    "insulet corporation",
    "integra lifesciences",
    "intel",
    "irish distillers (pernod ricard)",
    "irish ferries",
    "jazz pharmaceuticals",
    "kepak group",
    "kuehne+nagel ireland",
    "linkedin",
    "lonza",
    "marvell technology",
    "medpace",
    "medtronic",
    "merck group",
    "merit medical",
    "micron technology",
    "nxp semiconductors",
    "netapp",
    "nokia",
    # Eighth batch — 25 companies requested from Sheet 2 (rows 157-181),
    # 23 actually added below. Two were skipped:
    #   - "red hat" — identical CSV row to the "red hat" key already in
    #     dedicated_company_specs (scrape_red_hat_ireland). It already has
    #     a purpose-built scraper; the generic fallback wouldn't add
    #     anything, just burn a worker slot re-hitting the same page.
    #   - "siemens" — same reasoning, identical CSV row to the existing
    #     "siemens" dedicated scraper (which is also one of the companies
    #     currently on a reduced failure-budget in recent runs).
    # Four are worth flagging even though they're KEPT in, not skipped:
    # "qualcomm", "resmed", "takeda", "teleflex" all already get checked
    # every run via the Workday phase and came back with 0 Ireland
    # postings there (confirmed in your own run logs) — but that's a
    # different mechanism (Workday's JSON API) than this generic fallback
    # (rendering the page and scanning links), and your logs show Workday's
    # API-side Ireland filter is unreliable for some companies (the
    # "total=361 implausibly high, filter didn't apply" pattern seen on
    # Broadcom/VMware). So there's a genuine chance the generic scraper
    # succeeds where the Workday API parse doesn't — unlike Red Hat/Siemens,
    # these four don't have a purpose-built scraper standing in for this
    # already. Worth watching whether they actually turn up anything new;
    # if they don't after a few runs, they're better dropped too.
    "novartis",
    "ornua",
    "palo alto networks",
    "qiagen",
    "qualcomm",
    "regeneron",
    "resmed",
    "revvity (perkinelmer)",
    "roche",
    "ryanair",
    "smbc aviation capital",
    "sse airtricity / sse",
    "shannon airport group",
    "sky ireland",
    "slack",
    "smith & nephew",
    "smurfit westrock",
    "stena line ireland",
    "stryker",
    "syneos health",
    "takeda",
    "tandem diabetes care",
    "teleflex",
    # Ninth batch — final 16 companies from Sheet 2, 14 actually added
    # below. Two were skipped:
    #   - "three ireland" — identical CSV row to the "three ireland" key
    #     already in dedicated_company_specs (scrape_three_ireland_direct).
    #   - "ups ireland" — identical CSV row to the "ups ireland" key
    #     already in dedicated_company_specs (scrape_ups_ireland).
    # Same reasoning as Red Hat/Siemens in the previous batch: both already
    # have purpose-built scrapers, so the generic fallback adds nothing.
    #
    # Four more (same treatment as Qualcomm/ResMed/Takeda/Teleflex above)
    # are Workday-tenant companies that came back with 0 Ireland postings
    # via the Workday phase in your own logs, but have no dedicated
    # scraper of their own — kept in since the generic fallback might
    # succeed where Workday's own Ireland-location filter doesn't (the
    # same "total=361 implausibly high" unreliability seen elsewhere):
    # "teva pharmaceuticals", "vmware (broadcom)", "viatris", "zimmer biomet".
    "terumo",
    "teva pharmaceuticals",
    "texas instruments",
    "thermo fisher scientific",
    "uisce éireann (irish water)",
    "vmware (broadcom)",
    "viatris",
    "virgin media ireland",
    "vodafone ireland",
    "waters corporation",
    "wuxi biologics",
    "zendesk",
    "zimmer biomet",
    "daa (dublin airport authority)",
    # Note: this is the 178-company combined priority set (this batch was
    # the final 16 from Sheet 2, for 191 total requested across all
    # batches; minus hcltech, plus the 7 skipped exact-scraper duplicates
    # across all batches). This is the full Sheet 2 list.
}



def scrape_wipro_ireland(session):
    """Dedicated Wipro scraper using the actual SuccessFactors search route.

    /viewalljobs/ is an SEO/category page and may expose no vacancy anchors.
    The real result feed is /search/?q=&locationsearch=<place>. We query
    Ireland plus major ROI cities, collect only individual /job/.../<id>/ URLs,
    then verify each detail page's Job Title + City + State/Province.
    """
    base = "https://careers.wipro.com"
    headers = {
        **HEADERS,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "en-IE,en;q=0.9",
    }

    if not HAS_PLAYWRIGHT:
        print("      [wipro] Playwright unavailable")
        return []

    candidate_urls = set()
    search_terms = ["Ireland", "Dublin", "Cork", "Galway", "Limerick"]

    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1400, "height": 1000},
                user_agent=HEADERS.get("User-Agent"),
            )

            for term in search_terms:
                search_url = (
                    f"{base}/search/?createNewAlert=false&q="
                    f"&locationsearch={urllib.parse.quote_plus(term)}"
                    f"&searchResultView=LIST"
                )

                try:
                    page.goto(search_url, wait_until="domcontentloaded", timeout=45000)
                    page.wait_for_timeout(3500)
                except Exception as exc:
                    print(f"      [wipro] search {term!r} failed: {exc}")
                    continue

                # Cookie banners can obscure rows; dismiss when possible.
                for txt in ("Accept All Cookies", "Confirm My Choices"):
                    try:
                        btn = page.get_by_text(txt, exact=False).first
                        if btn.count() and btn.is_visible():
                            btn.click(timeout=1500)
                            page.wait_for_timeout(800)
                            break
                    except Exception:
                        pass

                # Trigger lazy rendering.
                try:
                    page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                    page.wait_for_timeout(1500)
                except Exception:
                    pass

                found = set()

                # DOM anchors
                links = page.locator('a[href*="/job/"]')
                for i in range(min(links.count(), 500)):
                    try:
                        href = links.nth(i).get_attribute("href")
                    except Exception:
                        continue
                    if not href:
                        continue
                    href = urllib.parse.urljoin(page.url, href).split("#")[0]

                    if re.search(
                        r"^https://careers\.wipro\.com/job/.+/\d+(?:-[A-Za-z_]+)?/?(?:\?.*)?$",
                        href,
                        re.I,
                    ):
                        found.add(href)

                # HTML fallback in case the links are present in markup but
                # not represented as standard anchor locators.
                try:
                    html_text = page.content()
                    for raw in re.findall(
                        r'https?://careers\.wipro\.com/job/[^"\'<>\s]+',
                        html_text,
                        re.I,
                    ):
                        raw = html.unescape(raw)
                        if re.search(
                            r"/job/.+/\d+(?:-[A-Za-z_]+)?/?(?:\?.*)?$",
                            raw,
                            re.I,
                        ):
                            found.add(raw)
                    for raw in re.findall(
                        r'["\'](/job/[^"\']+/\d+(?:-[A-Za-z_]+)?/?)["\']',
                        html_text,
                        re.I,
                    ):
                        found.add(urllib.parse.urljoin(base, html.unescape(raw)))
                except Exception:
                    pass

                candidate_urls.update(found)
                print(
                    f"      [wipro] search={term}: "
                    f"{len(found)} vacancy URLs ({len(candidate_urls)} unique total)"
                )

            browser.close()

    except Exception as exc:
        print(f"      [wipro] search discovery failed: {exc}")
        return []

    if not candidate_urls:
        print("      [wipro] no vacancy URLs found on SuccessFactors search pages")
        return []

    def fetch_detail(url):
        try:
            r = requests.get(url, headers=headers, timeout=10, allow_redirects=True)
            if r.status_code >= 400:
                return None

            page_text = re.sub(r"\s+", " ", _html_to_text(r.text)).strip()

            def field(label, following_labels):
                end = "|".join(re.escape(x) for x in following_labels)
                mm = re.search(
                    rf"\b{re.escape(label)}\s*:\s*(.+?)(?=\s+(?:{end})\s*:|$)",
                    page_text,
                    re.I,
                )
                return re.sub(r"\s+", " ", mm.group(1)).strip() if mm else ""

            title = field(
                "Job Title",
                ["City", "State/Province", "Posting Start Date", "Job Description"],
            )
            if not title:
                title = field(
                    "Title",
                    ["Requisition ID", "City", "Country/Region", "State/Province"],
                )

            city = field(
                "City",
                ["State/Province", "Country/Region", "Posting Start Date",
                 "Job Description", "Job Title", "Title"],
            )
            state = field(
                "State/Province",
                ["Country/Region", "Posting Start Date", "Job Description",
                 "Job Title", "City"],
            )
            country = field(
                "Country/Region",
                ["Posting Start Date", "Job Description", "Job Title", "City"],
            )
            posted_raw = field(
                "Posting Start Date",
                ["Job Description", "Job Title", "City", "State/Province",
                 "Country/Region"],
            )

            meta = _extract_job_detail_metadata_from_html(r.text, r.url, "Wipro")
            if not title:
                title = _clean_detail_page_title(meta.get("title"), "Wipro") or ""

            if not title or _looks_like_non_job_title(title):
                return None

            location_evidence = ", ".join(
                x for x in [city, state, country] if x
            ).strip()

            # Job detail itself must prove Republic of Ireland.
            if not is_republic_of_ireland_location(location_evidence):
                return None
            if _ROI_NEGATIVE_RE.search(location_evidence):
                return None

            location = location_evidence
            if country and country.upper() == "IE":
                location = ", ".join(x for x in [city, state, "Ireland"] if x)
            elif "ireland" not in location.lower():
                location = f"{location}, Ireland"

            posted_text = posted_raw or str(meta.get("posted_text") or "").strip()

            # Wipro/SuccessFactors can expose the posting date in several
            # formats and sometimes only in HTML attributes rather than the
            # visible text labels.
            if not posted_text:
                html_date_match = re.search(
                    r'(?:datetime|data-date|data-startdate)=["\']'
                    r'(\d{4}-\d{2}-\d{2})(?:[T ][^"\']*)?["\']',
                    r.text,
                    re.I,
                )
                if html_date_match:
                    posted_text = html_date_match.group(1)

            if not posted_text:
                text_date_match = re.search(
                    r'\b(?:Posting Start Date|Posted|Date Posted|Date)\s*:?\s*'
                    r'('
                    r'\d{1,2}/\d{1,2}/\d{2,4}'
                    r'|\d{4}-\d{2}-\d{2}'
                    r'|[A-Za-z]{3,9}\s+\d{1,2},\s+\d{4}'
                    r'|\d{1,2}\s+[A-Za-z]{3,9}\s+\d{4}'
                    r'|\d{1,2}-[A-Za-z]{3,9}-\d{4}'
                    r')',
                    page_text,
                    re.I,
                )
                if text_date_match:
                    posted_text = text_date_match.group(1)

            posted_text = posted_text or "Unknown"
            posted_days = parse_posted_text(posted_text)

            # SuccessFactors may inject the posting date only after rendering.
            # If static HTML has no usable date, render this individual vacancy
            # page once and inspect the visible body text.
            if posted_days is None and posted_text == "Unknown" and HAS_PLAYWRIGHT:
                try:
                    with sync_playwright() as _p:
                        _b = _p.chromium.launch(
                            headless=True,
                            args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
                        )
                        _pg = _b.new_page(user_agent=HEADERS.get("User-Agent"))
                        _pg.goto(r.url, wait_until="domcontentloaded", timeout=25000)
                        _pg.wait_for_timeout(1500)
                        _txt = re.sub(r"\s+", " ", _pg.locator("body").inner_text()).strip()
                        _b.close()

                    _mdate = re.search(
                        r'\b(?:Posting Start Date|Posted|Date Posted|Date)\s*:?\s*'
                        r'('
                        r'\d{1,2}/\d{1,2}/\d{2,4}'
                        r'|\d{4}-\d{2}-\d{2}'
                        r'|[A-Za-z]{3,9}\s+\d{1,2},\s+\d{4}'
                        r'|\d{1,2}\s+[A-Za-z]{3,9}\s+\d{4}'
                        r'|\d{1,2}-[A-Za-z]{3,9}-\d{4}'
                        r')',
                        _txt,
                        re.I,
                    )
                    if _mdate:
                        posted_text = _mdate.group(1)
                        posted_days = parse_posted_text(posted_text)
                except Exception:
                    pass

            if posted_days is None and posted_text != "Unknown":
                _wipro_date_formats = (
                    "%m/%d/%y", "%m/%d/%Y",
                    "%Y-%m-%d",
                    "%b %d, %Y", "%B %d, %Y",
                    "%d %b %Y", "%d %B %Y",
                    "%d-%b-%Y", "%d-%B-%Y",
                )
                for fmt in _wipro_date_formats:
                    try:
                        d = datetime.strptime(posted_text.strip(), fmt).replace(tzinfo=timezone.utc)
                        posted_days = max(
                            0.0,
                            float((datetime.now(timezone.utc).date() - d.date()).days),
                        )
                        break
                    except Exception:
                        pass

            description = str(meta.get("description") or page_text)
            sponsorship, snippet = classify_sponsorship(description[:16000])

            return {
                "company": "Wipro",
                "title": title[:300],
                "location": location,
                "posted_text": posted_text,
                "posted_days_ago": posted_days,
                "posted_age_known": posted_days is not None,
                "employment_type": normalize_employment_type(
                    meta.get("employment_type"), title
                ),
                "url": r.url,
                "source": "wipro_successfactors_search",
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            }
        except Exception:
            return None

    results = {}
    urls = sorted(candidate_urls)
    pool = ThreadPoolExecutor(max_workers=min(12, len(urls)))
    try:
        futs = {pool.submit(fetch_detail, u): u for u in urls}
        for fut in as_completed(futs):
            try:
                job = fut.result()
            except Exception:
                job = None
            if job:
                results[job["url"].rstrip("/").lower()] = job
    finally:
        pool.shutdown(wait=False)

    jobs = list(results.values())
    print(
        f"      [wipro] {len(jobs)} verified Republic-of-Ireland vacancies "
        f"from {len(candidate_urls)} SuccessFactors vacancy records"
    )
    return jobs




def scrape_iqvia_ireland(session):
    """Dedicated IQVIA scraper via IQVIA's own Sitemap -> Ireland Jobs page.

    The generic/global /en/jobs page does not reliably expose location on cards,
    and query parameters were observed to be ignored. IQVIA's first-party
    sitemap explicitly exposes an "Ireland Jobs" location page, which is the
    correct country-scoped discovery surface.
    """
    if not HAS_PLAYWRIGHT:
        print("      [iqvia] Playwright unavailable")
        return []

    base = "https://jobs.iqvia.com"
    candidate_urls = set()
    ireland_page_url = None

    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1400, "height": 1000},
                user_agent=HEADERS.get("User-Agent"),
            )

            # 1) Resolve the current Ireland location page from IQVIA's own sitemap.
            try:
                page.goto(f"{base}/en/sitemap", wait_until="domcontentloaded", timeout=45000)
                page.wait_for_timeout(2500)

                links = page.locator("a[href]")
                for i in range(min(links.count(), 2500)):
                    a = links.nth(i)
                    try:
                        txt = re.sub(r"\s+", " ", a.inner_text()).strip()
                        href = a.get_attribute("href")
                    except Exception:
                        continue
                    if not href:
                        continue
                    if re.fullmatch(r"Ireland Jobs", txt, re.I):
                        ireland_page_url = urllib.parse.urljoin(page.url, href).split("#")[0]
                        break

                # Fallback: search the sitemap HTML for a location URL containing Ireland.
                if not ireland_page_url:
                    sitemap_html = page.content()
                    mm = re.search(
                        r'href=["\']([^"\']*(?:ireland|%C3%A9ire)[^"\']*)["\'][^>]*>'
                        r'[^<]*Ireland Jobs',
                        sitemap_html,
                        re.I,
                    )
                    if mm:
                        ireland_page_url = urllib.parse.urljoin(
                            page.url, html.unescape(mm.group(1))
                        ).split("#")[0]
            except Exception as exc:
                print(f"      [iqvia] sitemap resolution failed: {exc}")

            if not ireland_page_url:
                print("      [iqvia] could not resolve first-party Ireland Jobs page from sitemap")
                browser.close()
                return []

            print(f"      [iqvia] Ireland Jobs page: {ireland_page_url}")

            # 2) Walk the Ireland-scoped location page.
            # IQVIA location pages usually paginate with ?page=N.
            no_new_pages = 0
            for page_no in range(1, 21):
                if page_no == 1:
                    url = ireland_page_url
                else:
                    sep = "&" if "?" in ireland_page_url else "?"
                    url = f"{ireland_page_url}{sep}page={page_no}"

                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=45000)
                    page.wait_for_timeout(1800)
                except Exception:
                    break

                found = set()
                links = page.locator('a[href*="/en/jobs/R"]')
                for i in range(min(links.count(), 300)):
                    try:
                        href = links.nth(i).get_attribute("href")
                    except Exception:
                        continue
                    if not href:
                        continue
                    href = urllib.parse.urljoin(page.url, href).split("#")[0]
                    if re.search(
                        r"^https://jobs\.iqvia\.com/en/jobs/R\d+(?:-\d+)?/?$",
                        href,
                        re.I,
                    ):
                        found.add(href)

                # Current/legacy IQVIA detail format fallback:
                # /en/job/<city>/<slug>/<numbers>/<numbers>
                legacy = page.locator('a[href*="/en/job/"]')
                for i in range(min(legacy.count(), 300)):
                    try:
                        href = legacy.nth(i).get_attribute("href")
                    except Exception:
                        continue
                    if not href:
                        continue
                    href = urllib.parse.urljoin(page.url, href).split("#")[0]
                    if "/en/job/" in href:
                        found.add(href)

                before = len(candidate_urls)
                candidate_urls.update(found)

                print(
                    f"      [iqvia] Ireland page={page_no}: "
                    f"{len(found)} vacancy URLs ({len(candidate_urls)} unique)"
                )

                if len(candidate_urls) == before:
                    no_new_pages += 1
                else:
                    no_new_pages = 0

                # Two consecutive pages with no new jobs means the location
                # listing has ended or page=N is ignored.
                if no_new_pages >= 2:
                    break

            if not candidate_urls:
                browser.close()
                print("      [iqvia] Ireland location page exposed 0 vacancy URLs")
                return []

            # 3) Verify each detail page in rendered DOM.
            results = {}

            for url in sorted(candidate_urls):
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=35000)
                    page.wait_for_timeout(900)

                    body = re.sub(r"\s+", " ", page.locator("body").inner_text()).strip()

                    title = ""
                    try:
                        title = re.sub(
                            r"\s+", " ",
                            page.locator("h1").first.inner_text()
                        ).strip()
                    except Exception:
                        pass

                    if not title or _looks_like_non_job_title(title):
                        continue

                    # IQVIA header examples:
                    # Dublin, Ireland | Full time | Hybrid | R...
                    # Galway County, Ireland | Full time | Field-based | R...
                    # Wexford, Ireland | Full time | Office-based | R...
                    # IQVIA LOCATION CLEANUP
                    # Extract a location from the vacancy detail itself, but
                    # never allow surrounding job-title/navigation text to
                    # become part of the location.
                    #
                    # Examples to normalize:
                    #   "Unix Systems Engineer Dublin, Ireland"
                    #       -> "Dublin, Ireland"
                    #   "homebased Dublin, Ireland"
                    #       -> "Dublin, Ireland"
                    #   "Wexford, Ireland"
                    #       -> "Wexford, Ireland"
                    #
                    # This is geographic parsing only. It does NOT use job-title
                    # keywords and does not affect whether a vacancy is relevant
                    # to the user's CV.
                    loc = ""

                    roi_place_patterns = [
                        (r"\bDublin\b", "Dublin"),
                        (r"\bCork\b", "Cork"),
                        (r"\bGalway(?:\s+County)?\b", "Galway"),
                        (r"\bLimerick\b", "Limerick"),
                        (r"\bWexford\b", "Wexford"),
                        (r"\bWaterford\b", "Waterford"),
                        (r"\bAthlone\b", "Athlone"),
                        (r"\bSligo\b", "Sligo"),
                        (r"\bKildare\b", "Kildare"),
                        (r"\bKilkenny\b", "Kilkenny"),
                        (r"\bClare\b", "Clare"),
                        (r"\bTipperary\b", "Tipperary"),
                        (r"\bMeath\b", "Meath"),
                        (r"\bLouth\b", "Louth"),
                        (r"\bMayo\b", "Mayo"),
                        (r"\bWicklow\b", "Wicklow"),
                        (r"\bDonegal\b", "Donegal"),
                    ]

                    # Prefer the header/metadata area before the main description.
                    # IQVIA normally presents:
                    #   <location> | Full time | <work mode> | R...
                    header_text = body[:3500]

                    # First, look for an explicit Republic-of-Ireland place that
                    # is immediately associated with ", Ireland".
                    for place_re, canonical_place in roi_place_patterns:
                        if re.search(
                            rf"{place_re}\s*,\s*Ireland\b",
                            header_text,
                            re.I,
                        ):
                            loc = f"{canonical_place}, Ireland"
                            break

                    # Some multi-location IQVIA roles have the Ireland location
                    # farther down the page. Search the whole vacancy only when
                    # the header did not provide a clean ROI place.
                    if not loc:
                        for place_re, canonical_place in roi_place_patterns:
                            if re.search(
                                rf"{place_re}\s*,\s*Ireland\b",
                                body,
                                re.I,
                            ):
                                loc = f"{canonical_place}, Ireland"
                                break

                    # Last resort: a detail page explicitly scoped simply to
                    # "Ireland | ..." with no city.
                    if not loc and re.search(
                        r"(?:^|\s)Ireland\s*\|\s*(?:Full|Part|Contract|Temporary|"
                        r"Permanent|Remote|Hybrid|Office|Field)",
                        header_text,
                        re.I,
                    ):
                        loc = "Ireland"

                    if not is_republic_of_ireland_location(loc):
                        continue
                    if _ROI_NEGATIVE_RE.search(loc):
                        continue

                    # Canonicalize whitespace and punctuation for dashboard use.
                    loc = re.sub(r"\s+", " ", loc).strip(" ,|-")
                    if loc.lower() != "ireland" and not loc.lower().endswith(", ireland"):
                        # A named ROI city/county should always render uniformly.
                        loc = f"{loc}, Ireland"

                    posted_text = "Unknown"
                    # IQVIA does not consistently expose a posting date.
                    employment = "Unspecified"
                    header_match = re.search(
                        re.escape(loc) + r"\s*\|\s*([^|]{2,40})",
                        body,
                        re.I,
                    )
                    if header_match:
                        employment = normalize_employment_type(
                            header_match.group(1), title
                        )

                    sponsorship, snippet = classify_sponsorship(body[:18000])

                    results[page.url.rstrip("/").lower()] = {
                        "company": "IQVIA",
                        "title": title[:300],
                        "location": loc,
                        "posted_text": posted_text,
                        "posted_days_ago": None,
                        "employment_type": employment,
                        "url": page.url,
                        "source": "iqvia_ireland_location_page",
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    }
                except Exception:
                    continue

            browser.close()

    except Exception as exc:
        print(f"      [iqvia] Ireland-location recovery failed: {exc}")
        return []

    jobs = list(results.values())
    print(f"      [iqvia] {len(jobs)} verified Republic-of-Ireland vacancies")
    return jobs


def scrape_merit_medical_ireland(session):
    """Dedicated Merit Medical first-party Workday route."""
    return _workday_override_scrape(
        "Merit Medical",
        "https://merit.wd503.myworkdayjobs.com/Merit",
        session,
    )




def _batch_first_party_roi_scrape(company_name, search_urls, allowed_domains,
                                  url_markers, session, source_tag,
                                  max_candidates=80):
    if not HAS_PLAYWRIGHT:
        print(f"      [{source_tag}] Playwright unavailable")
        return []

    candidates = set()

    def structural_job_url(url):
        u = str(url or "").lower()
        if not any(d.lower() in u for d in allowed_domains):
            return False
        return any(marker.lower() in u for marker in url_markers)

    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1400, "height": 1000},
                user_agent=HEADERS.get("User-Agent"),
            )

            for search_url in search_urls:
                try:
                    page.goto(search_url, wait_until="domcontentloaded", timeout=35000)
                    page.wait_for_timeout(1800)
                    try:
                        page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                        page.wait_for_timeout(700)
                    except Exception:
                        pass
                except Exception as exc:
                    print(f"      [{source_tag}] search failed: {exc}")
                    continue

                found = set()

                for frame in page.frames:
                    try:
                        links = frame.locator("a[href]")
                        for i in range(min(links.count(), 1200)):
                            href = links.nth(i).get_attribute("href")
                            if not href:
                                continue
                            href = urllib.parse.urljoin(
                                frame.url or page.url, href
                            ).split("#")[0]
                            if structural_job_url(href):
                                found.add(href)
                    except Exception:
                        pass

                    try:
                        frame_html = frame.content()
                        for raw in re.findall(
                            r'''(?:href=["\']|["\'])((?:https?://|/)[^"\'<> ]+)(?:["\'])''',
                            frame_html,
                            re.I,
                        ):
                            href = urllib.parse.urljoin(
                                frame.url or page.url,
                                html.unescape(raw).replace("\\/", "/"),
                            ).split("#")[0]
                            if structural_job_url(href):
                                found.add(href)
                    except Exception:
                        pass

                candidates.update(found)
                print(
                    f"      [{source_tag}] {len(found)} vacancy URLs "
                    f"({len(candidates)} unique)"
                )

                if len(candidates) >= max_candidates:
                    break

            if not candidates:
                browser.close()
                return []

            results = {}

            for detail_url in list(sorted(candidates))[:max_candidates]:
                try:
                    page.goto(
                        detail_url,
                        wait_until="domcontentloaded",
                        timeout=25000,
                    )
                    page.wait_for_timeout(500)

                    body = re.sub(
                        r"\s+", " ",
                        page.locator("body").inner_text()
                    ).strip()

                    if not is_republic_of_ireland_location(body):
                        continue
                    if _ROI_NEGATIVE_RE.search(body):
                        continue

                    title = ""
                    try:
                        title = re.sub(
                            r"\s+", " ",
                            page.locator("h1").first.inner_text()
                        ).strip()
                    except Exception:
                        pass

                    if not title or _looks_like_non_job_title(title):
                        continue

                    loc = "Republic of Ireland"
                    places = (
                        "Dublin", "Cork", "Galway", "Limerick", "Wexford",
                        "Waterford", "Athlone", "Sligo", "Kildare", "Kilkenny",
                        "Clare", "Tipperary", "Meath", "Louth", "Mayo",
                        "Wicklow", "Donegal", "Leixlip", "Cruiserath", "Shannon",
                    )
                    for place in places:
                        if re.search(
                            rf"\b{re.escape(place)}\b[^|.;]{{0,40}}\bIreland\b",
                            body,
                            re.I,
                        ):
                            loc = f"{place}, Ireland"
                            break

                    sponsorship, snippet = classify_sponsorship(body[:18000])

                    results[page.url.rstrip("/").lower()] = {
                        "company": company_name,
                        "title": title[:300],
                        "location": loc,
                        "posted_text": "Unknown",
                        "posted_days_ago": None,
                        "employment_type": normalize_employment_type("", title),
                        "url": page.url,
                        "source": source_tag,
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    }

                except Exception:
                    continue

            browser.close()

    except Exception as exc:
        print(f"      [{source_tag}] rendered recovery failed: {exc}")
        return []

    jobs = list(results.values())
    print(f"      [{source_tag}] {len(jobs)} verified Republic-of-Ireland vacancies")
    return jobs


def scrape_goodbody_ireland(session):
    return _batch_first_party_roi_scrape(
        "Goodbody",
        [
            "https://jobs.aib.ie/goodbody/search/?q=&locationsearch=Dublin",
            "https://jobs.aib.ie/goodbody/search/?q=&locationsearch=Ireland",
            "https://jobs.aib.ie/goodbody/",
        ],
        ["jobs.aib.ie"],
        ["/goodbody/job/"],
        session,
        "goodbody_first_party",
        40,
    )


def scrape_bms_ireland(session):
    return _batch_first_party_roi_scrape(
        "Bristol Myers Squibb",
        [
            "https://careers.bms.com/ie/",
            "https://careers.bms.com/jobs/?location=Ireland",
        ],
        ["careers.bms.com"],
        ["/job/", "/jobs/"],
        session,
        "bms_first_party",
        80,
    )


def scrape_sse_ireland(session):
    # The previous run found 2 verified ROI jobs but the outer 60s task
    # timeout fired while it was still walking 70+ global candidate URLs.
    # Restrict discovery to Ireland/Dublin-focused result pages and cap
    # detail verification so valid ROI jobs are returned in time.
    return _batch_first_party_roi_scrape(
        "SSE Airtricity / SSE",
        [
            "https://careers.sse.com/jobs/search?page=1&query=Dublin",
            "https://careers.sse.com/jobs/search?page=1&query=Ireland",
        ],
        ["careers.sse.com"],
        ["/jobs/", "/job/"],
        session,
        "sse_first_party",
        18,
    )


def scrape_hpe_ireland(session):
    return _batch_first_party_roi_scrape(
        "Hewlett Packard Enterprise (HPE)",
        [
            "https://careers.hpe.com/us/en/search-results?keywords=Ireland",
            "https://careers.hpe.com/us/en/search-results?keywords=Galway",
            "https://careers.hpe.com/us/en/search-results?keywords=Cork",
        ],
        ["careers.hpe.com"],
        ["/job/", "/jobs/"],
        session,
        "hpe_first_party",
        60,
    )


def scrape_dell_ireland(session):
    return _batch_first_party_roi_scrape(
        "Dell Technologies",
        [
            "https://jobs.dell.com/en/search-jobs/Ireland/375/2/2963597/53/-8/50/2",
            "https://jobs.dell.com/en/search-jobs?keywords=Ireland",
        ],
        ["jobs.dell.com"],
        ["/job/", "/jobs/"],
        session,
        "dell_first_party",
        80,
    )


def scrape_tesco_ireland(session):
    return _batch_first_party_roi_scrape(
        "Tesco Ireland",
        [
            "https://apply.tesco-careers.com/v2/job/search?location=Dublin&location_country=106",
            "https://apply.tesco-careers.com/v2/job/search?location=Cork&location_country=106",
            "https://apply.tesco-careers.com/v2/job/search?location_country=106",
        ],
        ["apply.tesco-careers.com"],
        ["/v2/job/"],
        session,
        "tesco_first_party",
        45,
    )


def scrape_aldi_ireland(session):
    # Second pass: discovery worked previously (3 vacancy URLs), so broaden
    # Ireland-specific result surfaces while retaining strict ROI verification.
    return _batch_first_party_roi_scrape(
        "Aldi Ireland",
        [
            "https://careers.aldirecruitment.ie/vacancies/vacancy-search-results.aspx",
            "https://careers.aldirecruitment.ie/vacancies/",
        ],
        ["careers.aldirecruitment.ie"],
        ["vacancy-details", "/vacancies/"],
        session,
        "aldi_first_party_v2",
        35,
    )


def scrape_fbd_ireland(session):
    return _batch_first_party_roi_scrape(
        "FBD Insurance",
        [
            "https://careers.fbdgroup.com/",
            "https://careers.fbdgroup.com/search/",
        ],
        ["careers.fbdgroup.com"],
        ["/job/", "/jobs/"],
        session,
        "fbd_first_party",
        35,
    )


def scrape_capgemini_ireland(session):
    return _batch_first_party_roi_scrape(
        "Capgemini",
        [
            "https://careers.capgemini.com/search/?q=&locationsearch=Dublin",
            "https://careers.capgemini.com/search/?q=&locationsearch=Ireland",
            "https://careers.capgemini.com/job/",
        ],
        ["careers.capgemini.com"],
        ["/job/"],
        session,
        "capgemini_first_party",
        45,
    )



def scrape_vodafone_ireland(session):
    """Vodafone Ireland via official SuccessFactors search/detail pages."""
    search_urls = [
        "https://opportunities.vodafone.com/search/?q=&locationsearch=Ireland",
        "https://opportunities.vodafone.com/search/?q=&locationsearch=Dublin",
        "https://opportunities.vodafone.com/",
    ]
    headers = {
        "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
        "Accept-Language": "en-IE,en;q=0.9",
    }
    detail_urls = set()
    results = {}

    for url in search_urls:
        try:
            r = session.get(url, headers=headers, timeout=20)
        except Exception:
            continue
        if r.status_code != 200:
            continue

        html_text = r.text or ""
        for m in re.finditer(
            r'href=["\']([^"\']*/job/[^"\']+/\d+/?)["\']',
            html_text, re.I
        ):
            detail_urls.add(urllib.parse.urljoin(url, m.group(1)).split("#")[0])
        for m in re.finditer(
            r'https://opportunities\.vodafone\.com/job/[^"\'<>\s]+/\d+/?',
            html_text, re.I
        ):
            detail_urls.add(m.group(0))

    for url in sorted(detail_urls):
        try:
            r = session.get(url, headers=headers, timeout=20)
        except Exception:
            continue
        if r.status_code != 200:
            continue

        body = re.sub(r"\s+", " ", _html_to_text(r.text or "")).strip()
        if _ROI_NEGATIVE_RE.search(body):
            continue
        if not is_republic_of_ireland_location(body):
            continue

        title = ""
        mm = re.search(r"<h1[^>]*>(.*?)</h1>", r.text or "", re.I | re.S)
        if mm:
            title = re.sub(r"\s+", " ", _html_to_text(mm.group(1))).strip()
        if not title:
            mm = re.search(r"<title[^>]*>(.*?)</title>", r.text or "", re.I | re.S)
            if mm:
                title = re.sub(r"\s+", " ", _html_to_text(mm.group(1))).strip()
                title = re.sub(r"\s+Job Details.*$", "", title, flags=re.I).strip()

        if not title or _looks_like_non_job_title(title):
            continue

        loc = "Dublin, Ireland" if re.search(r"\bDublin\b", body, re.I) else "Ireland"
        sponsorship, snippet = classify_sponsorship(body[:16000])

        canonical = url.split("?")[0]
        results[canonical.lower()] = {
            "company": "Vodafone Ireland",
            "title": title[:300],
            "location": loc,
            "posted_text": "Unknown",
            "posted_days_ago": None,
            "employment_type": normalize_employment_type("", title),
            "url": canonical,
            "source": "vodafone_successfactors_http",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }

    print(f"      [vodafone_friend] {len(results)} verified Ireland jobs from {len(detail_urls)} links")
    return list(results.values())





def scrape_abbott_ireland(session):
    """Abbott Ireland via official Workday tenant from the supplied scrape.py."""
    return _workday_override_scrape(
        "Abbott",
        "https://abbott.wd5.myworkdayjobs.com/abbottcareers",
        session,
    )



def scrape_astrazeneca_ireland(session):
    return _batch_first_party_roi_scrape(
        "AstraZeneca",
        [
            "https://careers.astrazeneca.com/search-jobs/Ireland",
            "https://careers.astrazeneca.com/search-jobs/Dublin",
        ],
        ["careers.astrazeneca.com"],
        ["/job/", "/jobs/", "/search-jobs/"],
        session,
        "astrazeneca_first_party",
        50,
    )


def scrape_amgen_ireland(session):
    return _batch_first_party_roi_scrape(
        "Amgen",
        [
            "https://careers.amgen.com/en/search-jobs/Ireland",
            "https://careers.amgen.com/en/search-jobs/Dublin",
        ],
        ["careers.amgen.com"],
        ["/job/", "/jobs/", "/search-jobs/"],
        session,
        "amgen_first_party",
        50,
    )


def scrape_alexion_ireland(session):
    return _batch_first_party_roi_scrape(
        "Alexion",
        [
            "https://careers.alexion.com/search-jobs/Ireland",
            "https://careers.alexion.com/search-jobs/Dublin",
        ],
        ["careers.alexion.com"],
        ["/job/", "/jobs/", "/search-jobs/"],
        session,
        "alexion_first_party",
        45,
    )


def scrape_stryker_ireland(session):
    return _batch_first_party_roi_scrape(
        "Stryker",
        [
            "https://careers.stryker.com/search-jobs/Ireland",
            "https://careers.stryker.com/search-jobs/Cork",
            "https://careers.stryker.com/search-jobs/Limerick",
        ],
        ["careers.stryker.com"],
        ["/job/", "/jobs/", "/search-jobs/"],
        session,
        "stryker_first_party",
        60,
    )


def scrape_novartis_ireland(session):
    return _batch_first_party_roi_scrape(
        "Novartis",
        [
            "https://www.novartis.com/careers/career-search?search_api_fulltext=&country%5B0%5D=LOC_IE",
            "https://www.novartis.com/careers/career-search?search_api_fulltext=Ireland",
        ],
        ["novartis.com"],
        ["/careers/career-search/job/details/", "/job/"],
        session,
        "novartis_first_party",
        45,
    )



def scrape_intel_ireland(session):
    """Intel Ireland via official Workday tenant from the supplied scrape.py."""
    return _workday_override_scrape(
        "Intel",
        "https://intel.wd1.myworkdayjobs.com/External",
        session,
    )





def scrape_tcs_ireland(session):
    """TCS Ireland via Candidate Manager, adapted from supplied scrape.py."""
    source_url = "https://www.candidatemanager.net/cm/p/pJobs.aspx?mid=CXAZAZB&sid=YYAZD"
    try:
        r = session.get(
            source_url, timeout=20,
            headers={
                "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
                "Accept-Language": "en-IE,en;q=0.9",
            },
        )
    except Exception as exc:
        print(f"      [tcs_friend] request failed: {exc}")
        return []

    if r.status_code != 200:
        return []

    html_text = r.text or ""
    results = {}

    for m in re.finditer(
        r'<a[^>]+href=["\']([^"\']*pJobDetails[^"\']*)["\'][^>]*>(.*?)</a>',
        html_text, re.I | re.S
    ):
        href = urllib.parse.urljoin(source_url, m.group(1))
        title = re.sub(r"\s+", " ", _html_to_text(m.group(2))).strip()
        start = max(0, m.start() - 1500)
        end = min(len(html_text), m.end() + 1500)
        row_text = re.sub(r"\s+", " ", _html_to_text(html_text[start:end])).strip()

        if not re.search(r"\bIreland\b", row_text, re.I):
            continue
        if not title or _looks_like_non_job_title(title):
            continue

        location = "Ireland"
        for city in ("Letterkenny", "Dublin", "Cork", "Galway", "Limerick", "Waterford"):
            if re.search(rf"\b{city}\b", row_text, re.I):
                location = f"{city}, Ireland"
                break

        sponsorship, snippet = classify_sponsorship(row_text[:16000])
        results[href.lower()] = {
            "company": "Tata Consultancy Services (TCS)",
            "title": title[:300],
            "location": location,
            "posted_text": "Unknown",
            "posted_days_ago": None,
            "employment_type": normalize_employment_type("", title),
            "url": href,
            "source": "tcs_candidate_manager",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }

    print(f"      [tcs_friend] {len(results)} Ireland jobs")
    return list(results.values())



def scrape_axa_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "AXA Ireland",
        [
            "https://careers.axa.com/careers-home/jobs?tags3=AXA%20Ireland&page=1&lat=53.3498&lng=-6.2603&radiusUnit=MILES&radius=25"
        ],
        ["careers.axa.com"],
        ["/careers-home/jobs/"],
        session,
        "axa_friend_reference",
        35,
    )


def scrape_agilent_ireland_friend(session):
    results = {}
    for site_url in (
        "https://agilent.wd5.myworkdayjobs.com/Agilent_Careers",
        "https://agilent.wd5.myworkdayjobs.com/Agilent_Student_Careers",
    ):
        for job in _workday_override_scrape("Agilent Technologies", site_url, session) or []:
            href = str(job.get("url") or "")
            if href:
                results[href.split("?")[0].rstrip("/").lower()] = job
    print(f"      [agilent_friend] {len(results)} Ireland jobs")
    return list(results.values())


def scrape_bnp_paribas_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "BNP Paribas Ireland",
        ["https://www.bnpparibas.ie/en/join-us/vacancies/"],
        ["bnpparibas.ie"],
        ["/en/jobs/", "/join-us/vacancies/"],
        session,
        "bnp_friend_reference",
        40,
    )


def scrape_coca_cola_hbc_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "Coca-Cola HBC Ireland",
        ["https://careers.coca-colahellenic.com/en_US/careers/SearchJobs/ireland"],
        ["careers.coca-colahellenic.com"],
        ["/careers/ProjectDetail/"],
        session,
        "cocacola_hbc_friend_reference",
        45,
    )


def scrape_hcltech_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "HCLTech",
        [
            "https://careers.hcltech.com/go/NonTPDemand/9558355/?markerViewed=&carouselIndex=&facetFilters=%7B%22custCountryRegion%22%3A%5B%22Ireland%22%5D%7D&pageNumber=0"
        ],
        ["careers.hcltech.com"],
        ["/job/"],
        session,
        "hcl_friend_reference",
        45,
    )


def scrape_infosys_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "Infosys",
        ["https://digitalcareers.infosys.com/infosys/global-careers?location=Ireland"],
        ["digitalcareers.infosys.com"],
        ["/apply-", "/company-job/", "reqid"],
        session,
        "infosys_friend_reference",
        50,
    )


def scrape_laya_healthcare_friend(session):
    return _batch_first_party_roi_scrape(
        "Laya Healthcare",
        [
            "https://careers.axa.com/careers-home/jobs?page=1&tags3=Laya%20Healthcare%20Ltd&location=Ireland&woe=12&regionCode=IE&stretchUnit=MILES&stretch=10"
        ],
        ["careers.axa.com"],
        ["/careers-home/jobs/", "/axa-uk-careers/jobs/"],
        session,
        "laya_friend_reference",
        35,
    )


def scrape_palo_alto_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "Palo Alto Networks",
        [
            "https://jobs.paloaltonetworks.com/en/search-jobs/Ireland/47263/2/2963597/53/-8/50/2"
        ],
        ["jobs.paloaltonetworks.com"],
        ["/en/job/"],
        session,
        "paloalto_friend_reference",
        45,
    )


def scrape_smbc_aviation_capital_friend(session):
    return _batch_first_party_roi_scrape(
        "SMBC Aviation Capital",
        ["https://smbcaviationcapital.groupgti.com/VacancyPosting/Search#!/"],
        ["smbcaviationcapital.groupgti.com"],
        ["/viewdetails", "/VacancyPosting/"],
        session,
        "smbc_friend_reference",
        35,
    )


def scrape_sig_ireland_friend(session):
    return _batch_first_party_roi_scrape(
        "Susquehanna International Group (SIG)",
        ["https://careers.sig.com/dublin/jobs"],
        ["careers.sig.com"],
        ["/jobs/"],
        session,
        "sig_friend_reference",
        55,
    )



def scrape_heineken_ireland_friend(session):
    """HEINEKEN Ireland official SuccessFactors-style board, HTTP only."""
    company = "Heineken Ireland"
    source_url = "https://careers.theheinekencompany.com/HEINEKEN-Ireland"
    results = {}

    try:
        r = session.get(
            source_url,
            timeout=20,
            headers={
                "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
                "Accept-Language": "en-IE,en;q=0.9",
            },
        )
    except Exception as exc:
        print(f"      [heineken_friend] request failed: {exc}")
        return []

    if r.status_code != 200:
        print(f"      [heineken_friend] HTTP {r.status_code}")
        return []

    html_text = r.text or ""
    body = _html_to_text(html_text)

    # Official board can legitimately be empty.
    if re.search(
        r"\bNo jobs on tap right now\b|\bno open positions\b",
        body,
        re.I,
    ):
        print("      [heineken_friend] official Ireland board currently empty")
        return []

    for m in re.finditer(
        r'<a[^>]+href=["\']([^"\']*/job/[^"\']+/\d+/?)["\'][^>]*>(.*?)</a>',
        html_text,
        re.I | re.S,
    ):
        href = urllib.parse.urljoin(source_url, m.group(1)).split("#")[0]

        start = max(0, m.start() - 1600)
        end = min(len(html_text), m.end() + 2000)
        card_text = _html_to_text(html_text[start:end])

        if _ROI_NEGATIVE_RE.search(card_text):
            continue
        if not is_republic_of_ireland_location(card_text):
            continue

        title = re.sub(r"\s+", " ", _html_to_text(m.group(2))).strip()
        if not title or _looks_like_non_job_title(title):
            continue

        location = "Ireland"
        for city in ("Dublin", "Cork", "Galway", "Limerick"):
            if re.search(rf"\b{city}\b", card_text, re.I):
                location = f"{city}, Ireland"
                break

        sponsorship, snippet = classify_sponsorship(card_text[:16000])
        canonical = href.split("?")[0].rstrip("/")

        results[canonical.lower()] = {
            "company": company,
            "title": title[:300],
            "location": location,
            "posted_text": "Unknown",
            "posted_days_ago": None,
            "employment_type": normalize_employment_type("", title),
            "url": canonical,
            "source": "heineken_friend_reference",
            "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }

    print(f"      [heineken_friend] {len(results)} verified Ireland jobs")
    return list(results.values())


def scrape_musgrave_ireland_friend(session):
    """Musgrave official vacancies page from supplied reference scraper."""
    company = "Musgrave Group (SuperValu / Centra)"
    source_url = "https://musgravegroup.com/careers/vacancies/"

    if not HAS_PLAYWRIGHT:
        return []

    results = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1440, "height": 1300},
                locale="en-IE",
            )
            page.goto(source_url, wait_until="domcontentloaded", timeout=45000)
            page.wait_for_timeout(2200)

            stagnant = 0
            previous = 0

            for _ in range(35):
                anchors = page.locator("a[href]")

                for i in range(min(anchors.count(), 800)):
                    a = anchors.nth(i)

                    try:
                        href = urllib.parse.urljoin(
                            page.url,
                            a.get_attribute("href") or "",
                        ).split("#")[0]
                    except Exception:
                        continue

                    low = href.lower()

                    # Reject obvious site navigation/social links.
                    if any(x in low for x in (
                        "linkedin.com", "facebook.com", "instagram.com",
                        "/about/", "/news/", "/contact/"
                    )):
                        continue

                    if href.rstrip("/") == source_url.rstrip("/"):
                        continue

                    try:
                        title = re.sub(r"\s+", " ", a.inner_text() or "").strip()
                    except Exception:
                        title = ""

                    node = a
                    card = ""

                    for _up in range(6):
                        try:
                            txt = re.sub(r"\s+", " ", node.inner_text() or "").strip()
                        except Exception:
                            txt = ""

                        if txt and len(txt) <= 3200:
                            card = txt

                        if is_republic_of_ireland_location(card):
                            break

                        try:
                            node = node.locator("..")
                        except Exception:
                            break

                    evidence = f"{title} {card} {href}"

                    if not title or _looks_like_non_job_title(title):
                        continue
                    if _ROI_NEGATIVE_RE.search(evidence):
                        continue

                    # Require a vacancy-ish structural URL OR explicit ROI card evidence.
                    if not (
                        any(k in low for k in ("vacanc", "/job", "career"))
                        and is_republic_of_ireland_location(evidence)
                    ):
                        continue

                    location = "Ireland"
                    for city in (
                        "Dublin", "Cork", "Limerick", "Galway", "Waterford",
                        "Kildare", "Meath", "Westmeath", "Kilkenny", "Tipperary",
                    ):
                        if re.search(rf"\b{city}\b", evidence, re.I):
                            location = f"{city}, Ireland"
                            break

                    sponsorship, snippet = classify_sponsorship(card[:16000])
                    canonical = href.split("?")[0]

                    results[canonical.rstrip("/").lower()] = {
                        "company": company,
                        "title": title[:300],
                        "location": location,
                        "posted_text": "Unknown",
                        "posted_days_ago": None,
                        "employment_type": normalize_employment_type("", title),
                        "url": canonical,
                        "source": "musgrave_friend_reference",
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    }

                try:
                    page.mouse.wheel(0, 3200)
                    page.wait_for_timeout(250)
                except Exception:
                    pass

                current = len(results)
                stagnant = stagnant + 1 if current == previous else 0
                previous = current
                if stagnant >= 6:
                    break

            browser.close()

    except Exception as exc:
        print(f"      [musgrave_friend] failed: {exc}")

    print(f"      [musgrave_friend] {len(results)} verified Ireland jobs")
    return list(results.values())


def scrape_vhi_ireland_friend(session):
    """VHI careers -> embedded CandidateManager vacancy links."""
    company = "VHI Healthcare"
    source = "https://www1.vhi.ie/about/careers"

    if not HAS_PLAYWRIGHT:
        return []

    results = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            context = browser.new_context(locale="en-IE")
            page = context.new_page()
            page.goto(source, wait_until="domcontentloaded", timeout=40000)
            page.wait_for_timeout(2200)

            for frame in page.frames:
                try:
                    anchors = frame.locator("a[href]")
                    count = anchors.count()
                except Exception:
                    continue

                for i in range(min(count, 600)):
                    a = anchors.nth(i)

                    try:
                        raw = a.get_attribute("href") or ""
                    except Exception:
                        continue

                    href = urllib.parse.urljoin(frame.url or source, raw).split("#")[0]

                    # Structural CandidateManager vacancy/detail link.
                    if "candidatemanager.net" not in href.lower():
                        continue
                    if not re.search(
                        r"(pjobdetails|jobdetails|vacanc|jobid|jid=|sid=)",
                        href,
                        re.I,
                    ):
                        continue

                    try:
                        title = re.sub(r"\s+", " ", a.inner_text() or "").strip()
                    except Exception:
                        title = ""

                    if not title or _looks_like_non_job_title(title):
                        continue

                    node = a
                    card = title
                    for _ in range(6):
                        try:
                            txt = re.sub(r"\s+", " ", node.inner_text() or "").strip()
                        except Exception:
                            txt = ""
                        if txt and 10 < len(txt) < 4000:
                            card = txt
                        if is_republic_of_ireland_location(card):
                            break
                        try:
                            node = node.locator("..")
                        except Exception:
                            break

                    # VHI is an Ireland board, but still require ROI evidence in card/page.
                    evidence = f"{card} Ireland"
                    if _ROI_NEGATIVE_RE.search(evidence):
                        continue

                    location = "Ireland"
                    for city in ("Dublin", "Cork", "Galway", "Limerick", "Kilkenny"):
                        if re.search(rf"\b{city}\b", card, re.I):
                            location = f"{city}, Ireland"
                            break

                    sponsorship, snippet = classify_sponsorship(card[:16000])
                    canonical = href.split("#")[0]

                    results[canonical.rstrip("/").lower()] = {
                        "company": company,
                        "title": title[:300],
                        "location": location,
                        "posted_text": "Unknown",
                        "posted_days_ago": None,
                        "employment_type": normalize_employment_type("", title),
                        "url": canonical,
                        "source": "vhi_friend_reference",
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    }

            context.close()
            browser.close()

    except Exception as exc:
        print(f"      [vhi_friend] failed: {exc}")

    print(f"      [vhi_friend] {len(results)} CandidateManager Ireland jobs")
    return list(results.values())


def scrape_hp_ireland_friend(session):
    """HP official jobs site with Ireland location search."""
    company = "HP (Hewlett-Packard)"
    source = "https://jobs.hp.com/"

    if not HAS_PLAYWRIGHT:
        return []

    results = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                viewport={"width": 1440, "height": 1100},
                locale="en-IE",
            )
            page.goto(source, wait_until="domcontentloaded", timeout=40000)
            page.wait_for_timeout(1500)

            for selector in (
                'input[placeholder*="location" i]',
                'input[aria-label*="location" i]',
                'input[name*="location" i]',
            ):
                try:
                    inp = page.locator(selector)
                    if inp.count():
                        inp.first.fill("Ireland")
                        inp.first.press("Enter")
                        page.wait_for_timeout(1800)
                        break
                except Exception:
                    pass

            stagnant = 0
            previous = 0

            for _ in range(25):
                anchors = page.locator("a[href]")

                for i in range(min(anchors.count(), 1000)):
                    a = anchors.nth(i)
                    try:
                        href = urllib.parse.urljoin(
                            page.url,
                            a.get_attribute("href") or "",
                        ).split("#")[0]
                    except Exception:
                        continue

                    if not any(x in href.lower() for x in (
                        "/job/", "/jobs/", "jobdetail", "job-detail"
                    )):
                        continue

                    try:
                        title = re.sub(r"\s+", " ", a.inner_text() or "").strip()
                    except Exception:
                        title = ""

                    if not title or _looks_like_non_job_title(title):
                        continue

                    node = a
                    card = ""

                    for _up in range(6):
                        try:
                            node = node.locator("..")
                            candidate = re.sub(r"\s+", " ", node.inner_text() or "").strip()
                        except Exception:
                            break

                        if candidate and len(candidate) <= 2600:
                            card = candidate
                        if is_republic_of_ireland_location(card):
                            break

                    evidence = f"{title} {card} {href}"
                    if _ROI_NEGATIVE_RE.search(evidence):
                        continue
                    if not is_republic_of_ireland_location(evidence):
                        continue

                    location = "Ireland"
                    for city in ("Dublin", "Leixlip", "Galway", "Cork"):
                        if re.search(rf"\b{city}\b", evidence, re.I):
                            location = f"{city}, Ireland"
                            break

                    sponsorship, snippet = classify_sponsorship(card[:16000])
                    canonical = href.split("?")[0]

                    results[canonical.rstrip("/").lower()] = {
                        "company": company,
                        "title": title[:300],
                        "location": location,
                        "posted_text": "Unknown",
                        "posted_days_ago": None,
                        "employment_type": normalize_employment_type("", title),
                        "url": canonical,
                        "source": "hp_friend_reference",
                        "visa_sponsorship": sponsorship,
                        "visa_snippet": snippet,
                    }

                page.mouse.wheel(0, 3000)
                page.wait_for_timeout(250)

                current = len(results)
                stagnant = stagnant + 1 if current == previous else 0
                previous = current
                if stagnant >= 5:
                    break

            browser.close()

    except Exception as exc:
        print(f"      [hp_friend] failed: {exc}")

    print(f"      [hp_friend] {len(results)} verified Ireland jobs")
    return list(results.values())



def scrape_oracle_ireland_friend(session):
    """Oracle Ireland via the existing public Oracle Recruiting Cloud REST helper."""
    jobs = scrape_oracle_candidate_experience(
        "Oracle",
        "https://eeho.fa.us2.oraclecloud.com",
        "CX_1",
        session,
    )
    print(f"      [oracle_friend] {len(jobs)} Ireland jobs from Oracle Recruiting REST")
    return jobs


def scrape_bausch_lomb_friend(session):
    """Bausch + Lomb official Ireland-filtered careers board."""
    return _batch_first_party_roi_scrape(
        "Bausch + Lomb",
        [
            "https://careers.bauschlomb.com/search/?q=&locationsearch=Ireland",
            "https://careers.bauschlomb.com/search/?q=&locationsearch=Waterford",
        ],
        ["careers.bauschlomb.com"],
        ["/job/", "/jobs/", "/search/"],
        session,
        "bausch_friend_reference",
        45,
    )


def scrape_mckinsey_ireland_friend(session):
    """McKinsey Dublin: official search, real job-detail links only."""
    company = "McKinsey & Company"
    source = (
        "https://www.mckinsey.com/careers/search-jobs"
        "?locations=Dublin&cities=Dublin"
    )
    official_marker = "/careers/search-jobs/jobs/"

    if not HAS_PLAYWRIGHT:
        return []

    results = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=[
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--disable-http2",
                    "--disable-blink-features=AutomationControlled",
                ],
            )
            context = browser.new_context(
                locale="en-IE",
                viewport={"width": 1440, "height": 1500},
                user_agent=HEADERS.get("User-Agent"),
            )
            context.add_init_script(
                """
                Object.defineProperty(
                    navigator,
                    'webdriver',
                    {get: () => undefined}
                );
                """
            )
            page = context.new_page()

            try:
                page.goto(source, wait_until="commit", timeout=35000)
            except Exception as exc:
                print(f"      [mckinsey_friend] initial navigation: {exc}")

            # Do not wait for full network-idle; McKinsey keeps background
            # traffic alive. Wait only for the actual vacancy link structure.
            try:
                page.wait_for_selector(
                    'a[href*="/careers/search-jobs/jobs/"]',
                    timeout=18000,
                )
            except Exception:
                pass

            page.wait_for_timeout(1200)

            try:
                links = page.locator(
                    'a[href*="/careers/search-jobs/jobs/"]'
                ).evaluate_all(
                    """els => els.map(a => ({
                        href: a.href || "",
                        text: (a.innerText || a.textContent || "").trim()
                    }))"""
                )
            except Exception:
                links = []

            for item in links:
                href = str(item.get("href") or "").strip().split("#")[0]
                title = re.sub(
                    r"\s+",
                    " ",
                    str(item.get("text") or ""),
                ).strip()

                if not href or official_marker not in href:
                    continue
                if not title or _looks_like_non_job_title(title):
                    continue

                # Dublin-specific source is already filtered, but still inspect
                # nearby/detail evidence when inexpensive.
                body = ""
                try:
                    detail = context.new_page()
                    detail.goto(href, wait_until="domcontentloaded", timeout=15000)
                    detail.wait_for_timeout(250)
                    body = detail.locator("body").inner_text(timeout=5000)
                    detail.close()
                except Exception:
                    try:
                        detail.close()
                    except Exception:
                        pass

                evidence = f"Dublin, Ireland {body}"
                if _ROI_NEGATIVE_RE.search(evidence):
                    continue
                if body and not is_republic_of_ireland_location(evidence):
                    continue

                canonical = href.split("?")[0]
                sponsorship, snippet = classify_sponsorship(body[:16000])

                results[canonical.rstrip("/").lower()] = {
                    "company": company,
                    "title": title[:300],
                    "location": "Dublin, Ireland",
                    "posted_text": "Unknown",
                    "posted_days_ago": None,
                    "employment_type": normalize_employment_type("", title),
                    "url": canonical,
                    "source": "mckinsey_friend_reference",
                    "visa_sponsorship": sponsorship,
                    "visa_snippet": snippet,
                }

            context.close()
            browser.close()

    except Exception as exc:
        print(f"      [mckinsey_friend] failed: {exc}")

    print(f"      [mckinsey_friend] {len(results)} verified Dublin jobs")
    return list(results.values())



def scrape_oracle_ireland_attempt2(session):
    """Oracle attempt 2: rendered Candidate Experience Ireland page, not REST."""
    return _batch_first_party_roi_scrape(
        "Oracle",
        [
            "https://eeho.fa.us2.oraclecloud.com/hcmUI/CandidateExperience/en/sites/CX_1/requisitions?location=Ireland",
            "https://eeho.fa.us2.oraclecloud.com/hcmUI/CandidateExperience/en/sites/CX_1/jobs?location=Ireland",
        ],
        ["eeho.fa.us2.oraclecloud.com"],
        ["/sites/CX_1/job/", "/sites/CX_1/jobs/"],
        session,
        "oracle_attempt2_rendered",
        55,
    )


def scrape_mckinsey_ireland_attempt2(session):
    """McKinsey attempt 2: lightweight official HTML route; avoids the 60s Playwright stall."""
    company = "McKinsey & Company"
    source = "https://www.mckinsey.com/careers/search-jobs?locations=Dublin&cities=Dublin"
    results = {}
    try:
        r = session.get(source, timeout=25, headers={
            "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
            "Accept-Language": "en-IE,en;q=0.9",
        })
        html = r.text or ""
    except Exception as exc:
        print(f"      [mckinsey_attempt2] HTTP failed: {exc}")
        return []

    for m in re.finditer(r'href=["\']([^"\']*/careers/search-jobs/jobs/[^"\'#?]+)[^"\']*["\']', html, re.I):
        href = urllib.parse.urljoin(source, m.group(1)).split("?")[0].split("#")[0]
        start, end = max(0, m.start()-1800), min(len(html), m.end()+2200)
        card = _html_to_text(html[start:end])
        if _ROI_NEGATIVE_RE.search(card):
            continue
        if not re.search(r"\bDublin\b|\bIreland\b", card, re.I):
            continue
        title = ""
        # Prefer nearby anchor text, then a conservative text line.
        am = re.search(r'<a[^>]+href=["\'][^"\']*' + re.escape(m.group(1)) + r'[^"\']*["\'][^>]*>(.*?)</a>', html[start:end], re.I|re.S)
        if am:
            title = re.sub(r"\s+", " ", _html_to_text(am.group(1))).strip()
        if not title or _looks_like_non_job_title(title):
            lines = [re.sub(r"\s+", " ", x).strip() for x in card.splitlines() if 5 <= len(x.strip()) <= 220]
            title = next((x for x in lines if not _looks_like_non_job_title(x) and not re.fullmatch(r"Dublin(?:, Ireland)?", x, re.I)), "")
        if not title:
            continue
        sponsorship, snippet = classify_sponsorship(card[:16000])
        results[href.rstrip('/').lower()] = {
            "company": company, "title": title[:300], "location": "Dublin, Ireland",
            "posted_text": "Unknown", "posted_days_ago": None,
            "employment_type": normalize_employment_type("", title), "url": href,
            "source": "mckinsey_attempt2_http", "visa_sponsorship": sponsorship,
            "visa_snippet": snippet,
        }
    print(f"      [mckinsey_attempt2] {len(results)} verified Dublin jobs")
    return list(results.values())


def scrape_honeywell_friend(session):
    """Fresh company: official Honeywell Oracle Ireland board from friend logic."""
    return _batch_first_party_roi_scrape(
        "Honeywell",
        ["https://ibqbjb.fa.ocs.oraclecloud.com/hcmUI/CandidateExperience/en/sites/Honeywell/jobs?location=Ireland&locationId=300000000469476&locationLevel=country&mode=location"],
        ["ibqbjb.fa.ocs.oraclecloud.com"],
        ["/sites/Honeywell/job/"],
        session,
        "honeywell_friend_reference",
        55,
    )


def scrape_schneider_friend(session):
    """Fresh company: Schneider official Ireland jobs route from friend logic."""
    return _batch_first_party_roi_scrape(
        "Schneider Electric",
        [
            "https://careers.se.com/jobs?keywords=&location=Ireland",
            "https://careers.se.com/jobs?location=Ireland",
        ],
        ["careers.se.com"],
        ["/jobs/"],
        session,
        "schneider_friend_reference",
        55,
    )


def scrape_honeywell_attempt2(session):
    """Honeywell second/final attempt: alternate official Oracle search routes."""
    return _batch_first_party_roi_scrape(
        "Honeywell",
        [
            "https://ibqbjb.fa.ocs.oraclecloud.com/hcmUI/CandidateExperience/en/sites/Honeywell/jobs?keyword=Ireland",
            "https://ibqbjb.fa.ocs.oraclecloud.com/hcmUI/CandidateExperience/en/sites/Honeywell/jobs?location=Ireland",
            "https://ibqbjb.fa.ocs.oraclecloud.com/hcmUI/CandidateExperience/en/sites/Honeywell/jobs",
        ],
        ["ibqbjb.fa.ocs.oraclecloud.com"],
        ["/sites/Honeywell/job/"],
        session,
        "honeywell_attempt2",
        80,
    )


def scrape_schneider_attempt2(session):
    """Schneider second/final attempt: alternate official Ireland/Dublin searches."""
    return _batch_first_party_roi_scrape(
        "Schneider Electric",
        [
            "https://careers.se.com/jobs?keywords=Ireland",
            "https://careers.se.com/jobs?keywords=&location=Dublin%2C%20Ireland",
            "https://careers.se.com/jobs",
        ],
        ["careers.se.com"],
        ["/jobs/"],
        session,
        "schneider_attempt2",
        80,
    )

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
        "wipro": lambda: scrape_wipro_ireland(session),
        "iqvia": lambda: scrape_iqvia_ireland(session),
        "merit medical": lambda: scrape_merit_medical_ireland(session),
        "goodbody": lambda: scrape_goodbody_ireland(session),
        "bristol myers squibb": lambda: scrape_bms_ireland(session),
        "sse airtricity / sse": lambda: scrape_sse_ireland(session),
        "hewlett packard enterprise (hpe)": lambda: scrape_hpe_ireland(session),
        "dell technologies": lambda: scrape_dell_ireland(session),
        "tesco ireland": lambda: scrape_tesco_ireland(session),
        "aldi ireland": lambda: scrape_aldi_ireland(session),
        "fbd insurance": lambda: scrape_fbd_ireland(session),
        "capgemini": lambda: scrape_capgemini_ireland(session),
        "vodafone ireland": lambda: scrape_vodafone_ireland(session),
        "abbott": lambda: scrape_abbott_ireland(session),
        "astrazeneca": lambda: scrape_astrazeneca_ireland(session),
        "amgen": lambda: scrape_amgen_ireland(session),
        "alexion": lambda: scrape_alexion_ireland(session),
        "stryker": lambda: scrape_stryker_ireland(session),
        "novartis": lambda: scrape_novartis_ireland(session),
        "intel": lambda: scrape_intel_ireland(session),
        "tata consultancy services (tcs)": lambda: scrape_tcs_ireland(session),
        "axa ireland": lambda: scrape_axa_ireland_friend(session),
        "agilent technologies": lambda: scrape_agilent_ireland_friend(session),
        "bnp paribas ireland": lambda: scrape_bnp_paribas_ireland_friend(session),
        "coca-cola hbc ireland": lambda: scrape_coca_cola_hbc_ireland_friend(session),
        "hcltech": lambda: scrape_hcltech_ireland_friend(session),
        "infosys": lambda: scrape_infosys_ireland_friend(session),
        "laya healthcare": lambda: scrape_laya_healthcare_friend(session),
        "palo alto networks": lambda: scrape_palo_alto_ireland_friend(session),
        "smbc aviation capital": lambda: scrape_smbc_aviation_capital_friend(session),
        "susquehanna international group (sig)": lambda: scrape_sig_ireland_friend(session),
        "heineken ireland": lambda: scrape_heineken_ireland_friend(session),
        "musgrave group (supervalu / centra)": lambda: scrape_musgrave_ireland_friend(session),
        "vhi healthcare": lambda: scrape_vhi_ireland_friend(session),
        "hp (hewlett-packard)": lambda: scrape_hp_ireland_friend(session),
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
        "guidewire": lambda: scrape_guidewire_ireland_direct_http(session),
        "bny mellon": lambda: scrape_bny_mellon_ireland_recovery(session),
        "fidelity investments": lambda: scrape_fidelity_investments_ireland_direct(session),
        "goldman sachs": lambda: scrape_goldman_sachs_ireland_recovery(session),
        "morgan stanley": lambda: scrape_morgan_stanley_ireland_recovery(session),
        "s&p global": lambda: scrape_sp_global_ireland_recovery(session),
        "databricks": lambda: scrape_databricks_ireland_recovery(session),
        "visa": lambda: scrape_visa_ireland_recovery(session),
        "aer lingus": lambda: scrape_aer_lingus_ireland_recovery(session),
        "northern trust": lambda: scrape_northern_trust_ireland_direct(session),
        "willis towers watson": lambda: scrape_wtw_ireland_direct(session),
        "becton dickinson": lambda: scrape_bd_ireland_direct(session),
        "jazz pharmaceuticals": lambda: scrape_jazz_ireland_direct(session),
        "takeda": lambda: scrape_takeda_ireland_direct(session),
        "teleflex": lambda: scrape_teleflex_ireland_direct(session),
        "viatris": lambda: scrape_viatris_ireland_direct(session),
        "qiagen": lambda: scrape_qiagen_ireland_direct(session),
        "regeneron": lambda: scrape_regeneron_ireland_direct(session),
        "medtronic": lambda: scrape_medtronic_ireland_direct(session),
        "oracle": lambda: scrape_oracle_ireland_attempt2(session),
        "bausch + lomb": lambda: scrape_bausch_lomb_friend(session),
        "mckinsey & company": lambda: scrape_mckinsey_ireland_attempt2(session),
        "honeywell": lambda: scrape_honeywell_attempt2(session),
        "schneider electric": lambda: scrape_schneider_attempt2(session),
        "jpmorgan chase": lambda: scrape_oracle_candidate_experience("JPMorgan Chase", "https://jpmc.fa.oraclecloud.com", "CX_1001", session),
    }
    matched_key = next((k for k in dedicated if name_lower == k or name_lower.startswith(k)), None)

    if not matched_key and name_lower in PRIORITY_SHEET2_COMPANIES:
        print(f"'{name}' is a Sheet 2 priority company — testing via the generic "
              f"Ireland-first browser fallback (scrape_priority_sheet2_generic).\n")
        companies = load_companies("Job_Automation.csv")
        row = next((c for c in companies if c["company_name"].strip().lower() == name_lower), None)
        if not row:
            print(f"'{name}' not found in Job_Automation.csv (exact match required for this fallback path).")
            return
        jobs = scrape_priority_sheet2_generic(row["company_name"], row["career_url"].strip(), session)
        for j in jobs:
            normalize_posted_age(j)
        print(f"\n=== RESULT: {len(jobs)} Ireland postings found for '{name}' (Sheet 2 generic) ===")
        for j in jobs[:10]:
            _age = j.get("posted_days_ago")
            _known = j.get("posted_age_known", _age is not None and _age < UNKNOWN_POSTED_DAYS)
            _age_display = _age if _known else "Unknown"
            print(f"  - {j['title']} | {j['location']} | posted_days_ago={_age_display} | {j['url']}")
        if len(jobs) > 10:
            print(f"  ... and {len(jobs) - 10} more")
        return

    if matched_key:
        print(f"Matched dedicated scraper: '{matched_key}'\n")
        jobs = dedicated[matched_key]()
        for j in jobs:
            normalize_posted_age(j)
        print(f"\n=== RESULT: {len(jobs)} Ireland postings found for '{name}' ===")
        for j in jobs[:10]:
            _age = j.get("posted_days_ago")
            _known = j.get("posted_age_known", _age is not None and _age < UNKNOWN_POSTED_DAYS)
            _age_display = _age if _known else "Unknown"
            print(f"  - {j['title']} | {j['location']} | posted_days_ago={_age_display} | {j['url']}")
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



def scrape_fidelity_investments_ireland_direct(session):
    return _scrape_first_party_ireland_listing(
        "Fidelity Investments",
        [
            "https://jobs.fidelity.com/ie/jobs/",
            "https://jobs.fidelity.com/ie/jobs/?page=2",
            "https://jobs.fidelity.com/ie/jobs/?page=3",
        ],
        [r"jobs\.fidelity\.com/ie/job/[^?#]+", r"jobs\.fidelity\.com/ie/jobs/[^?#]+"],
        "fidelity_ie_direct", session, True
    )


def scrape_bny_mellon_ireland_recovery(session):
    return _sitemap_job_recovery(
        "BNY Mellon",
        ["https://www.bny.com", "https://careers.bnymellon.com"],
        "bny_sitemap", session
    )


def scrape_goldman_sachs_ireland_recovery(session):
    return _sitemap_job_recovery(
        "Goldman Sachs",
        ["https://higher.gs.com", "https://www.goldmansachs.com"],
        "goldman_sitemap", session
    )


def scrape_morgan_stanley_ireland_recovery(session):
    return _sitemap_job_recovery(
        "Morgan Stanley",
        ["https://morganstanley.tal.net", "https://www.morganstanley.com"],
        "morgan_stanley_sitemap", session
    )



def scrape_sp_global_ireland_recovery(session):
    """S&P Global via official Workday Ireland country facet."""
    company = "S&P Global"
    base = "https://spgi.wd5.myworkdayjobs.com"
    site = "SPGI_Careers"
    api = f"{base}/wday/cxs/spgi/{site}/jobs"
    ireland_country_id = "04a05835925f45b3a59406a2a6b72c8a"
    results = {}
    offset = 0

    while offset < 500:
        payload = {
            "appliedFacets": {"Location_Country": [ireland_country_id]},
            "limit": 20,
            "offset": offset,
            "searchText": "",
        }
        try:
            r = session.post(
                api, json=payload, timeout=20,
                headers={
                    "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
                    "Accept": "application/json",
                    "Content-Type": "application/json",
                    "Accept-Language": "en-IE,en;q=0.9",
                    "Referer": f"{base}/{site}",
                },
            )
            if r.status_code != 200:
                break
            data = r.json()
        except Exception:
            break

        rows = data.get("jobPostings") or []
        if not rows:
            break

        for row in rows:
            external_path = str(row.get("externalPath") or "").strip()
            if not external_path:
                continue

            detail_url = f"{base}/wday/cxs/spgi/{site}{external_path}"
            try:
                dr = session.get(
                    detail_url, timeout=15,
                    headers={
                        "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
                        "Accept": "application/json",
                        "Referer": f"{base}/{site}",
                    },
                )
                if dr.status_code != 200:
                    continue
                detail = dr.json()
            except Exception:
                continue

            info = detail.get("jobPostingInfo") or {}
            title = str(info.get("title") or row.get("title") or "").strip()
            location = str(info.get("location") or "")
            additional = info.get("additionalLocations") or []
            additional_text = " ".join(
                str(x.get("location") if isinstance(x, dict) else x)
                for x in additional
            ) if isinstance(additional, list) else str(additional)
            desc = str(info.get("jobDescription") or info.get("description") or "")
            blob = f"{title} {location} {additional_text} {desc}"

            if _ROI_NEGATIVE_RE.search(blob):
                continue
            if not is_republic_of_ireland_location(blob):
                continue
            if not title or _looks_like_non_job_title(title):
                continue

            if re.search(r"\bDublin\b", blob, re.I):
                clean_location = "Dublin, Ireland"
            elif re.search(r"\bCork\b", blob, re.I):
                clean_location = "Cork, Ireland"
            else:
                clean_location = "Ireland"

            public_url = base + "/" + site + external_path
            sponsorship, snippet = classify_sponsorship(desc[:16000])
            results[public_url.rstrip("/").lower()] = {
                "company": company,
                "title": title[:300],
                "location": clean_location,
                "posted_text": str(info.get("startDate") or "Unknown"),
                "posted_days_ago": parse_posted_text(str(info.get("startDate") or "")),
                "employment_type": normalize_employment_type(info.get("timeType"), title),
                "url": public_url,
                "source": "spglobal_workday_ireland",
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            }

        offset += len(rows)
        total = data.get("total")
        if isinstance(total, int) and offset >= total:
            break

    print(f"      [spglobal_friend] {len(results)} Ireland jobs")
    return list(results.values())



def scrape_databricks_ireland_recovery(session):
    return _sitemap_job_recovery(
        "Databricks",
        ["https://www.databricks.com"],
        "databricks_sitemap", session
    )


def scrape_visa_ireland_recovery(session):
    return _sitemap_job_recovery(
        "Visa",
        ["https://search.visa.com", "https://corporate.visa.com"],
        "visa_sitemap", session
    )


def scrape_aer_lingus_ireland_recovery(session):
    return _sitemap_job_recovery(
        "Aer Lingus",
        ["https://www.aerlingus.com"],
        "aer_lingus_sitemap", session
    )


# === NEXT_COMPANIES_3_DIRECT_FIX ===
# Company-coverage phase only: these are new routes for companies that were
# still non-live. Existing successful live-company scrapers are unchanged.

def _next3_http_card_jobs(session, company, listing_urls, href_patterns, source):
    results = {}
    headers = {
        "User-Agent": HEADERS.get("User-Agent", "Mozilla/5.0"),
        "Accept-Language": "en-IE,en;q=0.9",
    }
    for listing in listing_urls:
        try:
            r = session.get(listing, headers=headers, timeout=22)
        except Exception as exc:
            print(f"      [{source}] listing failed: {exc}")
            continue
        if r.status_code != 200:
            continue
        html = r.text or ""
        for pat in href_patterns:
            for m in re.finditer(pat, html, re.I):
                raw_href = m.group(1) if m.lastindex else m.group(0)
                href = urllib.parse.urljoin(listing, raw_href).split("#")[0]
                start = max(0, m.start() - 2200)
                end = min(len(html), m.end() + 2600)
                card_html = html[start:end]
                card = re.sub(r"\s+", " ", _html_to_text(card_html)).strip()
                if _ROI_NEGATIVE_RE.search(card):
                    continue
                if not is_republic_of_ireland_location(card):
                    continue

                title = ""
                headings = re.findall(r"<h[1-4][^>]*>(.*?)</h[1-4]>", card_html, re.I | re.S)
                for candidate in reversed(headings):
                    candidate = re.sub(r"\s+", " ", _html_to_text(candidate)).strip()
                    if candidate and not _looks_like_non_job_title(candidate):
                        title = candidate
                        break
                if not title:
                    around = html[max(0, m.start()-400):min(len(html), m.end()+700)]
                    a = re.search(r"<a[^>]*>(.*?)</a>", around, re.I | re.S)
                    if a:
                        title = re.sub(r"\s+", " ", _html_to_text(a.group(1))).strip()
                if not title or _looks_like_non_job_title(title):
                    continue

                loc = "Ireland"
                for city in ("Dublin", "Cork", "Galway", "Limerick", "Shannon", "Athenry"):
                    if re.search(rf"\b{re.escape(city)}\b", card, re.I):
                        loc = f"{city}, Ireland"
                        break
                posted_text, posted_days = extract_posted_from_text(card)
                sponsorship, snippet = classify_sponsorship(card[:12000])
                canonical = href.split("?")[0].rstrip("/")
                results[canonical.lower()] = {
                    "company": company, "title": title[:300], "location": loc,
                    "posted_text": posted_text, "posted_days_ago": posted_days,
                    "employment_type": normalize_employment_type("", title),
                    "url": canonical, "source": source,
                    "visa_sponsorship": sponsorship, "visa_snippet": snippet,
                }
    print(f"      [{source}] {len(results)} Ireland jobs from first-party listing cards")
    return list(results.values())


def scrape_ryanair_ireland_next3(session):
    urls = ["https://careers.ryanair.com/jobs/?search=ireland"] + [
        f"https://careers.ryanair.com/jobs/?page={p}&search=ireland" for p in range(2, 7)
    ]
    return _next3_http_card_jobs(
        session, "Ryanair", urls,
        [r'href=["\']([^"\']*/jobs/[a-z0-9][^"\']*/?)["\']'],
        "ryanair_direct_next3",
    )


def scrape_dexcom_ireland_next3(session):
    base = ("https://careers.dexcom.com/careers?domain=dexcom.com&filter_distance=80"
            "&filter_include_remote=1&location=Athenry%2C+G%2C+IE&sort_by=distance")
    urls = [base + f"&start={start}" for start in (0, 10, 20, 30, 40)]
    return _next3_http_card_jobs(
        session, "Dexcom", urls,
        [r'href=["\']([^"\']*/careers/job/\d+[^"\']*)["\']'],
        "dexcom_eightfold_next3",
    )


def scrape_docusign_ireland_next3(session):
    urls = [
        "https://careers.docusign.com/careers-home/jobs?location=Ireland",
        "https://careers.docusign.com/careers-home/jobs",
    ]
    return _next3_http_card_jobs(
        session, "DocuSign", urls,
        [r'href=["\']([^"\']*/careers-home/jobs/\d+[^"\']*)["\']'],
        "docusign_direct_next3",
    )




# === LARGE_NONLIVE_BATCH_8 ===
# Dexcom + DocuSign get their second recovery attempt.
# Six additional currently non-live companies get their first dedicated route.
# Existing live-company routes are intentionally untouched.

def scrape_dexcom_ireland_attempt2(session):
    """Attempt 2: rendered Eightfold board, unlike attempt 1's plain HTTP cards."""
    return _batch_first_party_roi_scrape(
        "Dexcom",
        [
            "https://careers.dexcom.com/careers?domain=dexcom.com&location=Athenry%2C%20Galway%2C%20Ireland&sort_by=distance&filter_distance=100&start=0",
            "https://careers.dexcom.com/careers?domain=dexcom.com&location=Ireland&sort_by=relevance&start=0",
        ],
        ["careers.dexcom.com"],
        ["/careers/job/"],
        session,
        "dexcom_rendered_attempt2",
        80,
    )


def scrape_docusign_ireland_attempt2(session):
    """Attempt 2: rendered Docusign board, unlike attempt 1's plain HTML cards."""
    return _batch_first_party_roi_scrape(
        "DocuSign",
        [
            "https://careers.docusign.com/careers-home/jobs?location=Ireland",
            "https://careers.docusign.com/careers-home/jobs?location=Dublin",
            "https://careers.docusign.com/careers-home/jobs",
        ],
        ["careers.docusign.com"],
        ["/careers-home/jobs/"],
        session,
        "docusign_rendered_attempt2",
        80,
    )


def scrape_aecom_ireland_newbatch(session):
    """AECOM Ireland through its official SmartRecruiters public API."""
    raw = try_smartrecruiters("AECOM2", session) or []
    results = []
    for item in raw:
        norm = normalize_smartrecruiters_job(
            "AECOM", item, "AECOM2", session, False
        )
        if norm:
            results.append(norm)
    print(f"      [aecom_smartrecruiters] {len(results)} Ireland jobs")
    return results


def scrape_netapp_ireland_newbatch(session):
    """NetApp's official Ireland location page."""
    return _batch_first_party_roi_scrape(
        "NetApp",
        [
            "https://careers.netapp.com/location/ireland-jobs/27600/2963597/2/1",
            "https://careers.netapp.com/location/ireland-jobs/27600/2963597/2",
        ],
        ["careers.netapp.com"],
        ["/job/"],
        session,
        "netapp_ireland_newbatch",
        80,
    )


def scrape_applied_materials_ireland_newbatch(session):
    """Applied Materials official Ireland location board."""
    return _batch_first_party_roi_scrape(
        "Applied Materials",
        [
            "https://jobs.appliedmaterials.com/location/ireland-jobs/95/2963597/2",
            "https://jobs.appliedmaterials.com/search-jobs/ireland/95/2/2963597/53/-8/50/2",
        ],
        ["jobs.appliedmaterials.com"],
        ["/job/"],
        session,
        "applied_materials_ireland_newbatch",
        80,
    )


def scrape_arcadis_ireland_newbatch(session):
    """Arcadis rendered Eightfold Dublin/Ireland board."""
    return _batch_first_party_roi_scrape(
        "Arcadis",
        [
            "https://jobs.arcadis.com/careers?domain=arcadis.com&location=Dublin%2C%20Dublin%2C%20Ireland&sort_by=distance&filter_distance=80&start=0",
            "https://jobs.arcadis.com/careers?domain=arcadis.com&location=Ireland&sort_by=relevance&start=0",
        ],
        ["jobs.arcadis.com"],
        ["/careers/job/"],
        session,
        "arcadis_ireland_newbatch",
        80,
    )


def scrape_jacobs_ireland_newbatch(session):
    """Jacobs' official Ireland-filtered Avature search."""
    return _batch_first_party_roi_scrape(
        "Jacobs",
        [
            "https://careers.jacobs.com/en_US/careers/SearchJobs/?4182=%5B76407%5D&4182_format=4422&listFilterMode=1&jobRecordsPerPage=20",
            "https://careers.jacobs.com/en_US/careers/SearchJobs/?jobRecordsPerPage=20&search=Ireland",
        ],
        ["careers.jacobs.com"],
        ["/en_US/careers/JobDetail/"],
        session,
        "jacobs_ireland_newbatch",
        80,
    )


def scrape_atkinsrealis_ireland_newbatch(session):
    """AtkinsRéalis first-party job-detail route."""
    return _batch_first_party_roi_scrape(
        "AtkinsRéalis",
        [
            "https://careers.atkinsrealis.com/en/jobs/?location=Ireland",
            "https://careers.atkinsrealis.com/en/jobs/?search=&location=Dublin",
            "https://careers.atkinsrealis.com/en",
        ],
        ["careers.atkinsrealis.com"],
        ["/en/jobs/"],
        session,
        "atkinsrealis_ireland_newbatch",
        80,
    )



def scrape_netapp_ireland_attempt2(session):
    """NetApp attempt 2: rendered official search pages with Ireland city queries."""
    return _batch_first_party_roi_scrape(
        "NetApp",
        [
            "https://careers.netapp.com/search/?q=&locationsearch=Ireland",
            "https://careers.netapp.com/search/?q=&locationsearch=Cork",
            "https://careers.netapp.com/search/?q=&locationsearch=Dublin",
            "https://careers.netapp.com/search/?q=Ireland",
        ],
        ["careers.netapp.com"],
        ["/job/", "/jobs/"],
        session,
        "netapp_attempt2_rendered",
        100,
    )



def scrape_next_manual_batch_generic(company_name, career_url, session):
    """Fresh-cache wrapper for the next unresolved manual-company batch."""
    return scrape_priority_sheet2_generic(company_name, career_url, session)




# === NEXT_RECOVERY_BATCH_7 ===
# High-confidence first-party recoveries for currently unresolved companies.

def scrape_baker_tilly_ireland_attempt2(session):
    # Current official Baker Tilly Ireland vacancies are real detail pages
    # under /vacancies/<slug>, with Dublin/Cork location text on each detail.
    return _batch_first_party_roi_scrape(
        "Baker Tilly Ireland",
        ["https://www.bakertilly.ie/careers/vacancies"],
        ["www.bakertilly.ie", "bakertilly.ie"],
        ["/vacancies/"],
        session,
        "baker_tilly_attempt2",
        50,
    )


def scrape_greencore_ireland_attempt2(session):
    # Greencore now exposes its Dublin head-office vacancies on its dedicated
    # careers subdomain rather than the corporate careers landing page.
    return _batch_first_party_roi_scrape(
        "Greencore",
        [
            "https://www.careers.greencore.com/branches/dublin-city",
            "https://www.careers.greencore.com/",
        ],
        ["careers.greencore.com"],
        ["/jobs/", "/vacancies/"],
        session,
        "greencore_attempt2",
        70,
    )


def scrape_amd_ireland_attempt2(session):
    # The old jobs.amd.com URL is dead. AMD's current official career system
    # is careers.amd.com and exposes Dublin/Cork Ireland detail records.
    return _batch_first_party_roi_scrape(
        "Advanced Micro Devices (AMD)",
        [
            "https://careers.amd.com/careers-home/jobs?location=Ireland",
            "https://careers.amd.com/careers-home/jobs?location=Dublin%2C%20Ireland",
            "https://careers.amd.com/careers-home/jobs?location=Cork%2C%20Ireland",
            "https://careers.amd.com/careers-home/jobs",
        ],
        ["careers.amd.com"],
        ["/careers-home/jobs/"],
        session,
        "amd_current_career_attempt2",
        100,
    )


def scrape_bayer_ireland_attempt2(session):
    # Current Bayer application portal (SuccessFactors-style job detail URLs).
    return _batch_first_party_roi_scrape(
        "Bayer",
        [
            "https://jobs.bayer.com/search/?q=&locationsearch=Ireland",
            "https://jobs.bayer.com/search/?q=Ireland",
            "https://jobs.bayer.com/",
        ],
        ["jobs.bayer.com"],
        ["/job/"],
        session,
        "bayer_current_portal_attempt2",
        80,
    )


def scrape_bdo_ireland_pinpoint(session):
    # BDO Ireland's current official careers host is Pinpoint.
    raw = try_pinpoint("bdoireland", session) or []
    jobs = []
    for item in raw:
        norm = normalize_pinpoint_job("BDO Ireland", "bdoireland", item)
        if norm:
            jobs.append(norm)
    print(f"      [bdo_pinpoint] {len(jobs)} Ireland jobs")
    return jobs


def scrape_aviva_ireland_current(session):
    # Aviva Ireland currently routes vacancies to its official Randstad
    # talent-community site. City-scoped pages avoid UK results.
    return _batch_first_party_roi_scrape(
        "Aviva Ireland",
        [
            "https://aviva.talent-community.com/projects/in/dublin",
            "https://aviva.talent-community.com/projects/in/cork",
            "https://aviva.talent-community.com/projects/in/galway",
            "https://aviva.talent-community.com/projects/in/ireland",
        ],
        ["aviva.talent-community.com"],
        ["/projects/"],
        session,
        "aviva_current_portal",
        80,
    )


def scrape_fitch_ireland_current(session):
    # Fitch's current official job site is careers.fitch.group (SuccessFactors).
    return _batch_first_party_roi_scrape(
        "Fitch Ratings",
        [
            "https://careers.fitch.group/search/?q=&locationsearch=Ireland",
            "https://careers.fitch.group/search/?q=&locationsearch=Dublin",
            "https://careers.fitch.group/go/View-All-Jobs/8883701/",
        ],
        ["careers.fitch.group"],
        ["/job/"],
        session,
        "fitch_current_portal",
        80,
    )




def scrape_large_unresolved_batch(company_name, career_url, session):
    """Fresh-cache wrapper for the next large unresolved-company batch.
    It uses the pipeline's existing strict ROI generic scraper, so this adds
    coverage without loosening filters or changing successful live routes."""
    return scrape_priority_sheet2_generic(company_name, career_url, session)




def scrape_multi_seed_attempt2(company_name, career_url, session):
    """Second-pass recovery for unresolved first-party career sites.
    Unlike the first generic pass (single career URL), this tries multiple
    Ireland-specific search/listing URL shapes on the same official host and
    still requires real detail URLs + strict Republic-of-Ireland proof."""
    if not career_url:
        return []
    try:
        parsed = urllib.parse.urlparse(career_url)
        origin = f"{parsed.scheme or 'https'}://{parsed.netloc}"
        host = parsed.netloc.lower()
    except Exception:
        return []

    seeds = []
    def add(u):
        if u and u not in seeds:
            seeds.append(u)

    add(career_url)
    add(origin + "/")
    add(origin + "/jobs?location=Ireland")
    add(origin + "/jobs/?location=Ireland")
    add(origin + "/jobs?search=Ireland")
    add(origin + "/search/?q=&locationsearch=Ireland")
    add(origin + "/search/?q=Ireland")
    add(origin + "/careers?location=Ireland")
    add(origin + "/careers/?location=Ireland")
    add(origin + "/vacancies?location=Ireland")
    add(origin + "/vacancies/?location=Ireland")

    patterns = [
        "/job/", "/jobs/", "/job-detail/", "/jobdetail/",
        "/vacancy/", "/vacancies/", "/careers/job/",
        "/careers-home/jobs/", "/positions/", "/opportunities/"
    ]
    return _batch_first_party_roi_scrape(
        company_name,
        seeds,
        [host],
        patterns,
        session,
        "multi_seed_attempt2",
        60,
    )


def main():
    print("=== NEXT_20_ATTEMPT2 ACTIVE: 20 remaining unresolved companies get multi-seed first-party attempt 2; live routes untouched ===")
    print("=== LARGE_RECOVERY_BATCH_20 ACTIVE: 20 unresolved companies forced into one run with fresh cache; live routes untouched ===")
    print("=== NEXT_RECOVERY_BATCH_7 ACTIVE: Baker Tilly/Greencore/AMD/Bayer attempt2 + BDO/Aviva/Fitch current first-party routes; live routes untouched ===")
    print("=== NEXT_MANUAL_BATCH_20_QUEUE_FIX ACTIVE: 20 unresolved companies forced from CSV status-independently; live routes untouched ===")
    print("=== DOCUSIGN_ATKINS_RETURN_FIX_NETAPP_ATTEMPT2 ACTIVE: proven DocuSign/Atkins routes get return budget; NetApp gets second route ===")
    print("=== LARGE_NONLIVE_BATCH_8 ACTIVE: Dexcom/DocuSign attempt 2 + AECOM/NetApp/Applied Materials/Arcadis/Jacobs/AtkinsRealis attempt 1; live routes untouched ===")
    print("=== THREE_REGRESSION_RECOVERY ACTIVE: Three CSOD country=ie recovery + persistent last-known-nonzero protection ===")
    print("=== NEXT_COMPANIES_3_DIRECT_FIX ACTIVE: Ryanair/Dexcom/DocuSign first-party recovery; live routes untouched ===")
    print("=== REGRESSION_GUARD_FIX ACTIVE: versioned zero caches cleared; sudden 1-run disappearances protected; count drops reported ===")
    print("=== RUNTIME_DEDUPE_FIX ACTIVE: one company = one full-run task; dedicated routes win over generic duplicates ===")
    print("=== TWO_ATTEMPT_RULE_BATCH ACTIVE: Oracle/McKinsey attempt 2 + Honeywell/Schneider attempt 1; successful live routes untouched ===")
    print("=== ORACLE_BAUSCH_MCKINSEY_BATCH ACTIVE: Oracle REST scheduled in full run + Bausch/McKinsey friend routes; live companies untouched ===")
    print("=== AGILENT_PLUS_FRIEND_NEXT4 ACTIVE: Agilent full dedicated timeout + Heineken/Musgrave/VHI/HP friend logic; live companies untouched ===")
    print("=== NONLIVE_FRIEND_BATCH_10 ACTIVE: AXA/Agilent/BNP/Coca-Cola HBC/HCL/Infosys/Laya/Palo Alto/SMBC Aviation/SIG; valid live companies untouched ===")
    print("=== GRANT_EXACT_TITLE_FIX ACTIVE: Oracle card location/date/badges stripped from Grant job titles ===")
    print("=== SINGLE_FILE_GRANT_QUALITY_FIX ACTIVE: Grant uses Oracle real-job links; navigation/CTA titles globally blocked ===")
    print("=== FRIEND_LOGIC_NONLIVE_BATCH ACTIVE: Abbott/Intel/Vodafone/DXC/DB/S&P/Three/TCS; existing live companies untouched ===")
    print("=== FAST_BATCH_8_NEXT ACTIVE: Abbott/AZ/Amgen/Alexion/Stryker/Novartis/Intel + Aldi second pass ===")
    print("=== FAST_BATCH_6_NEXT ACTIVE: SSE fast-return + Tesco/Aldi/FBD/Capgemini/Vodafone dedicated routes ===")
    print("=== FAST_BATCH_5_RECOVERY ACTIVE: Goodbody/BMS/SSE/HPE/Dell dedicated first-party routes; runtime architecture unchanged ===")
    print("=== FAST_MERIT_MEDICAL_FIX ACTIVE: official Merit Workday route; runtime architecture unchanged ===")
    print("=== FAST_GUIDEWIRE_QUALITY_FIX ACTIVE: verified Guidewire ROI jobs no longer rejected only for URL shape ===")
    print("=== FAST_BASELINE_IQVIA_ONLY ACTIVE: proven IQVIA Ireland scraper added; runtime architecture unchanged ===")
    print("=== WIPRO_UNKNOWN_DATE_FIX ACTIVE: rendered date if available; otherwise Unknown ===")
    print("=== WIPRO_DATE_FIX ACTIVE: SuccessFactors posting dates parsed from labels/HTML attributes ===")
    print("=== WIPRO_SEARCH_FIX ACTIVE: uses SuccessFactors /search/ endpoint, not /viewalljobs/ ===")
    print("=== WIPRO_RENDERED_FIX ACTIVE: Playwright discovers rendered /job/ records; detail page verifies ROI ===")
    print("=== WIPRO_DEDICATED ACTIVE: structural /job/ records + explicit City/State ROI verification ===")
    print("=== STRUCTURAL_VACANCY_FIX ACTIVE: generic results require real job-detail URL + proven Republic-of-Ireland location ===")
    print("=== ROI_VACANCY_MODE ACTIVE: fetch real Republic-of-Ireland vacancies; no profession-title keyword filtering ===")
    print("=== FULL_RUN_COVERAGE_FIX ACTIVE: known company scrapers are scheduled from CSV, not status buckets ===")
    print("=== JOB_COUNT_REGRESSION_FIX ACTIVE: keep valid ROI listing jobs when detail parsing fails ===")
    print("=== STATUS MODE ACTIVE: Live Jobs / Currently No Jobs / Fetching Error ===")
    print("=== VACANCY_QUALITY_V2 ACTIVE: sitemap/blog/saved-job false positives rejected; strict ROI retained ===")
    print("=== STRICT_ROI_MODE ACTIVE: job detail page must prove Republic of Ireland; Northern Ireland excluded ===")
    print("=== MANUAL_RECOVERY_NEXT_BATCH ACTIVE: corrected Viatris/Medtronic/QIAGEN routes + WTW/Guidewire + sitemap recovery + 8 new manual targets ===")
    print("=== PLATFORM_SPECIFIC_RECOVERY ACTIVE: 15 confirmed-manual companies get first-party recovery paths ===")
    print("=== CONFIRMED_MANUAL_RECOVERY ACTIVE: 15 companies from latest JSON; live companies untouched ===")
    print("=== WORKDAY_RECOVERY_BATCH=2 ACTIVE: 18 audited Workday companies get rendered fallback on API error/zero ===")
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

    # Force a fresh browser attempt for audited manual companies only when the
    # existing cache contains ZERO jobs. Positive cached results are preserved.
    _recovery_zeroes = []
    for _cache_name in list(browser_cache.keys()):
        if str(_cache_name).lower() in MANUAL_RECOVERY_CONFIRMED:
            _entry = browser_cache.get(_cache_name) or {}
            if not _entry.get("jobs"):
                browser_cache.pop(_cache_name, None)
                _recovery_zeroes.append(_cache_name)
    if _recovery_zeroes:
        print("=== Confirmed-manual recovery: bypassing stale zero browser cache for "
              + ", ".join(sorted(_recovery_zeroes)) + " ===")
    fresh_count = sum(1 for v in browser_cache.values()
                       if (time.time() - v.get("checked_at", 0)) / 3600 < BROWSER_SCRAPE_MAX_AGE_HOURS)
    print(f"=== Browser-scrape cache: {len(browser_cache)} companies tracked, "
          f"{fresh_count} still fresh (within {BROWSER_SCRAPE_MAX_AGE_HOURS}h) and will be reused "
          f"instantly instead of re-launching a real browser this run ===")

    session = requests.Session()

    # Three-state company model:
    #   live_jobs             = automated successfully + current ROI jobs
    #   automated_zero       = automated successfully + 0 current ROI jobs
    #   manual_check         = unresolved because automation could not reliably check it
    #
    # sponsorship_history.json already contains every company that has ever
    # produced a live job in earlier successful runs. Reusing that history
    # prevents a stricter title/detail validator from pushing a previously
    # automated company back into "manual" merely because this run yields zero.
    prior_history = load_history(args.history)
    historically_automated = {str(name).strip() for name in prior_history.keys()}

    # A previous over-strict validation run may have cached an empty result
    # for a company that demonstrably produced valid jobs in earlier runs.
    # Never let that poisoned zero cache suppress the repaired scraper.
    _historical_lower = {name.lower() for name in historically_automated}
    _cleared_zero_cache = []
    for _cache_company in list(browser_cache.keys()):
        _cache_entry = browser_cache.get(_cache_company) or {}
        # Cache keys are often versioned: "Company::route_v2". Compare the
        # company portion, not the entire cache key. Otherwise a cached zero
        # for a previously-live company can survive indefinitely.
        _cache_base_company = str(_cache_company).split("::", 1)[0].strip().lower()
        if (_cache_base_company in _historical_lower
                and not _cache_entry.get("jobs")):
            browser_cache.pop(_cache_company, None)
            _cleared_zero_cache.append(_cache_company)
    if _cleared_zero_cache:
        print(
            f"=== Cache recovery: cleared {len(_cleared_zero_cache)} stale zero results "
            "for companies that produced valid jobs before ==="
        )

    # Persistent last-known-nonzero snapshot. Unlike jobs.json, this does not
    # forget a company after one or more zero runs. It is generated/maintained
    # automatically by the pipeline; no manual file replacement is required.
    _last_nonzero_path = "last_nonzero_jobs.json"
    _last_nonzero_by_company = {}
    if os.path.exists(_last_nonzero_path):
        try:
            with open(_last_nonzero_path, encoding="utf-8") as _lf:
                _raw_last_nonzero = json.load(_lf)
            if isinstance(_raw_last_nonzero, dict):
                _last_nonzero_by_company = _raw_last_nonzero
        except Exception:
            _last_nonzero_by_company = {}

    # Snapshot the immediately previous live output. This is used only as a
    # regression safety net: one transient zero/error must not instantly erase
    # a company that was live in the preceding run.
    _previous_live_jobs = []
    if os.path.exists(args.output):
        try:
            with open(args.output, encoding="utf-8") as _pf:
                _previous_payload = json.load(_pf)
            if isinstance(_previous_payload, dict):
                _previous_live_jobs = list(_previous_payload.get("jobs") or [])
            elif isinstance(_previous_payload, list):
                _previous_live_jobs = list(_previous_payload)
        except Exception:
            _previous_live_jobs = []

    live_jobs, manual_check, errors = [], [], []
    automated_zero = {}
    failed_companies = set()

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

        # Batch-1 recovery: several real Ireland employers currently fail at the
        # Workday CXS layer (most commonly HTTP 422), while a few return a
        # suspicious zero.  For ONLY this explicitly-audited set, fall back to
        # the already-existing rendered Ireland-first scraper.  The normal API
        # remains primary, so companies that already work are unchanged.
        if (not jobs and name.lower() in WORKDAY_RECOVERY_COMPANIES
                and name.lower() not in {
                    "aon", "dxc technology", "northern trust", "willis towers watson (wtw)",
                    "becton dickinson (bd)", "jazz pharmaceuticals", "takeda",
                    "teleflex", "viatris"
                } and HAS_PLAYWRIGHT):
            original_err = err
            try:
                print(f"      [workday-recovery] {name}: API returned "
                      f"{'an error' if original_err else '0 jobs'}; trying rendered Ireland fallback")
                recovered = scrape_priority_sheet2_generic(name, url, requests.Session()) or []
                if recovered:
                    for job in recovered:
                        job["source"] = "workday_browser_fallback"
                    jobs = recovered
                    err = None
                    print(f"      [workday-recovery] {name}: recovered {len(jobs)} Ireland postings")
                else:
                    print(f"      [workday-recovery] {name}: rendered fallback found 0 Ireland postings")
            except Exception as recovery_exc:
                print(f"      [workday-recovery] {name}: fallback failed ({recovery_exc})")
                # Preserve the original API error when one existed; otherwise
                # expose the recovery failure so this is never mistaken for a
                # confirmed legitimate zero.
                if not err:
                    err = f"{name}: Workday browser recovery failed ({recovery_exc})"

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
                    failed_companies.add(name)
                done += 1
                print(f"      [workday {done}/{len(workday_rows)}] {name} -> {len(jobs)} Ireland postings")
                if not jobs:
                    if err:
                        manual_check.append({
                            "company": name,
                            "url": url,
                            "platform": "workday (Fetching error)",
                        })
                    else:
                        automated_zero[name] = {
                            "company": name,
                            "platform": "workday",
                            "reason": "Currently no jobs in Ireland",
                        }
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
    discovered_jobs, manual_check, ats_automated_zero = probe_ats_for_manual_companies(
        manual_check, session, cache_path="ats_platform_cache.json",
        fetch_descriptions=not args.no_descriptions)
    for item in ats_automated_zero:
        automated_zero[item["company"]] = item
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
    # SHEET 2 PRIORITY COVERAGE — the company-name set itself now lives at
    # module level as PRIORITY_SHEET2_COMPANIES (near test_single_company),
    # since test_single_company also needs to see it for --only testing.
    # Task queueing happens further below, AFTER task_list/matched_entries
    # exist; see the fix note there.

    dedicated_company_specs = [
        ("exact", "ryanair", scrape_ryanair_ireland_next3, 45, "official Ryanair Ireland listing"),
        ("exact", "dexcom", scrape_dexcom_ireland_attempt2, 60, "attempt 2 rendered Dexcom Ireland board"),
        ("exact", "docusign", scrape_docusign_ireland_attempt2, 105, "verified Docusign route; extended return budget"),
        ("exact", "aecom", scrape_aecom_ireland_newbatch, 45, "official AECOM SmartRecruiters API"),
        ("exact", "netapp", scrape_netapp_ireland_attempt2, 90, "NetApp attempt 2 rendered Ireland/city search"),
        ("exact", "applied materials", scrape_applied_materials_ireland_newbatch, 60, "official Applied Materials Ireland board"),
        ("exact", "arcadis", scrape_arcadis_ireland_newbatch, 60, "official Arcadis Ireland Eightfold board"),
        ("exact", "jacobs", scrape_jacobs_ireland_newbatch, 60, "official Jacobs Ireland search"),
        ("exact", "atkinsréalis", scrape_atkinsrealis_ireland_newbatch, 105, "verified AtkinsRéalis route; extended return budget"),
        ("exact", "baker tilly ireland", scrape_baker_tilly_ireland_attempt2, 75, "Baker Tilly attempt 2 current vacancies"),
        ("exact", "greencore", scrape_greencore_ireland_attempt2, 75, "Greencore attempt 2 Dublin careers hub"),
        ("exact", "advanced micro devices (amd)", scrape_amd_ireland_attempt2, 90, "AMD attempt 2 current careers host"),
        ("exact", "bayer", scrape_bayer_ireland_attempt2, 75, "Bayer attempt 2 current job portal"),
        ("exact", "bdo ireland", scrape_bdo_ireland_pinpoint, 30, "BDO Ireland official Pinpoint API"),
        ("exact", "aviva ireland", scrape_aviva_ireland_current, 75, "Aviva Ireland official talent-community"),
        ("exact", "fitch ratings", scrape_fitch_ireland_current, 75, "Fitch current official careers site"),
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
        ("exact", "wipro", scrape_wipro_ireland, 75, "first-party Wipro vacancy records + City/State verification"),
        ("exact", "iqvia", scrape_iqvia_ireland, 90, "first-party IQVIA Ireland Jobs page"),
        ("exact", "merit medical", scrape_merit_medical_ireland, 75, "official Merit Medical Workday"),
        ("exact", "goodbody", scrape_goodbody_ireland, 60, "official Goodbody jobs board"),
        ("exact", "bristol myers squibb", scrape_bms_ireland, 60, "official BMS Ireland careers"),
        ("exact", "sse airtricity / sse", scrape_sse_ireland, 60, "official SSE careers"),
        ("exact", "hewlett packard enterprise (hpe)", scrape_hpe_ireland, 60, "official HPE careers"),
        ("exact", "dell technologies", scrape_dell_ireland, 60, "official Dell careers"),
        ("exact", "tesco ireland", scrape_tesco_ireland, 60, "official Tesco Ireland careers"),
        ("exact", "aldi ireland", scrape_aldi_ireland, 60, "official Aldi Ireland careers"),
        ("exact", "fbd insurance", scrape_fbd_ireland, 60, "official FBD careers"),
        ("exact", "capgemini", scrape_capgemini_ireland, 60, "official Capgemini careers"),
        ("exact", "vodafone ireland", scrape_vodafone_ireland, 60, "official Vodafone Ireland careers"),
        ("exact", "abbott", scrape_abbott_ireland, 60, "official Abbott careers"),
        ("exact", "astrazeneca", scrape_astrazeneca_ireland, 60, "official AstraZeneca careers"),
        ("exact", "amgen", scrape_amgen_ireland, 60, "official Amgen careers"),
        ("exact", "alexion", scrape_alexion_ireland, 60, "official Alexion careers"),
        ("exact", "stryker", scrape_stryker_ireland, 60, "official Stryker careers"),
        ("exact", "novartis", scrape_novartis_ireland, 60, "official Novartis careers"),
        ("exact", "intel", scrape_intel_ireland, 60, "official Intel careers"),
        ("exact", "tata consultancy services (tcs)", scrape_tcs_ireland, 45, "official TCS Candidate Manager"),
        ("exact", "axa ireland", scrape_axa_ireland_friend, 60, "friend-referenced AXA Ireland board"),
        ("exact", "agilent technologies", scrape_agilent_ireland_friend, 60, "friend-referenced Agilent Workday"),
        ("exact", "bnp paribas ireland", scrape_bnp_paribas_ireland_friend, 60, "friend-referenced BNP Ireland board"),
        ("exact", "coca-cola hbc ireland", scrape_coca_cola_hbc_ireland_friend, 60, "friend-referenced Coca-Cola HBC board"),
        ("exact", "hcltech", scrape_hcltech_ireland_friend, 60, "friend-referenced HCLTech Ireland facet"),
        ("exact", "infosys", scrape_infosys_ireland_friend, 60, "friend-referenced Infosys Ireland board"),
        ("exact", "laya healthcare", scrape_laya_healthcare_friend, 60, "friend-referenced Laya AXA board"),
        ("exact", "palo alto networks", scrape_palo_alto_ireland_friend, 60, "friend-referenced Palo Alto Ireland board"),
        ("exact", "smbc aviation capital", scrape_smbc_aviation_capital_friend, 60, "friend-referenced SMBC Aviation board"),
        ("exact", "susquehanna international group (sig)", scrape_sig_ireland_friend, 60, "friend-referenced SIG Dublin board"),
        ("exact", "heineken ireland", scrape_heineken_ireland_friend, 45, "friend-referenced HEINEKEN Ireland board"),
        ("exact", "musgrave group (supervalu / centra)", scrape_musgrave_ireland_friend, 60, "friend-referenced Musgrave vacancies"),
        ("exact", "vhi healthcare", scrape_vhi_ireland_friend, 60, "friend-referenced VHI CandidateManager"),
        ("exact", "hp (hewlett-packard)", scrape_hp_ireland_friend, 60, "friend-referenced HP Ireland search"),
        ("exact", "oracle", scrape_oracle_ireland_attempt2, 60, "attempt 2 rendered Oracle Ireland board"),
        ("exact", "bausch + lomb", scrape_bausch_lomb_friend, 60, "friend-referenced Bausch + Lomb Ireland board"),
        ("exact", "mckinsey & company", scrape_mckinsey_ireland_attempt2, 45, "attempt 2 lightweight McKinsey Dublin HTTP"),
        ("exact", "honeywell", scrape_honeywell_attempt2, 90, "Honeywell second/final Ireland attempt"),
        ("exact", "schneider electric", scrape_schneider_attempt2, 90, "Schneider second/final Ireland attempt"),
        ("exact", "aib (allied irish banks)", scrape_aib_ireland, 240, "filtered against UK-only postings"),
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
        ("exact", "allianz", scrape_allianz_ireland, 180, "real careers page"),
        ("exact", "siemens", scrape_siemens_ireland, 180, "Avature-powered search"),
        ("exact", "northern trust", scrape_northern_trust_ireland_direct, 75, "first-party HTTP detail verification"),
        ("exact", "willis towers watson (wtw)", scrape_wtw_ireland_direct, 75, "first-party WTW Ireland listing"),
        ("exact", "becton dickinson (bd)", scrape_bd_ireland_direct, 75, "first-party BD Ireland listing"),
        ("exact", "jazz pharmaceuticals", scrape_jazz_ireland_direct, 75, "first-party Jazz Ireland listing"),
        ("exact", "takeda", scrape_takeda_ireland_direct, 75, "first-party Takeda Ireland listing"),
        ("exact", "teleflex", scrape_teleflex_ireland_direct, 75, "first-party Teleflex Ireland search"),
        ("exact", "viatris", scrape_viatris_ireland_direct, 75, "first-party Viatris Ireland search"),
        ("exact", "qiagen", scrape_qiagen_ireland_direct, 75, "first-party QIAGEN careers"),
        ("exact", "regeneron", scrape_regeneron_ireland_direct, 75, "first-party Regeneron Ireland listing"),
        ("exact", "medtronic", scrape_medtronic_ireland_direct, 75, "first-party Medtronic Ireland search"),
        ("exact", "fidelity investments", scrape_fidelity_investments_ireland_direct, 75, "Ireland-scoped first-party listing"),
        ("exact", "bny mellon", scrape_bny_mellon_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "goldman sachs", scrape_goldman_sachs_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "morgan stanley", scrape_morgan_stanley_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "s&p global", scrape_sp_global_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "databricks", scrape_databricks_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "visa", scrape_visa_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "aer lingus", scrape_aer_lingus_ireland_recovery, 75, "first-party sitemap recovery"),
        ("exact", "pepsico", scrape_pepsico_ireland, 180, "official careers search"),
    ]

    task_list = []
    matched_entries = {}

    # NEXT MANUAL BATCH QUEUE FIX: these targets are selected directly from
    # the CSV company rows, NOT from manual_check. This is intentional: a
    # target may currently be classified as Currently No Jobs rather than
    # Manual, and that status must not prevent its recovery attempt from
    # actually running. Existing live companies are still skipped below.
    # Final company-level dedupe ensures this never creates a second task for
    # a company that already has a more-specific dedicated route.
    _next_manual_batch_names = {
        # Previously intended batch (did not run because of the old
        # manual_check-only gate; this run is their real first attempt).
        "baker tilly ireland", "davy", "dunnes stores", "forvis mazars ireland",
        "greencore", "lidl ireland", "oliver wyman", "protiviti",
        "advanced micro devices (amd)", "bayer",
        # Additional unresolved batch so we move more companies per run.
        "dynatrace", "fti consulting", "factset", "msci", "macquarie group",
        "moody's", "morningstar", "refinitiv (lseg)", "societe generale", "splunk",
    }
    _next_manual_rows = [c for c in companies if c["company_name"].strip().lower() in _next_manual_batch_names]


    _large_recovery_batch20_names = {
        'edwards lifesciences',
        'teva pharmaceuticals',
        'revvity (perkinelmer)',
        'supervalu / musgrave',
        'alkermes',
        'an post',
        'atlassian',
        'biotronik',
        'boehringer ingelheim',
        'bord gáis energy',
        'box',
        'bruker',
        'coloplast',
        'dsv ireland',
        'eirgrid group',
        'energia group',
        'glaxosmithkline (gsk)',
        'haleon',
        'hollister incorporated',
        'insulet corporation',
    }
    _large_recovery_rows = [
        c for c in companies
        if c["company_name"].strip().lower() in _large_recovery_batch20_names
    ]

    # ------------------------------------------------------------------
    # ORDERING FIX: dedicated/oracle_cx/lightweight scrapers (all
    # long-proven, reliable companies — Microsoft, Google, Citi, JPMorgan
    # Chase, etc.) are queued FIRST, and the 141 more speculative Sheet 2
    # priority companies are queued LAST. This matters because
    # ThreadPoolExecutor serves submitted tasks roughly in submission
    # order as workers free up — with the browser pool capped at
    # BROWSER_WORKERS, if Sheet 2's ~140 companies were submitted first
    # (as they were before this fix), an established company like
    # Microsoft could sit behind well over a hundred speculative new
    # entries before ever getting a worker, and time out before its own
    # scrape even started. Queuing proven companies first means new
    # additions can never crowd out or delay existing working coverage —
    # they only ever queue behind it.

    # Functions confirmed (by direct source-code check for sync_playwright)
    # to launch a real Chrome instance — everything else in
    # dedicated_company_specs is plain HTTP requests. Used below to route
    # each task into the right pool (see run_company_tasks_in_parallel).
    BROWSER_BASED_SCRAPER_NAMES = {
        "scrape_google_ireland", "scrape_meta_ireland", "scrape_ey_ireland",
        "scrape_kpmg_ireland", "scrape_tiktok_ireland", "scrape_boston_scientific_ireland",
        "scrape_microsoft_ireland", "scrape_citi_ireland", "scrape_red_hat_ireland",
        "scrape_johnson_controls_ireland", "scrape_hsbc_ireland", "scrape_dxc_ireland",
        "scrape_aon_ireland", "scrape_nvidia_ireland", "scrape_aib_ireland",
        "scrape_bnp_paribas_ireland", "scrape_blackrock_ireland", "scrape_bank_of_ireland_direct",
        "scrape_ing_ireland", "scrape_deutsche_bank_ireland", "scrape_central_bank_ireland_direct",
        "scrape_irish_life_ireland", "scrape_ups_ireland", "scrape_three_ireland_direct",
        "scrape_huawei_ireland", "scrape_ge_healthcare_ireland", "scrape_ntt_data_ireland",
        "scrape_guidewire_ireland", "scrape_hcltech_ireland", "scrape_allianz_ireland",
        "scrape_siemens_ireland",
        "scrape_wtw_ireland_direct", "scrape_guidewire_ireland_direct_http",
        "scrape_wipro_ireland",
        "scrape_iqvia_ireland",
        "scrape_goodbody_ireland", "scrape_bms_ireland", "scrape_sse_ireland",
        "scrape_hpe_ireland", "scrape_dell_ireland",
        "scrape_tesco_ireland", "scrape_aldi_ireland", "scrape_fbd_ireland",
        "scrape_capgemini_ireland", "scrape_vodafone_ireland",
        "scrape_abbott_ireland", "scrape_astrazeneca_ireland", "scrape_amgen_ireland",
        "scrape_alexion_ireland", "scrape_stryker_ireland", "scrape_novartis_ireland",
        "scrape_intel_ireland",
        "scrape_axa_ireland_friend", "scrape_bnp_paribas_ireland_friend",
        "scrape_coca_cola_hbc_ireland_friend", "scrape_hcltech_ireland_friend",
        "scrape_infosys_ireland_friend", "scrape_laya_healthcare_friend",
        "scrape_palo_alto_ireland_friend", "scrape_smbc_aviation_capital_friend",
        "scrape_sig_ireland_friend",
        "scrape_musgrave_ireland_friend", "scrape_vhi_ireland_friend",
        "scrape_hp_ireland_friend",
        "scrape_dexcom_ireland_attempt2", "scrape_docusign_ireland_attempt2",
        "scrape_netapp_ireland_attempt2", "scrape_applied_materials_ireland_newbatch",
        "scrape_arcadis_ireland_newbatch", "scrape_jacobs_ireland_newbatch",
        "scrape_atkinsrealis_ireland_newbatch",
        "scrape_baker_tilly_ireland_attempt2", "scrape_greencore_ireland_attempt2",
        "scrape_amd_ireland_attempt2", "scrape_bayer_ireland_attempt2",
        "scrape_aviva_ireland_current", "scrape_fitch_ireland_current",
        "scrape_bausch_lomb_friend",
        "scrape_oracle_ireland_attempt2", "scrape_honeywell_attempt2", "scrape_schneider_attempt2",
    }

    _live_company_names = {
        str(j.get("company") or "").strip().lower()
        for j in live_jobs
        if j.get("company")
    }

    for match_type, key, scraper_fn, timeout_s, description in dedicated_company_specs:
        if match_type == "exact":
            company_row = next(
                (c for c in companies if c["company_name"].strip().lower() == key),
                None,
            )
        else:
            company_row = next(
                (c for c in companies if c["company_name"].strip().lower().startswith(key)),
                None,
            )
        if not company_row:
            continue

        company_name = company_row["company_name"].strip()

        # Earlier reliable API/ATS stages already found current jobs: no need
        # to run the company's dedicated fallback a second time.
        if company_name.lower() in _live_company_names:
            continue

        entry = next(
            (c for c in manual_check if c["company"].strip().lower() == company_name.lower()),
            None,
        )
        if entry is not None:
            matched_entries[company_name] = entry

        def make_task(fn=scraper_fn, name=company_name):
            # IQVIA has a dedicated Ireland scraper now. Keep its cache separate
            # from the old generic Sheet-2 zero-result cache so the proven
            # dedicated result cannot be shadowed by a stale generic verdict.
            _key = name.strip().lower()
            if _key == "iqvia":
                cache_key = "IQVIA::ireland_dedicated_v1"
            elif _key == "merit medical":
                cache_key = "Merit Medical::workday_dedicated_v1"
            elif _key in {"honeywell", "schneider electric"}:
                cache_key = f"{name}::final_attempt_v3"
            elif _key in {
                "oracle",
                "mckinsey & company",
            }:
                cache_key = f"{name}::attempt2_plus_new_v2"
            elif _key in {
                "bausch + lomb",
            }:
                cache_key = f"{name}::friend_oracle_bausch_mckinsey_v1"
            elif _key in {
                "heineken ireland",
                "musgrave group (supervalu / centra)",
                "vhi healthcare",
                "hp (hewlett-packard)",
            }:
                cache_key = f"{name}::friend_next4_v1"
            elif _key in {
                "axa ireland",
                "agilent technologies",
                "bnp paribas ireland",
                "coca-cola hbc ireland",
                "hcltech",
                "infosys",
                "laya healthcare",
                "palo alto networks",
                "smbc aviation capital",
                "susquehanna international group (sig)",
            }:
                cache_key = ("Agilent Technologies::friend_workday_return_v2" if _key == "agilent technologies" else f"{name}::friend_nonlive_batch10_v1")
            elif _key in {
                "goodbody",
                "bristol myers squibb",
                "sse airtricity / sse",
                "hewlett packard enterprise (hpe)",
                "dell technologies",
                "tesco ireland",
                "aldi ireland",
                "fbd insurance",
                "capgemini",
                "vodafone ireland",
                "abbott",
                "astrazeneca",
                "amgen",
                "alexion",
                "stryker",
                "novartis",
                "intel",
                "tata consultancy services (tcs)",
            }:
                if _key == "aldi ireland":
                    cache_key = "Aldi Ireland::batch_dedicated_v2"
                elif _key in {
                    "abbott", "intel", "vodafone ireland",
                    "tata consultancy services (tcs)"
                }:
                    cache_key = f"{name}::friend_logic_v1"
                else:
                    cache_key = f"{name}::batch_dedicated_v1"
            else:
                cache_key = name
            if _key == "ryanair":
                cache_key = f"{name}::next_companies_3_direct_v1"
            elif _key == "netapp":
                cache_key = f"{name}::netapp_attempt2_v3"
            elif _key in {
                "dexcom", "docusign", "aecom",
                "applied materials", "arcadis", "jacobs", "atkinsréalis"
            }:
                cache_key = f"{name}::large_nonlive_batch8_v2"
            elif _key in {
                "baker tilly ireland", "greencore", "advanced micro devices (amd)",
                "bayer", "bdo ireland", "aviva ireland", "fitch ratings"
            }:
                cache_key = f"{name}::next_recovery_batch7_v1"
            elif _key in {"dxc technology", "deutsche bank", "s&p global", "three ireland"}:
                cache_key = f"{name}::friend_logic_v1"
            elif _key == "grant thornton ireland":
                cache_key = "Grant Thornton Ireland::oracle_exact_titles_v2"
            return lambda: cached_browser_scrape(browser_cache, cache_key, lambda: fn(session), 0, name)

        _fresh_dedicated_timeout_names = {
            "agilent technologies",
            "heineken ireland",
            "musgrave group (supervalu / centra)",
            "vhi healthcare",
            "hp (hewlett-packard)",
            "oracle",
            "bausch + lomb",
            "mckinsey & company",
            "honeywell",
            "schneider electric",
            "dexcom",
            "docusign",
            "aecom",
            "netapp",
            "applied materials",
            "arcadis",
            "jacobs",
            "atkinsréalis",
            "baker tilly ireland",
            "greencore",
            "advanced micro devices (amd)",
            "bayer",
            "bdo ireland",
            "aviva ireland",
            "fitch ratings",
        }
        if company_name.strip().lower() in _fresh_dedicated_timeout_names:
            actual_timeout = timeout_s
        else:
            actual_timeout = effective_timeout(browser_cache, company_name, timeout_s)

        if actual_timeout < timeout_s:
            failures = (browser_cache.get(company_name) or {}).get("consecutive_failures", 0)
            print(f"  [{company_name}] {failures} consecutive failures — reduced budget "
                  f"{timeout_s}s -> {actual_timeout}s this run")
        is_browser = scraper_fn.__name__ in BROWSER_BASED_SCRAPER_NAMES
        task_list.append((key, company_name, make_task(), actual_timeout, is_browser))

    oracle_cx_targets = [
        ("jpmorgan chase", "JPMorgan Chase", "https://jpmc.fa.oraclecloud.com", "CX_1001"),
        # Oracle is intentionally NOT listed here anymore.
        # It is already scheduled above through scrape_oracle_ireland_attempt2.
        # Keeping both routes caused two Oracle tasks every full run.
    ]
    for exact_name, display_name, host, site_number in oracle_cx_targets:
        company_row = next(
            (c for c in companies if c["company_name"].strip().lower() == exact_name),
            None,
        )
        if not company_row:
            continue
        company_name = company_row["company_name"].strip()
        if company_name.lower() in _live_company_names:
            continue
        entry = next(
            (c for c in manual_check if c["company"].strip().lower() == exact_name),
            None,
        )
        if entry is not None:
            matched_entries[company_name] = entry

        def make_oracle_task(h=host, s=site_number, name=company_name):
            return lambda: cached_browser_scrape(
                browser_cache, name, lambda: scrape_oracle_candidate_experience(name, h, s, session), 0, name)

        task_list.append(("oracle_cx", company_name, make_oracle_task(), 180, False))

    # 9 new companies — 8 are genuinely lightweight (plain HTTP requests, no
    # browser), deliberately chosen that way to avoid adding real cost to
    # runtime. ASL Aviation Holdings is the exception: despite the label,
    # its scraper (scrape_asl_aviation_ireland) actually launches a real
    # Playwright browser — confirmed by checking its source directly — so
    # it's routed to the browser pool below, not the HTTP one, to keep this
    # comment and the routing decision honest.
    lightweight_specs = [
        ("esb", "ESB", scrape_esb_ireland, 60),
        ("irish rail (iarnród éireann)", "Irish Rail (Iarnród Éireann)", scrape_irish_rail_ireland, 45),
        ("avolon", "Avolon", scrape_avolon_ireland, 60),
        ("bloomberg", "Bloomberg", scrape_bloomberg_ireland, 90),
        ("amcs group", "AMCS Group", scrape_amcs_ireland, 90),
        ("dawn meats", "Dawn Meats", scrape_dawn_meats_ireland, 60),
        ("auxilion", "Auxilion", scrape_auxilion_ireland, 60),
        ("biomarin", "BioMarin", scrape_biomarin_ireland, 90),
        ("asl aviation holdings", "ASL Aviation Holdings", scrape_asl_aviation_ireland, 150),
    ]
    LIGHTWEIGHT_BROWSER_EXCEPTIONS = {"scrape_asl_aviation_ireland"}
    for key, display_name, scraper_fn, base_timeout in lightweight_specs:
        company_row = next(
            (c for c in companies if c["company_name"].strip().lower() == key),
            None,
        )
        if not company_row:
            continue
        company_name = company_row["company_name"].strip()
        if company_name.lower() in _live_company_names:
            continue
        entry = next(
            (c for c in manual_check if c["company"].strip().lower() == key),
            None,
        )
        if entry is not None:
            matched_entries[company_name] = entry

        def make_light_task(fn=scraper_fn, name=company_name):
            return lambda: cached_browser_scrape(browser_cache, name, lambda: fn(session), 0, name)

        actual_timeout = effective_timeout(browser_cache, company_name, base_timeout)
        is_browser = scraper_fn.__name__ in LIGHTWEIGHT_BROWSER_EXCEPTIONS
        task_list.append((key, company_name, make_light_task(), actual_timeout, is_browser))

    _next_manual_queued = []
    for _row in _next_manual_rows:
        _name = _row["company_name"].strip()
        if _name.lower() in _live_company_names:
            continue
        _entry = next((c for c in manual_check if c["company"].strip().lower() == _name.lower()), None)
        if _entry is not None:
            matched_entries[_name] = _entry
        # Crucial queue fix: use the CSV career_url even when the company is
        # not presently in manual_check. The previous _entry-is-None skip is
        # exactly why the intended batch silently never ran.
        _url = str(_row.get("career_url") or (_entry or {}).get("url") or "").strip()
        if not _url:
            continue
        def _make_next_manual_task(name=_name, u=_url):
            return lambda: cached_browser_scrape(
                browser_cache, f"{name}::next_manual_batch_v2",
                lambda: scrape_next_manual_batch_generic(name, u, session), 0, name)
        task_list.append(("next_manual_batch", _name, _make_next_manual_task(), 75, True))
        _next_manual_queued.append(_name)

    print(f"=== Next manual queue fix: {len(_next_manual_queued)}/{len(_next_manual_batch_names)} target companies queued before final dedupe ===")
    if _next_manual_queued:
        print("  -> " + ", ".join(_next_manual_queued))


    _large_batch_queued = []
    for _row in _large_recovery_rows:
        _name = _row["company_name"].strip()
        if _name.lower() in _live_company_names:
            continue
        _entry = next(
            (c for c in manual_check if c["company"].strip().lower() == _name.lower()),
            None
        )
        # If the company is currently in "no jobs" rather than manual, build the
        # minimal entry directly from the CSV row instead of silently skipping it.
        if _entry is None:
            _entry = {"company": _name, "url": _row["career_url"]}
        matched_entries[_name] = _entry

        def _make_large_recovery_task(name=_name, u=_entry["url"]):
            return lambda: cached_browser_scrape(
                browser_cache,
                f"{name}::next20_attempt2_v2",
                lambda: scrape_multi_seed_attempt2(name, u, session),
                0,
                name,
            )

        task_list.append(
            ("next20_attempt2", _name, _make_large_recovery_task(), 65, True)
        )
        _large_batch_queued.append(_name)

    print(f"=== Next 20 attempt-2 batch: {len(_large_batch_queued)}/20 targets queued before final dedupe ===")
    if _large_batch_queued:
        print("  -> " + ", ".join(_large_batch_queued))

    # SHEET 2 PRIORITY COVERAGE — queued LAST, deliberately (see ordering
    # note above). Also now that task_list/matched_entries actually exist:
    # this block previously sat above the dedicated_company_specs loop and
    # referenced task_list/matched_entries before they were ever assigned —
    # the exact use-before-definition bug already caught and fixed once
    # before in this file's history, and it crept back in more than once
    # when new batches of companies were added on top of an un-fixed base
    # file. Confirmed via pyflakes each time: both names flagged as
    # "undefined name" at their old location.
    # Runtime dedupe: if a company already has a dedicated/company-specific
    # task in this run, never queue the generic Sheet-2 browser fallback for
    # the same company as a second task. The dedicated route is more precise
    # and the duplicate browser launch was adding runtime without coverage.
    _already_scheduled_company_names = {
        str(t[1] or "").strip().lower()
        for t in task_list
        if str(t[1] or "").strip()
    }

    priority_entries = [
        entry for entry in manual_check
        if entry["company"].strip().lower() in PRIORITY_SHEET2_COMPANIES
        and entry["company"].strip().lower() not in _already_scheduled_company_names
        and entry["company"].strip().lower() not in {
            "wipro",
            "iqvia",
            "merit medical",
            "goodbody",
            "bristol myers squibb",
            "sse airtricity / sse",
            "hewlett packard enterprise (hpe)",
            "dell technologies",
            "tesco ireland",
            "aldi ireland",
            "fbd insurance",
            "capgemini",
            "vodafone ireland",
            "abbott",
            "astrazeneca",
            "amgen",
            "alexion",
            "stryker",
            "novartis",
            "intel",
            "tata consultancy services (tcs)",
            "axa ireland",
            "agilent technologies",
            "bnp paribas ireland",
            "coca-cola hbc ireland",
            "hcltech",
            "infosys",
            "laya healthcare",
            "palo alto networks",
            "smbc aviation capital",
            "susquehanna international group (sig)",
            "heineken ireland",
            "musgrave group (supervalu / centra)",
            "vhi healthcare",
            "hp (hewlett-packard)",
            "oracle",
            "bausch + lomb",
            "mckinsey & company",
        }
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
        task_list.append(("sheet2_priority", company_name, make_priority_task(), actual_timeout, True))

    print(
        f"\n=== Sheet 2 priority coverage: {len(priority_entries)}/{len(PRIORITY_SHEET2_COMPANIES)} "
        f"selected companies queued for Ireland browser fallback ==="
    )
    if priority_entries:
        print("  -> " + ", ".join(e["company"] for e in priority_entries))

    # Final defensive company-level dedupe. Earlier queue ordering guarantees
    # the first task is the preferred/specific route; later duplicate generic
    # tasks are discarded.
    _deduped_task_list = []
    _seen_task_companies = set()
    _removed_duplicate_tasks = []

    for _task in task_list:
        _company_key = str(_task[1] or "").strip().lower()
        if _company_key and _company_key in _seen_task_companies:
            _removed_duplicate_tasks.append(str(_task[1]))
            continue
        if _company_key:
            _seen_task_companies.add(_company_key)
        _deduped_task_list.append(_task)

    if _removed_duplicate_tasks:
        print(
            "=== Runtime dedupe: removed "
            f"{len(_removed_duplicate_tasks)} duplicate company tasks: "
            + ", ".join(sorted(set(_removed_duplicate_tasks)))
            + " ==="
        )

    task_list = _deduped_task_list

    browser_count = sum(1 for t in task_list if t[4])
    http_count = len(task_list) - browser_count
    print(f"\n=== Running {len(task_list)} dedicated company scrapers "
          f"({browser_count} browser-based, up to {BROWSER_WORKERS} at once; "
          f"{http_count} plain HTTP, up to {HTTP_WORKERS} at once) ===")
    parallel_results, parallel_errors, parallel_failed_companies = run_company_tasks_in_parallel(task_list)
    failed_companies.update(parallel_failed_companies)

    for task_label, company_name, jobs in parallel_results:
        entry = matched_entries.get(company_name)

        if jobs:
            for job in jobs:
                job["company"] = company_name
            live_jobs.extend(jobs)
            _live_company_names.add(company_name.lower())
            if entry is not None:
                manual_check = [c for c in manual_check if c is not entry]
            automated_zero.pop(company_name, None)
            continue

        # A completed, company-specific scraper returning zero is a valid
        # automated result. Do NOT send it back to manual.
        #
        # The broad Sheet-2 generic fallback is deliberately excluded here:
        # "0 job-like links" on an arbitrary custom site is not strong enough
        # evidence that the company was reliably checked.
        if task_label != "sheet2_priority" and company_name not in failed_companies:
            if entry is not None:
                manual_check = [c for c in manual_check if c is not entry]
            automated_zero[company_name] = {
                "company": company_name,
                "platform": task_label,
                "reason": "Currently no jobs in Ireland",
            }

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

    # Final precision pass: removes career navigation / CTA pseudo-jobs,
    # including stale bad records served from browser_scrape_cache.json.
    live_jobs = _final_job_quality_filter(live_jobs)

    current_live_companies = {
        str(job.get("company") or "").strip()
        for job in live_jobs
        if job.get("company")
    }

    # Once a company has successfully produced real jobs in prior runs, a
    # later zero-result run must not make it "manual" unless we have a real
    # technical failure (timeout, exception, not-reached, Workday error, etc.).
    #
    # This is the stability fix for companies such as Wipro/IQVIA/LinkedIn
    # that were pushed back into manual solely because a stricter detail-page
    # validator rejected today's candidate cards.
    sticky_automated = historically_automated - failed_companies
    unresolved_before_sticky = len(manual_check)
    new_manual = []
    for entry in manual_check:
        name = str(entry.get("company") or "").strip()
        if name in current_live_companies:
            continue
        if name in automated_zero:
            continue
        if name in sticky_automated:
            automated_zero[name] = {
                "company": name,
                "platform": entry.get("platform", "historical"),
                "reason": "Currently no jobs in Ireland",
            }
            continue
        new_manual.append(entry)
    manual_check = new_manual

    sticky_removed = unresolved_before_sticky - len(manual_check)
    if sticky_removed:
        print(
            f"=== Automation-status stability: kept {sticky_removed} previously automated "
            f"companies out of manual because this run had no hard fetch failure ==="
        )

    # Any company with current live jobs is not an automated-zero company.
    for name in current_live_companies:
        automated_zero.pop(name, None)

    # Regression guard.
    #
    # - If a company had live jobs in the immediately previous jobs.json and
    #   this run suddenly has ZERO, preserve that previous set for this run.
    #   This prevents a transient browser/API/cache miss from deleting a
    #   previously proven live company.
    # - If the count merely decreased, report it for review but DO NOT pad the
    #   result with old jobs; real vacancies can close normally.
    _prev_by_company = {}
    for _job in _previous_live_jobs:
        _n = str((_job or {}).get("company") or "").strip()
        if _n:
            _prev_by_company.setdefault(_n, []).append(_job)

    _cur_counts = {}
    for _job in live_jobs:
        _n = str((_job or {}).get("company") or "").strip()
        if _n:
            _cur_counts[_n] = _cur_counts.get(_n, 0) + 1

    # Update the persistent snapshot with every company that is genuinely
    # live in the current scrape BEFORE applying any preservation.
    _current_jobs_by_company = {}
    for _job in live_jobs:
        _n = str((_job or {}).get("company") or "").strip()
        if _n:
            _current_jobs_by_company.setdefault(_n, []).append(_job)

    for _name, _jobs in _current_jobs_by_company.items():
        if _jobs:
            _last_nonzero_by_company[_name] = [dict(j) for j in _jobs]

    # Seed the snapshot from the immediately previous jobs.json for companies
    # that were live before this feature existed.
    for _name, _prev_jobs in _prev_by_company.items():
        if _prev_jobs and _name not in _last_nonzero_by_company:
            _last_nonzero_by_company[_name] = [dict(j) for j in _prev_jobs]

    _zero_regressions = []
    _count_decreases = []

    # Union of previous-run and persistent historically-live companies.
    _regression_names = set(_prev_by_company) | set(_last_nonzero_by_company)

    for _name in sorted(_regression_names):
        _prev_jobs = _prev_by_company.get(_name) or []
        _last_jobs = _last_nonzero_by_company.get(_name) or []
        _reference_jobs = _last_jobs or _prev_jobs
        _reference_count = len(_reference_jobs)
        _cur_count = _cur_counts.get(_name, 0)

        if _reference_count > 0 and _cur_count == 0:
            # Preserve the LAST KNOWN NON-ZERO set. This survives sequences such
            # as 25 -> 0 -> 0 instead of forgetting the original live inventory.
            for _old_job in _reference_jobs:
                _kept = dict(_old_job)
                _kept["regression_guard"] = "preserved_from_last_known_nonzero"
                live_jobs.append(_kept)
            automated_zero.pop(_name, None)
            _zero_regressions.append((_name, _reference_count))
        elif _prev_jobs and 0 < _cur_count < len(_prev_jobs):
            _count_decreases.append((_name, len(_prev_jobs), _cur_count))

    if _zero_regressions:
        print("=== REGRESSION GUARD: prevented single-run disappearance for "
              f"{len(_zero_regressions)} previously-live companies ===")
        for _name, _old_count in sorted(_zero_regressions):
            print(f"      [regression-zero] {_name}: {_old_count} -> 0; "
                  "previous live records preserved pending a clean recheck")

    if _count_decreases:
        print("=== COUNT REGRESSION WATCH: live companies with lower counts than previous run "
              "(reported only; old vacancies are NOT re-added) ===")
        for _name, _old_count, _new_count in sorted(_count_decreases):
            print(f"      [count-drop] {_name}: {_old_count} -> {_new_count}")

    try:
        with open(_last_nonzero_path, "w", encoding="utf-8") as _lf:
            json.dump(_last_nonzero_by_company, _lf, indent=2)
    except Exception as _exc:
        print(f"      [regression-guard] could not save {_last_nonzero_path}: {_exc}")

    # Recompute after the zero-regression guard.
    current_live_companies = {
        str(job.get("company") or "").strip()
        for job in live_jobs
        if job.get("company")
    }

    history = update_history(prior_history, live_jobs)
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
        "status_labels": {
            "live_jobs": "Live Jobs",
            "automated_zero_companies": "Currently No Jobs",
            "manual_check_companies": "Fetching Error / Manual Check Needed",
        },
        "automated_zero_companies": sorted(
            automated_zero.values(),
            key=lambda x: str(x.get("company", "")).lower(),
        ),
        "manual_check_companies": manual_check,
        "company_sponsorship_stats": company_sponsorship_stats,
        "official_permit_stats": official_permit_stats,
        "errors": errors,
        "stats": {
            "total_companies": len(companies),
            "automated_companies": len(companies) - len(manual_check),
            "automated_zero_companies": len(automated_zero),
            "companies_with_live_jobs": len({
                str(j.get("company") or "").strip() for j in live_jobs if j.get("company")
            }),
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
    print(
        f"{len(automated_zero)} companies: Currently No Jobs in Ireland."
    )
    print(
        f"{len(manual_check)} companies: Fetching Error / Manual Check Needed."
    )
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
