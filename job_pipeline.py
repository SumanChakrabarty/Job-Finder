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


def is_ireland_location(location_text: str) -> bool:
    if not location_text:
        return False
    lt = location_text.lower()
    return any(hint in lt for hint in IRELAND_LOCATION_HINTS)


def guess_employment_type(bullet_fields):
    if not bullet_fields:
        return "Unspecified"
    for b in bullet_fields:
        bl = str(b).lower()
        if "full time" in bl or "full-time" in bl:
            return "Full-time"
        if "part time" in bl or "part-time" in bl:
            return "Part-time"
        if "contract" in bl:
            return "Contract"
        if "intern" in bl:
            return "Internship"
        if "temporary" in bl:
            return "Temporary"
    return "Unspecified"


def normalize_employment_type(raw):
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
    if not raw:
        return "Unspecified"
    original = str(raw).lower()

    def word(pattern):
        return re.search(pattern, original) is not None

    if word(r"\bintern(?:ship)?\b"):
        return "Internship"
    if word(r"\bpart[\s-]?time\b"):
        return "Part-time"
    if word(r"\btemp(?:orary)?\b"):  # 'temp' alone should count too, not just 'temporary'
        return "Temporary"
    if word(r"\b(?:contract(?:or)?|freelance)\b"):
        # NOTE: 'consultant' deliberately excluded — it's commonly a
        # permanent full-time JOB TITLE at many companies (Accenture,
        # Deloitte, etc.), not a genuine employment-type signal. Treating
        # it as Contract would misclassify real full-time consultants.
        return "Contract"
    if word(r"\b(?:full[\s-]?time|permanent|regular)\b"):
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
        {"appliedFacets": {}, "limit": limit, "offset": offset, "searchText": "Ireland"},
    ]
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
                    "employment_type": guess_employment_type(job.get("bulletFields")),
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
    e.g. 'VMware (Broadcom)' -> ['vmware', 'broadcom']; 'HubSpot' -> ['hubspot']"""
    base = re.sub(r"\([^)]*\)", " ", company_name)  # drop "(Broadcom)" etc.
    base = CORP_SUFFIX_RE.sub(" ", base)
    words = re.findall(r"[a-zA-Z0-9]+", base)
    if not words:
        return []
    slugs = set()
    slugs.add("".join(words).lower())
    slugs.add("-".join(words).lower())
    slugs.add(words[0].lower())
    slugs.add("".join(words).lower() + "jobs")  # e.g. HubSpot's real board token is 'hubspotjobs', not 'hubspot'
    if len(words) >= 2:
        slugs.add("".join(words[:2]).lower())   # first two words joined, e.g. "johnsonjohnson"
        slugs.add("-".join(words[:2]).lower())  # first two words hyphenated
    return list(slugs)[:6]  # keep probing bounded but a bit wider than before


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
        "employment_type": "Unspecified",
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
        "employment_type": normalize_employment_type(categories.get("commitment")),
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
        "employment_type": normalize_employment_type(raw_employment_type),
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
        "employment_type": normalize_employment_type(job.get("employmentType")),
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
        "employment_type": normalize_employment_type(job.get("employment_type_code")),
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
        "employment_type": normalize_employment_type(field("employmentType")),
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
        "employment_type": normalize_employment_type(job.get("employmentType") or job.get("employment_type")),
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
    """The correct, documented Eightfold pattern (confirmed via a public
    open-source ATS-scraping reference, not guessed): fetch the real
    careers page, pull the company's internal '_EF_GROUP_ID' token out of
    its embedded JS, then call the actual search API with that ID. My
    earlier attempts guessed a plausible-looking but wrong endpoint and a
    wrong ID value (the domain name instead of this internal token) —
    that's why real, confirmed Eightfold tenants (Eaton) weren't matching
    despite genuinely being on this platform."""
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
        "employment_type": normalize_employment_type(job.get("employment_type")),
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
        "employment_type": normalize_employment_type(job.get("type")),
        "url": url,
        "source": "phenom_widgets",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


PROBE_VERSION = 11  # bump whenever a new ATS platform is added to the probe list, or slug guessing changes


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
    known_platforms = ("greenhouse", "lever", "smartrecruiters", "ashby", "recruitee", "personio", "pinpoint", "eightfold", "phenom")

    for entry in manual_companies:
        name, url = entry["company"], entry["url"]
        cached = cache.get(name)

        if cached and cached.get("platform") in known_platforms:
            platform, slug = cached["platform"], cached["slug"]
        elif cached and cached.get("platform") == "none":
            still_manual.append(entry)
            continue
        else:
            platform, slug = None, None
            if name in KNOWN_PHENOM_DOMAINS:
                known_domain, known_path = KNOWN_PHENOM_DOMAINS[name]
                ref_num, jobs_found = try_phenom_domain(known_domain, session, exact_path=known_path)
                if jobs_found:
                    platform, slug = "phenom", f"{known_domain}|{ref_num}"
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
                    phenom_domain, phenom_ref, phenom_jobs = try_phenom(candidate, session)
                    if phenom_jobs:
                        platform, slug = "phenom", f"{phenom_domain}|{phenom_ref}"
                        break
            cache[name] = {"platform": platform or "none", "slug": slug}
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", default="Job_Automation.csv")
    ap.add_argument("--output", default="jobs.json")
    ap.add_argument("--history", default="sponsorship_history.json")
    ap.add_argument("--seen", default="seen_jobs.json")
    ap.add_argument("--no-descriptions", action="store_true",
                     help="Skip fetching full job descriptions (faster, but no visa sponsorship signal)")
    args = ap.parse_args()

    companies = load_companies(args.input)
    print(f"Loaded {len(companies)} companies from {args.input}")

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
