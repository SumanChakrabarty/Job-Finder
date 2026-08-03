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
from datetime import datetime, timezone

try:
    import requests
except ImportError:
    print("This script needs the 'requests' library: pip install requests")
    sys.exit(1)

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

CORP_SUFFIX_RE = re.compile(
    r"\b(limited|ltd|plc|unlimited company|uc|inc|incorporated|group|holdings|"
    r"ireland|international|corporation|corp|company|co|technologies|technology)\b",
    re.IGNORECASE,
)

HEADERS = {
    "Content-Type": "application/json",
    "User-Agent": "Mozilla/5.0 (compatible; job-search-dashboard/1.0)",
}

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


def fetch_job_description(tenant, wd_shard, site, external_path, session):
    detail_url = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/wday/cxs/{tenant}/{site}{external_path}"
    try:
        resp = session.get(detail_url, headers=HEADERS, timeout=15)
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


def fetch_workday_jobs(company_name, url, session, fetch_descriptions=True,
                        page_size=20, detail_delay=0.25):
    m = WORKDAY_URL_RE.search(url)
    if not m:
        return [], f"URL did not match Workday pattern: {url}"

    tenant, wd_shard, site = m.group(1), m.group(2), m.group(3)
    api_base = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/wday/cxs/{tenant}/{site}/jobs"
    site_base = f"https://{tenant}.{wd_shard}.myworkdayjobs.com/{site}"

    # First, small probe request just to read the facet list (no location
    # filter yet) so we can find Workday's own Ireland location facet IDs.
    applied_facets = {}
    max_pages = 10  # fallback cap if we can't find a location facet at all
    try:
        probe = session.post(api_base, headers=HEADERS,
                              json={"appliedFacets": {}, "limit": 1, "offset": 0, "searchText": ""},
                              timeout=15)
        probe.raise_for_status()
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
            max_pages = 60
    except Exception as e:
        return [], f"{company_name}: facet probe failed ({e})"

    results = []
    offset = 0
    error = None

    for _ in range(max_pages):
        payload = {"appliedFacets": applied_facets, "limit": page_size, "offset": offset, "searchText": ""}
        try:
            resp = session.post(api_base, headers=HEADERS, json=payload, timeout=15)
            resp.raise_for_status()
            data = resp.json()
        except Exception as e:
            error = f"{company_name}: request failed ({e})"
            break

        postings = data.get("jobPostings", [])
        if not postings:
            break

        for job in postings:
            location_text = job.get("locationsText", "") or job.get("bulletFields", [""])[0]
            # Keep this client-side check too, even with facet filtering on —
            # it's a cheap safety net against imprecise facets (e.g. a
            # "UK & Ireland" combined region matching too broadly).
            if not is_ireland_location(location_text):
                continue
            posted_text = job.get("postedOn", "")
            external_path = job.get("externalPath", "")

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
                "url": site_base.rstrip("/") + external_path,
                "source": "workday_api",
                "visa_sponsorship": sponsorship,
                "visa_snippet": snippet,
            })

        total = data.get("total", 0)
        offset += page_size
        if offset >= total:
            break
        time.sleep(0.3)

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
    return list(slugs)[:3]  # keep probing lightweight


def try_greenhouse(slug, session):
    try:
        resp = session.get(GREENHOUSE_JOBS_URL.format(slug=slug), timeout=10)
        if resp.status_code != 200:
            return None
        data = resp.json()
        jobs = data.get("jobs")
        return jobs if jobs else None
    except Exception:
        return None


def try_lever(slug, session):
    try:
        resp = session.get(LEVER_JOBS_URL.format(slug=slug), timeout=10)
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
        "employment_type": categories.get("commitment", "Unspecified") or "Unspecified",
        "url": job.get("hostedUrl", ""),
        "source": "lever_api",
        "visa_sponsorship": sponsorship,
        "visa_snippet": snippet,
    }


def probe_ats_for_manual_companies(manual_companies, session, cache_path):
    """For companies with no known API (custom sites), try a few likely
    Greenhouse/Lever board slugs. If one hits, that company's Ireland jobs
    get pulled automatically from then on instead of needing a manual visit.
    Results (including 'no match found') are cached so repeat runs don't
    re-probe the same misses every 15 minutes."""
    cache = {}
    if os.path.exists(cache_path):
        with open(cache_path, encoding="utf-8") as f:
            cache = json.load(f)

    still_manual = []
    discovered_jobs = []

    for entry in manual_companies:
        name, url = entry["company"], entry["url"]
        cached = cache.get(name)

        if cached and cached.get("platform") in ("greenhouse", "lever"):
            platform, slug = cached["platform"], cached["slug"]
        elif cached and cached.get("platform") == "none":
            still_manual.append(entry)
            continue
        else:
            platform, slug = None, None
            for candidate in candidate_slugs(name):
                jobs = try_greenhouse(candidate, session)
                if jobs is not None:
                    platform, slug = "greenhouse", candidate
                    break
                jobs = try_lever(candidate, session)
                if jobs is not None:
                    platform, slug = "lever", candidate
                    break
            cache[name] = {"platform": platform or "none", "slug": slug}
            if platform is None:
                still_manual.append(entry)
                continue

        # Fetch (or re-fetch) this company's postings.
        if platform == "greenhouse":
            jobs = try_greenhouse(slug, session) or []
            for job in jobs:
                norm = normalize_greenhouse_job(name, job)
                if norm:
                    discovered_jobs.append(norm)
        elif platform == "lever":
            jobs = try_lever(slug, session) or []
            for job in jobs:
                norm = normalize_lever_job(name, job)
                if norm:
                    discovered_jobs.append(norm)

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
    live_jobs, manual_check, errors = [], [], []

    for row in companies:
        name = row["company_name"].strip()
        url = row["career_url"].strip()
        kind = classify_url(url)

        if kind == "workday":
            print(f"  [workday] fetching {name} ...")
            jobs, err = fetch_workday_jobs(name, url, session, fetch_descriptions=not args.no_descriptions)
            live_jobs.extend(jobs)
            if err:
                errors.append(err)
            print(f"      -> {len(jobs)} Ireland postings")
        else:
            manual_check.append({"company": name, "url": url, "platform": kind})

    print(f"\nProbing remaining {len(manual_check)} companies for Greenhouse/Lever boards "
          f"(cached — only new/changed companies are actually re-probed)...")
    discovered_jobs, manual_check = probe_ats_for_manual_companies(
        manual_check, session, cache_path="ats_platform_cache.json")
    if discovered_jobs:
        found_companies = sorted(set(j["company"] for j in discovered_jobs))
        print(f"  -> Auto-discovered {len(discovered_jobs)} Ireland postings across "
              f"{len(found_companies)} companies previously in the manual list: {', '.join(found_companies)}")
    live_jobs.extend(discovered_jobs)

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
