# Ireland Job Radar — Pipeline + Dashboard

## What this is
A free, GitHub-hosted job-hunting pipeline built from your `Job_Automation.csv` (397 target companies):

1. **`job_pipeline.py`** — pulls live Ireland job postings, flags which ones are new since the last check, and opens a GitHub Issue (= free notification) when it finds new ones.
2. **`visa_stats.py`** — downloads Ireland's official government employment-permit records and matches them to your companies (run monthly).
3. **`dashboard.html`** — a single-file, click-through card dashboard, live-hosted on GitHub Pages, auto-refreshing every 5 minutes. Filter by Company, Location, Posted within, Employment type, Visa sponsorship, and "New since last check."
4. **`.github/workflows/`** — two scheduled GitHub Actions that run everything automatically, for free.

**Every card is clickable and takes you straight through — no second search required.** What "through" means depends on the company:
- **Live matches tab (~46 companies):** click opens the *exact job posting* — the actual page with the Apply button for that specific role.
- **Other companies tab (~351 companies):** click opens that company's *careers page* — I don't have job-level data for these (see coverage note below), so this is the closest "direct link" possible without a scraper for every individual site. It's still one click, no searching by hand.

## 1. Coverage — what's automated now vs. still manual

| Coverage | How |
|---|---|
| **Workday companies (~40)** | Live via Workday's public JSON search API. |
| **Greenhouse / Lever companies (varies)** | The pipeline now auto-probes each "manual" company against Greenhouse's and Lever's public APIs using guessed board slugs (e.g. "notion", "figma"). If one hits, that company moves out of the manual list automatically — no config needed. How many convert depends on how many of your 357 non-Workday companies happen to run one of these two platforms under a custom domain; you'll see the exact count and names printed each run. |
| **Everyone else** | Still needs a purpose-built scraper per site (custom React apps, Oracle HCM, SuccessFactors, iCIMS, JS-rendered pages, bot protection, etc.) — genuinely not automatable without one script per company. These stay in the dashboard's Directory tab as direct links. |

This is a real improvement over v2, not a full fix — I want to be clear I can't promise 100% coverage of 397 arbitrary company websites. If you tell me which of the manual-list companies matter most to you, I can look at whether any use a platform worth adding a dedicated fetcher for (SmartRecruiters and Ashby are the next most common and could be added the same way).

## 2. Near-real-time updates + free notifications
- Every run compares against `seen_jobs.json` and tags anything new as `new_since_last_check`. The dashboard shows a **NEW** ribbon and a filter for it.
- When the GitHub Actions workflow finds new postings, it **opens a GitHub Issue** listing them, labeled `new-jobs`. GitHub already emails/push-notifies you about new issues on repos you watch — so this is a genuinely free notification with zero extra setup (no SMTP, no webhook, no third-party service, no API key beyond the token GitHub provides automatically).
- The schedule runs every 15 minutes — GitHub's practical minimum for free scheduled Actions (it can be a few minutes late during busy periods; that's normal, not a bug).

## 3. Visa sponsorship — now backed by real government data
Two signals now feed the dashboard's visa badge, in priority order:

1. **Official DETE record** (`visa_stats.py`) — Ireland's Department of Enterprise, Tourism and Employment publishes, every month, the actual list of employers who were issued work permits, and how many. This is real historical fact, not a guess: e.g. "DETE record: 39 permits (2024–2026)." Source: https://enterprise.gov.ie/en/publications/employment-permit-statistics-2026.html
2. **Text-scan estimate** (`job_pipeline.py`, as before) — when there's no official match, falls back to scanning job descriptions for sponsorship language, with a rarity label built from a running sample size.

**Caveats worth knowing:**
- The government file lists legal entity names ("Google Ireland Limited"), which the script fuzzy-matches to your CSV's casual company names ("Google"). `visa_stats.py` prints its detected matches — skim `official_permit_stats.json` once after the first run and delete any wrong matches by hand.
- A permit count is history, not a promise for a specific open role — a company that sponsored 40 permits last year might not sponsor this particular vacancy. Use it to prioritize where to apply, not as a guarantee.
- DETE updates this data roughly monthly, so `visa_stats.py` only needs to run monthly (there's a separate, less-frequent workflow for it).

## Setup

```bash
pip install requests openpyxl
python job_pipeline.py            # live jobs + new-postings detection
python visa_stats.py              # official government sponsorship stats (run monthly)
```

This writes `jobs.json`, plus supporting state files you should keep between runs (don't delete them):
`sponsorship_history.json`, `seen_jobs.json`, `ats_platform_cache.json`, `official_permit_stats.json`.

Open `dashboard.html` in your browser and click **Load jobs.json**.

## Making the dashboard permanently live on GitHub (free)

This is the exact sequence — follow it in order, nothing skipped.

**1. Create the repo.**
Go to github.com → New repository → name it (e.g. `job-radar`) → **must be Public** (GitHub Pages is only free on public repos — private repos can run the Actions, but can't serve Pages for free). Don't add a README/gitignore, keep it empty.

**2. Push this folder to it.**
Unzip what I gave you, then from inside that folder:
```bash
cd job-radar
git init
git add .
git commit -m "Initial job radar setup"
git branch -M main
git remote add origin https://github.com/<your-username>/job-radar.git
git push -u origin main
```

**3. Give the Actions workflow permission to push back to the repo.**
This step is easy to miss and the run will silently fail without it:
Repo → **Settings → Actions → General** → scroll to "Workflow permissions" → select **"Read and write permissions"** → Save.

**4. Turn on GitHub Pages.**
Repo → **Settings → Pages** → under "Build and deployment", Source: **"Deploy from a branch"** → Branch: **main**, folder **/ (root)** → Save. Wait ~1 minute. Your dashboard is now live at:
```
https://<your-username>.github.io/job-radar/dashboard.html
```
Bookmark that URL — that's the one you actually use from now on. It fetches `jobs.json` from the same site automatically, no manual loading.

**5. Trigger the first data run manually** (don't wait for the 15-minute schedule):
Repo → **Actions** tab → click "refresh-jobs" in the left list → **"Run workflow"** button → Run. Do the same once for "refresh-official-visa-stats". After each finishes (~1–2 min), refresh your dashboard URL and you'll see real data.

**6. From here on, it runs itself:**
`refresh-jobs` runs every 15 minutes, commits the new `jobs.json`, and GitHub Pages auto-redeploys it — your open dashboard tab picks it up within 5 minutes on its own (no refresh needed). `refresh-official-visa-stats` runs monthly.

**7. To get notified of new postings:**
You're automatically "watching" your own repo, so new GitHub Issues (opened whenever new jobs are found, labeled `new-jobs`) trigger GitHub's normal notifications. Check Settings (top-right avatar) → Notifications → make sure "Issues" is on for email and/or the GitHub mobile app.

This entire setup costs nothing: public repos get free Pages hosting and enough free Actions minutes to run every 15 minutes indefinitely.

## File formats

`jobs.json` (produced by `job_pipeline.py`):
```json
{
  "generated_at": "...",
  "live_jobs": [
    {"company": "Pfizer", "title": "...", "location": "Dublin, Ireland",
     "posted_text": "Posted Today", "posted_days_ago": 0,
     "employment_type": "Full-time", "url": "https://...",
     "source": "workday_api | greenhouse_api | lever_api",
     "visa_sponsorship": "sponsors | no_sponsorship | not_mentioned",
     "new_since_last_check": true}
  ],
  "manual_check_companies": [{"company": "Stripe", "url": "...", "platform": "custom"}],
  "company_sponsorship_stats": {"Pfizer": {"sponsors": 4, "total": 20, "label": "..."}},
  "official_permit_stats": {"Pfizer": {"matched_employer_names": [...], "permits_by_year": {"2024": 12}, "total_permits": 39}},
  "stats": {"total_companies": 397, "automated_companies": 46, "manual_companies": 351, "live_jobs_found": N, "new_since_last_check": N}
}
```

## Extending further
- Add SmartRecruiters/Ashby/Recruitee probing the same way `try_greenhouse`/`try_lever` work, to convert more of the manual list.
- Add a job aggregator API (Adzuna, Jooble) as a last-resort layer for companies with none of the above.
