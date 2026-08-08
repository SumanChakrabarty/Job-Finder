#!/usr/bin/env python3
"""
General Ireland job-search scraper.
Hits public ATS JSON APIs (Greenhouse, Lever, Ashby, …) and JSON-LD career pages.
Run by GitHub Actions hourly. Writes data.json for index.html.
"""

import json
import re
import time
import os
import html
import urllib.request
import urllib.error
import urllib.parse
from datetime import datetime, timezone, timedelta

try:
    import requests
except ImportError:
    requests = None

# ---------------------------------------------------------------------------
# Company list: (slug, ats) -- expand this over time as we confirm more boards
# ---------------------------------------------------------------------------

GREENHOUSE_COMPANIES = [
    "stripe", "airbnb", "doordash", "pinterest", "squarespace", "dropbox",
    "twilio", "docusign", "robinhood", "reddit", "coinbase", "gitlab",
    "github", "hubspot", "indeed", "zendesk", "trustpilot", "workhuman",
    "wayflyer", "intercom", "wise", "asana", "cloudflare", "datadog",
    "snowflake", "databricks", "instacart", "lyft", "fenergo", "affirm",
    "airtable", "algolia", "amplitude", "betterup", "box", "buffer",
    "calendly", "carta", "chime", "classpass", "coursera", "discord",
    "doximity", "elastic", "envoy", "faire", "figma", "flexport", "gusto",
    "handshake", "hashicorp", "honeycomb", "justworks", "klaviyo", "lattice",
    "mixpanel", "mongodb", "mural", "okta", "opendoor", "patreon", "peloton",
    "pilot", "postman", "procore", "quora", "rippling", "samsara", "segment",
    "sendgrid", "sourcegraph", "sprinklr", "strava", "tanium", "thumbtack",
    "toast", "turo", "udemy", "verkada", "webflow", "wework", "yelp",
    "zapier", "zoominfo", "getyourguide", "trivago", "deliveryhero",
    "babbel", "contentful", "celonis", "flixbus", "tiermobility", "gorillas",
    "typeform", "glovo", "cabify", "blablacar", "backmarket", "doctolib",
    "qonto", "alan", "payfit", "gocardless", "truelayer", "thoughtmachine",
    "cazoo", "octopusenergy", "farfetch", "starlingbank", "revolut",
    "darktrace", "graphcore", "onfido", "fundingcircle", "tines", "flipdish",
    "letsgetchecked", "genesys", "grab", "sea", "carousell", "razer",
    "lazada", "careem", "noon", "talabat", "propertyfinder", "razorpay",
    "swiggy", "freshworks", "browserstack", "meesho", "cred", "groww",
    "urbancompany", "chargebee", "clevertap",
    # Australia / New Zealand
    "canva", "cultureamp", "safetyculture", "employmenthero", "airwallex",
    "deputy", "linktree", "go1", "halter", "judobank",
]

LEVER_COMPANIES = [
    "netflix", "spotify", "plaid", "brex", "checkout", "deliveroo", "monzo",
    "wolt", "bolt", "pipedrive", "zopa", "gojek", "traveloka",
]

ASHBY_COMPANIES = [
    "notion", "linear", "ramp", "elevenlabs", "openai", "anthropic",
    "vercel", "scale", "deel", "partly", "clickup", "snowflake",
    "wayflyer", "harveynash",
]

# ---------------------------------------------------------------------------
# Workday-hosted career sites (*.myworkdayjobs.com). Workday has no official
# public jobs API, but every tenant's own career-site JSON endpoint --
# https://{tenant}.{wd_host}.myworkdayjobs.com/wday/cxs/{tenant}/{site}/jobs --
# is unauthenticated and freely queryable via POST, the same class of access
# already used for Greenhouse/Lever/Ashby above. Workday hard-caps each page
# at 20 results, so this paginates.
#
# (tenant, wd_host, site) -- verified working as of this build. Find more by
# opening any company's careers.<company>.com page, opening browser dev tools
# -> Network tab, and looking for a request to a "/wday/cxs/.../jobs" URL --
# the tenant/wd_host/site values are all in that URL.
# ---------------------------------------------------------------------------

WORKDAY_COMPANIES = [
    ('Accenture', 'accenture', 'wd103', 'AccentureCareers'),
    ('Salesforce', 'salesforce', 'wd12', 'External_Career_Site'),
    ('Workday', 'workday', 'wd5', 'Workday'),
    ('VMware (Broadcom)', 'broadcom', 'wd1', 'External_Career'),
    ('Genesys', 'genesys', 'wd1', 'Genesys'),
    ('Slack', 'salesforce', 'wd12', 'Slack'),
    ('Mastercard', 'mastercard', 'wd1', 'CorporateCareers'),
    ('PayPal', 'paypal', 'wd1', 'jobs'),
    ('Adobe', 'adobe', 'wd5', 'external_experienced'),
    ('Autodesk', 'autodesk', 'wd1', 'Ext'),
    ('Cadence Design Systems', 'cadence', 'wd1', 'External_Careers'),
    ('Analog Devices', 'analogdevices', 'wd1', 'External'),
    ('NVIDIA', 'nvidia', 'wd5', 'NVIDIAExternalCareerSite'),
    ('Broadcom', 'broadcom', 'wd1', 'External_Career'),
    ('NXP Semiconductors', 'nxp', 'wd3', 'careers'),
    ('Rockwell Automation', 'rockwellautomation', 'wd1', 'External_Rockwell_Automation'),
    ('Eaton', 'eaton', 'wd5', 'Eaton'),
    ('Pfizer', 'pfizer', 'wd1', 'PfizerCareers'),
    ('Sanofi', 'sanofi', 'wd3', 'SanofiCareers'),
    ('MSD (Merck Sharp & Dohme)', 'msd', 'wd5', 'SearchJobs'),
    ('Bausch + Lomb', 'bauschhealth', 'wd1', 'BauschHealthCareers'),
    ('Takeda', 'takeda', 'wd3', 'External'),
    ('Gilead Sciences', 'gilead', 'wd1', 'gileadcareers'),
    ('Edwards Lifesciences', 'edwards', 'wd1', 'EdwardsCareers'),
    ('Teleflex', 'teleflex', 'wd1', 'TeleflexCareers'),
    ('Zimmer Biomet', 'zimmerbiomet', 'wd1', 'Zimmer_Biomet_Careers'),
    ('Viatris', 'viatris', 'wd1', 'ViatrisCareers'),
    ('Teva Pharmaceuticals', 'teva', 'wd1', 'Teva_Careers'),
    ('Jazz Pharmaceuticals', 'jazzpharma', 'wd5', 'Jazz_Careers'),
    ('ResMed', 'resmed', 'wd1', 'ResMed_External_Careers'),
    ('Becton Dickinson (BD)', 'bd', 'wd1', 'BD_External'),
    ('Illumina', 'illumina', 'wd1', 'illumina-careers'),
    ('Catalent', 'catalent', 'wd1', 'External'),
    ('State Street', 'statestreet', 'wd1', 'Global'),
    ('Elavon', 'usbank', 'wd1', 'Elavon_Careers'),
    ('Northern Trust', 'northerntrust', 'wd1', 'External_Careers'),
    ('Deloitte Ireland', 'deloitteie', 'wd3', 'experienced_professionals'),
    ('PwC Ireland', 'pwc', 'wd3', 'Global_Experienced_Careers'),
    ('Grant Thornton Ireland', 'iegt', 'wd3', 'GTI_External_Careers_Experienced_Hires_ROI'),
    ('DXC Technology', 'dxc', 'wd1', 'DXC_Jobs'),
    ('Aon', 'aon', 'wd1', 'AonCareers'),
    ('Willis Towers Watson (WTW)', 'wtw', 'wd1', 'WTWCareers'),
    ('Mercer', 'mmc', 'wd1', 'MMC'),
    ('Marsh McLennan', 'mmc', 'wd1', 'MMC'),
    ('Diageo Ireland', 'diageo', 'wd3', 'Diageo_Careers'),
]

# ---------------------------------------------------------------------------
# SmartRecruiters has a genuinely documented public Postings API --
# https://api.smartrecruiters.com/v1/companies/{companyId}/postings -- but
# it's a per-customer toggle, so not every SmartRecruiters customer has it
# switched on. "smartrecruiters" itself (their own careers page) is
# SmartRecruiters' own documented example and confirmed working. Add more by
# checking https://api.smartrecruiters.com/v1/companies/{guess}/postings
# directly in a browser -- a 200 with JSON means it's enabled for that company.
# ---------------------------------------------------------------------------

SMARTRECRUITERS_COMPANIES = [
    "smartrecruiters", "servicenow", "aristanetworks", "abbvie",
    "eurofins", "version1", "primark",
]

# ---------------------------------------------------------------------------
# Three more genuinely free, unauthenticated ATS APIs. These skew toward
# SMB/mid-market and European scale-ups rather than Fortune-500-scale firms
# (that's who tends to run them) -- useful breadth, but don't expect them to
# unlock the big banks/telcos/national champions still marked "manual" in the
# company list. Ceiling for those: most run either a fully custom in-house
# platform (confirmed for Deutsche Bank -- careers.db.com has no ATS
# fingerprint at all) or an enterprise ATS (SAP SuccessFactors, Oracle
# Taleo/Recruiting Cloud, Phenom, Eightfold) that requires signed/session-
# based requests -- the same class of difficulty as Google/Apple/Meta, which
# is exactly why those three stayed on Apify instead of being reverse-
# engineered. For that remaining bucket the realistic options are: manual
# checking, an Apify actor per company (pay-per-result, browser automation
# handles the hard cases), or a paid cross-ATS aggregator (e.g. fantastic.jobs,
# jobspipe.dev) -- there is no free universal answer for them.
# ---------------------------------------------------------------------------

WORKABLE_COMPANIES = [
    # https://apply.workable.com/api/v1/widget/accounts/{slug} -- add slugs here
]

RECRUITEE_COMPANIES = [
    # https://{slug}.recruitee.com/api/offers/ -- add slugs here
]

PERSONIO_COMPANIES = [
    "dilloneustace",
]

PINPOINT_COMPANIES = [
    "ericsson", "ptsb", "kpmg", "morganmckinley", "greencore",
    "arcadis", "zendesk", "synopsys", "nutanix", "virgin", "terumo",
    "smith", "waterstones", "next",
]

# ---------------------------------------------------------------------------
# JSON-LD structured-data scraper -- universal fallback for the ~500-company
# "manual-check" bucket (big banks, telcos, national champions, most Big 4
# outside Accenture) that don't run any of the ATS platforms above.
#
# Most large-company career pages, regardless of ATS, embed a
# schema.org/JobPosting block as JSON-LD in their HTML specifically so
# Google for Jobs can index them -- this includes Workday, SuccessFactors,
# Taleo, and even fully custom sites. Instead of reverse-engineering each
# platform's internal API, this fetches the plain HTML of each career page
# and pulls the embedded structured job data straight out.
#
# This is genuinely free (just an HTTP GET) but NOT guaranteed coverage --
# it only works if the site bothered to add the markup. Expect a mixed hit
# rate: some companies will return real results, many will return zero.
# That's still strictly better than "manual-check only" at zero extra cost.
# List sourced from the "Career Page URL" column of company_shortlist_by_
# region.xlsx, limited to companies not already covered by a dedicated
# scraper above.
# ---------------------------------------------------------------------------

JSONLD_CAREER_PAGES = [
        ("Google (Ireland)", "https://www.google.com/about/careers/applications/jobs/results/?location=Dublin%2C%20Ireland"),
    ("Meta (Ireland)", "https://www.metacareers.com/locations/dublin"),
    ("Amazon (Ireland)", "https://www.amazon.jobs/en/locations/dublin-ireland"),
    ("Microsoft (Ireland)", "https://jobs.careers.microsoft.com/global/en/search?lc=Dublin%2C%20Ireland"),
    ("LinkedIn (Ireland)", "https://careers.linkedin.com/"),
    ("Workday (Ireland)", "https://workday.wd5.myworkdayjobs.com/Workday"),
    ("Salesforce (Ireland)", "https://careers.salesforce.com/en/"),
    ("Indeed (Ireland)", "https://www.indeed.jobs/"),
    ("TikTok (Ireland)", "https://careers.tiktok.com/"),
    ("Mastercard (Ireland)", "https://careers.mastercard.com/"),
    ("AIB", "https://aib.ie/careers"),
    ("Bank of Ireland", "https://careers.bankofireland.com/"),
    ("Deloitte Ireland", "https://www2.deloitte.com/ie/en/careers.html"),
    ("PwC Ireland", "https://www.pwc.ie/careers.html"),
    ("KPMG Ireland", "https://home.kpmg/ie/en/home/careers.html"),
    ("EY Ireland", "https://careers.ey.com/ey"),
    ("IBM Ireland", "https://www.ibm.com/ie-en/employment"),
    ("SAP Ireland", "https://jobs.sap.com/"),
    ("Version 1", "https://www.version1.com/careers/"),
    ("eBay/PayPal Ireland ops", "https://www.paypal.com/us/webapps/mpp/jobs"),
    ("Citi (Ireland)", "https://jobs.citi.com/"),
    ("State Street (Ireland)", "https://careers.statestreet.com/"),
    ("J.P. Morgan (Ireland)", "https://careers.jpmorgan.com/"),
    ("Three Ireland", "https://careers.three.ie/"),
    ("eir", "https://www.eir.ie/careers/"),
    ("Tesco Ireland", "https://www.tesco.ie/careers/"),
    ("Dunnes Stores", "https://www.dunnesstoresjobs.ie/"),
    ("SuperValu / Musgrave", "https://careers.musgravegroup.com/"),
    ("Ryanair", "https://careers.ryanair.com/"),
    ("Aer Lingus", "https://careers.aerlingus.com/"),
    ("Concentrix (Ireland)", "https://www.concentrix.com/careers/"),
    ("Teleperformance (Ireland)", "https://www.teleperformance.com/en-us/careers/"),
    ("Apple (Ireland)", "https://jobs.apple.com/en-ie/search"),
    ("Oracle (Ireland)", "https://www.oracle.com/careers/"),
    ("Emirates Group", "https://www.emiratesgroupcareers.com/"),
    ("Emaar Properties", "https://www.emaar.com/en/careers/"),
    ("ADNOC", "https://careers.adnoc.ae/"),
    ("e& (Etisalat)", "https://www.eand.com/en/careers.html"),
    ("DP World", "https://www.dpworld.com/careers"),
    ("Emirates NBD", "https://www.emiratesnbd.com/en/careers"),
    ("First Abu Dhabi Bank (FAB)", "https://www.bankfab.com/en-ae/careers"),
    ("Careem", "https://www.careem.com/careers/"),
    ("noon", "https://careers.noon.com/"),
    ("Mashreq Bank", "https://www.mashreq.com/en/uae/careers/"),
    ("Majid Al Futtaim", "https://careers.majidalfuttaim.com/"),
    ("Chalhoub Group", "https://www.chalhoubgroup.com/careers"),
    ("Deloitte UAE", "https://www2.deloitte.com/xe/en/careers.html"),
    ("PwC UAE", "https://www.pwc.com/m1/en/careers.html"),
    ("Amazon UAE", "https://www.amazon.jobs/en/locations/united-arab-emirates"),
    ("Microsoft UAE", "https://jobs.careers.microsoft.com/global/en/search?lc=United%20Arab%20Emirates"),
    ("Dubai Duty Free", "https://www.dubaidutyfree.com/en/careers"),
    ("LuLu Group (UAE)", "https://www.lulugroupinternational.com/careers"),
    ("Etihad Airways", "https://careers.etihad.com/"),
    ("du (EITC)", "https://www.du.ae/about-us/careers"),
    ("EY UAE", "https://www.ey.com/en_ae/careers"),
    ("KPMG UAE", "https://home.kpmg/ae/en/home/careers.html"),
    ("Google (UAE)", "https://www.google.com/about/careers/applications/jobs/results/?location=United%20Arab%20Emirates"),
    ("Meta (UAE)", "https://www.metacareers.com/locations/dubai"),
    ("Salesforce (UAE)", "https://careers.salesforce.com/en/"),
    ("Allegro", "https://about.allegro.eu/careers"),
    ("InPost", "https://grupainpost.pl/en/careers/"),
    ("CD Projekt", "https://www.cdprojekt.com/en/careers/"),
    ("mBank", "https://www.mbank.pl/kariera/"),
    ("PKO Bank Polski", "https://www.pkobp.pl/kariera/"),
    ("Santander Bank Polska", "https://www.santander.pl/kariera"),
    ("ING Poland", "https://www.ing.pl/kariera"),
    ("State Street (Krakow GBS)", "https://careers.statestreet.com/"),
    ("Capgemini Poland", "https://www.capgemini.com/pl-en/careers/"),
    ("IBM Poland", "https://www.ibm.com/pl-pl/employment"),
    ("HSBC GSC Krakow", "https://www.hsbc.com/careers"),
    ("Shell Business Operations Krakow", "https://www.shell.pl/careers.html"),
    ("Google Poland", "https://www.google.com/about/careers/applications/jobs/results/?location=Warsaw%2C%20Poland"),
    ("Amazon Poland", "https://www.amazon.jobs/en/locations/poland"),
    ("Luxoft (DXC)", "https://www.dxc.com/us/en/careers"),
    ("Comarch", "https://www.comarch.pl/kariera/"),
    ("Nordea Poland (GBS)", "https://www.nordea.com/en/careers"),
    ("Credit Suisse/UBS (Krakow GBS)", "https://www.ubs.com/careers"),
    ("Cisco Poland", "https://jobs.cisco.com/"),
    ("PZU", "https://kariera.pzu.pl/"),
    ("Orange Polska", "https://kariera.orange.pl/"),
    ("Zabka", "https://zabkagroup.com/en/careers/"),
    ("Deloitte Poland", "https://www2.deloitte.com/pl/en/careers.html"),
    ("PwC Poland", "https://www.pwc.pl/en/careers.html"),
    ("EY Poland", "https://www.ey.com/pl_pl/careers"),
    ("KPMG Poland", "https://home.kpmg/pl/en/home/careers.html"),
    ("Microsoft Poland", "https://jobs.careers.microsoft.com/global/en/search?lc=Warsaw%2C%20Poland"),
    ("Critical TechWorks (BMW)", "https://www.criticaltechworks.com/careers/"),
    ("Talkdesk", "https://www.talkdesk.com/careers/"),
    ("OutSystems", "https://www.outsystems.com/careers/"),
    ("Natixis (Porto GBS)", "https://www.natixis.com/natixis/en/careers"),
    ("Mercedes-Benz.io", "https://www.mercedes-benz.io/careers"),
    ("Cisco Portugal", "https://jobs.cisco.com/"),
    ("Deloitte Portugal", "https://www2.deloitte.com/pt/en/careers.html"),
    ("Vodafone Portugal", "https://careers.vodafone.com/"),
    ("EDP", "https://www.edp.com/en/careers"),
    ("Jeronimo Martins", "https://www.jeronimomartins.com/careers/"),
    ("Feedzai", "https://feedzai.com/careers/"),
    ("Teleperformance Portugal", "https://www.teleperformance.com/en-us/careers/"),
    ("Concentrix Portugal", "https://www.concentrix.com/careers/"),
    ("Sonae", "https://www.sonae.pt/en/careers/"),
    ("PwC Portugal", "https://www.pwc.pt/en/careers.html"),
    ("EY Portugal", "https://www.ey.com/pt_pt/careers"),
    ("KPMG Portugal", "https://home.kpmg/pt/en/home/careers.html"),
    ("Capgemini Portugal", "https://www.capgemini.com/pt-en/careers/"),
    ("HSBC (Hong Kong)", "https://www.hsbc.com/careers"),
    ("Standard Chartered (HK)", "https://www.sc.com/en/careers/"),
    ("Bank of China (Hong Kong)", "https://www.bochk.com/en/aboutus/careeropp.html"),
    ("AIA Group", "https://careers.aia.com/"),
    ("Prudential Hong Kong", "https://www.prudential.com.hk/en/careers/"),
    ("Jardine Matheson", "https://www.jardines.com/en/careers"),
    ("CLP Group", "https://www.clpgroup.com/en/careers"),
    ("Cathay Pacific", "https://careers.cathaypacific.com/"),
    ("PCCW", "https://www.pccw.com/en/careers.html"),
    ("Hang Seng Bank", "https://www.hangseng.com/en-hk/about-hang-seng/careers/"),
    ("DBS (Hong Kong)", "https://www.dbs.com/careers/"),
    ("Deloitte Hong Kong", "https://www2.deloitte.com/hk/en/careers.html"),
    ("PwC Hong Kong", "https://www.pwchk.com/en/careers.html"),
    ("Manulife Hong Kong", "https://careers.manulife.com/"),
    ("PARKnSHOP / AS Watson Group", "https://careers.aswatson.com/"),
    ("EY Hong Kong", "https://www.ey.com/en_hk/careers"),
    ("KPMG Hong Kong", "https://home.kpmg/cn/en/home/careers.html"),
    ("Google (Hong Kong)", "https://www.google.com/about/careers/applications/jobs/results/?location=Hong%20Kong"),
    ("Microsoft (Hong Kong)", "https://jobs.careers.microsoft.com/global/en/search?lc=Hong%20Kong"),
    ("Amazon (Hong Kong)", "https://www.amazon.jobs/en/locations/hong-kong"),
    ("Maybank", "https://www.maybank.com/en/careers.page"),
    ("CIMB Group", "https://www.cimb.com/en/careers.html"),
    ("Public Bank", "https://www.pbebank.com/careers.html"),
    ("AirAsia", "https://careers.airasia.com/"),
    ("Petronas", "https://www.petronas.com/careers"),
    ("Grab Malaysia", "https://grab.careers/"),
    ("Shopee Malaysia", "https://careers.shopee.com/"),
    ("DXC Technology Malaysia", "https://dxc.com/my/en/careers"),
    ("IBM Malaysia", "https://www.ibm.com/my-en/employment"),
    ("HSBC Electronic Data Processing (Malaysia)", "https://www.hsbc.com/careers"),
    ("AIA Malaysia", "https://careers.aia.com/"),
    ("Genting Group", "https://www.genting.com/careers/"),
    ("AEON Malaysia", "https://www.aeonretail.com.my/careers/"),
    ("Deloitte Malaysia", "https://www2.deloitte.com/my/en/careers.html"),
    ("PwC Malaysia", "https://www.pwc.com/my/en/careers.html"),
    ("EY Malaysia", "https://www.ey.com/en_my/careers"),
    ("KPMG Malaysia", "https://home.kpmg/my/en/home/careers.html"),
    ("Microsoft Malaysia", "https://jobs.careers.microsoft.com/global/en/search?lc=Malaysia"),
    ("Google Malaysia", "https://www.google.com/about/careers/applications/jobs/results/?location=Malaysia"),
    ("ASML", "https://www.asml.com/en/careers"),
    ("Philips", "https://www.careers.philips.com/"),
    ("ING", "https://www.ing.jobs/"),
    ("Booking.com", "https://careers.booking.com/"),
    ("Adyen", "https://www.adyen.com/careers"),
    ("Shell (NL)", "https://www.shell.com/careers.html"),
    ("Ahold Delhaize", "https://www.aholddelhaize.com/en/careers/"),
    ("Heineken", "https://www.theheinekencompany.com/careers"),
    ("KLM", "https://werkenbijklm.com/en/"),
    ("Rabobank", "https://www.rabobank.jobs/en/"),
    ("ABN AMRO", "https://www.abnamro.com/en/careers"),
    ("Randstad", "https://www.randstad.com/careers/"),
    ("Wolters Kluwer", "https://www.wolterskluwer.com/en/careers"),
    ("Mollie", "https://jobs.mollie.com/"),
    ("Bol.com", "https://werkenbij.bol.com/"),
    ("Coolblue", "https://werkenbij.coolblue.nl/"),
    ("Uber (Netherlands ops)", "https://www.uber.com/us/en/careers/"),
    ("Deloitte Netherlands", "https://www2.deloitte.com/nl/en/careers.html"),
    ("Capgemini Netherlands", "https://www.capgemini.com/nl-en/careers/"),
    ("KPN", "https://www.werkenbijkpn.com/"),
    ("Jumbo Supermarkten", "https://werkenbijjumbo.nl/"),
    ("TomTom", "https://www.tomtom.com/careers/"),
    ("PwC Netherlands", "https://www.pwc.nl/en/careers.html"),
    ("EY Netherlands", "https://www.ey.com/nl_nl/careers"),
    ("KPMG Netherlands", "https://home.kpmg/nl/en/home/careers.html"),
    ("Microsoft Netherlands", "https://jobs.careers.microsoft.com/global/en/search?lc=Netherlands"),
    ("SAP", "https://jobs.sap.com/"),
    ("Siemens", "https://jobs.siemens.com/"),
    ("Bosch", "https://careers.bosch.com/"),
    ("BMW Group", "https://www.bmwgroup.jobs/"),
    ("Mercedes-Benz Group", "https://career.mercedes-benz.com/"),
    ("Volkswagen Group", "https://www.volkswagenag.com/en/career.html"),
    ("Deutsche Bank", "https://careers.db.com/"),
    ("Allianz", "https://careers.allianz.com/"),
    ("Deutsche Telekom", "https://www.telekom.com/en/careers"),
    ("N26", "https://n26.com/en/careers"),
    ("Personio", "https://www.personio.com/career/"),
    ("HelloFresh", "https://careers.hellofresh.com/"),
    ("Trade Republic", "https://traderepublic.com/en-de/careers"),
    ("DHL / Deutsche Post", "https://careers.dhl.com/"),
    ("BASF", "https://www.basf.com/global/en/careers.html"),
    ("Continental", "https://www.continental.com/en/career/"),
    ("Commerzbank", "https://www.commerzbank.de/en/karriere/"),
    ("Lufthansa", "https://www.lufthansagroup.careers/"),
    ("Munich Re", "https://careers.munichre.com/"),
    ("E.ON", "https://careers.eon.com/"),
    ("Infineon", "https://www.infineon.com/cms/en/careers/"),
    ("Software AG", "https://www.softwareag.com/en_corporate/company/careers.html"),
    ("Deloitte Germany", "https://www2.deloitte.com/de/en/careers.html"),
    ("Capgemini Germany", "https://www.capgemini.com/de-en/careers/"),
    ("REWE Group", "https://karriere.rewe-group.com/"),
    ("Lidl / Schwarz Group", "https://jobs.lidl.com/"),
    ("Aldi", "https://karriere.aldi-sued.de/"),
    ("Deutsche Bahn", "https://www.deutschebahn.com/en/career"),
    ("Apple (Germany)", "https://jobs.apple.com/en-de"),
    ("PwC Germany", "https://www.pwc.de/en/careers.html"),
    ("EY Germany", "https://www.ey.com/de_de/careers"),
    ("KPMG Germany", "https://home.kpmg/de/en/home/careers.html"),
    ("Google (Germany)", "https://www.google.com/about/careers/applications/jobs/results/?location=Munich%2C%20Germany"),
    ("Microsoft Germany", "https://jobs.careers.microsoft.com/global/en/search?lc=Germany"),
    ("Amazon (Germany)", "https://www.amazon.jobs/en/locations/germany"),
    ("Salesforce Germany", "https://careers.salesforce.com/en/"),
    ("Erste Group", "https://www.erstegroup.com/en/about-us/careers"),
    ("Raiffeisen Bank International", "https://www.rbinternational.com/en/careers.html"),
    ("OMV", "https://www.omv.com/en/careers"),
    ("Voestalpine", "https://www.voestalpine.com/group/en/careers/"),
    ("Red Bull", "https://jobs.redbull.com/"),
    ("A1 Telekom Austria", "https://a1.jobs/"),
    ("Andritz", "https://www.andritz.com/careers-en/"),
    ("BAWAG Group", "https://www.bawaggroup.com/BAWAGGROUP/BG/EN/Careers"),
    ("Verbund", "https://www.verbund.com/en-at/about-verbund/career"),
    ("Spar Austria", "https://www.spar.at/karriere"),
    ("Rewe Austria (Billa/Merkur)", "https://karriere.rewe-group.at/"),
    ("Deloitte Austria", "https://www2.deloitte.com/at/en/careers.html"),
    ("PwC Austria", "https://www.pwc.at/en/careers.html"),
    ("EY Austria", "https://www.ey.com/de_at/careers"),
    ("KPMG Austria", "https://home.kpmg/at/en/home/careers.html"),
    ("Saudi Aramco", "https://careers.aramco.com/"),
    ("STC (Saudi Telecom)", "https://www.stc.com.sa/wps/wcm/connect/english/individual/aboutus/careers"),
    ("SABIC", "https://www.sabic.com/en/careers"),
    ("Al Rajhi Bank", "https://www.alrajhibank.com.sa/en/careers"),
    ("NEOM", "https://www.neom.com/en-us/careers"),
    ("Riyad Bank", "https://www.riyadbank.com/en/careers"),
    ("Saudi National Bank (SNB)", "https://www.alahli.com/en-us/about-us/careers"),
    ("Almarai", "https://www.almarai.com/en/careers/"),
    ("Jahez", "https://www.jahez.net/en/careers/"),
    ("Deloitte Saudi Arabia", "https://www2.deloitte.com/xe/en/careers.html"),
    ("PwC Saudi Arabia", "https://www.pwc.com/m1/en/careers.html"),
    ("Red Sea Global", "https://www.redseaglobal.com/en/careers"),
    ("Qiddiya", "https://www.qiddiya.com/careers"),
    ("Panda Retail Company", "https://www.pandaretailcompany.com/careers/"),
    ("Extra (United Electronics)", "https://www.extra.com/en-sa/careers"),
    ("Saudia (airline)", "https://www.saudia.com/about-saudia/careers"),
    ("flynas", "https://www.flynas.com/en/about-flynas/careers"),
    ("EY Saudi Arabia", "https://www.ey.com/en_sa/careers"),
    ("KPMG Saudi Arabia", "https://home.kpmg/sa/en/home/careers.html"),
    ("Microsoft Saudi Arabia", "https://jobs.careers.microsoft.com/global/en/search?lc=Saudi%20Arabia"),
    ("Amazon (Saudi Arabia)", "https://www.amazon.jobs/en/locations/saudi-arabia"),
    ("Nokia", "https://www.nokia.com/careers/"),
    ("KONE", "https://www.kone.com/en/careers/"),
    ("Wartsila", "https://www.wartsila.com/careers"),
    ("Nordea (Finland)", "https://www.nordea.com/en/careers"),
    ("OP Financial Group", "https://www.op.fi/en/careers"),
    ("Fortum", "https://www.fortum.com/about-us/careers"),
    ("Kesko", "https://www.kesko.fi/en/careers/"),
    ("Neste", "https://www.neste.com/careers"),
    ("Supercell", "https://supercell.com/en/careers/"),
    ("Wolt (DoorDash)", "https://careers.wolt.com/"),
    ("S Group (S-ryhma)", "https://www.s-kanava.fi/web/s/tyopaikat"),
    ("Finnair", "https://careers.finnair.com/"),
    ("Accenture Finland", "https://accenture.wd103.myworkdayjobs.com/AccentureCareers"),
    ("Deloitte Finland", "https://www2.deloitte.com/fi/en/careers.html"),
    ("PwC Finland", "https://www.pwc.fi/en/careers.html"),
    ("EY Finland", "https://www.ey.com/fi_fi/careers"),
    ("KPMG Finland", "https://home.kpmg/fi/en/home/careers.html"),
    ("KBC Group", "https://www.kbc.com/en/careers.html"),
    ("ING Belgium", "https://www.ing.jobs/belgium"),
    ("Belfius", "https://www.belfius.be/about-us/en/careers"),
    ("Proximus", "https://jobs.proximus.com/"),
    ("Colruyt Group", "https://www.jobat.be/en/employers/colruyt-group"),
    ("AB InBev", "https://www.ab-inbev.com/careers/"),
    ("Solvay", "https://www.solvay.com/en/careers"),
    ("UCB", "https://www.ucb.com/careers"),
    ("bpost", "https://career.bpost.be/"),
    ("Deloitte Belgium", "https://www2.deloitte.com/be/en/careers.html"),
    ("PwC Belgium", "https://www.pwc.be/en/careers.html"),
    ("EY Belgium", "https://www.ey.com/en_be/careers"),
    ("KPMG Belgium", "https://home.kpmg/be/en/home/careers.html"),
    ("Euroclear", "https://www.euroclear.com/careers/"),
    ("SWIFT", "https://www.swift.com/careers"),
    ("Delhaize Belgium", "https://www.delhaizegroup.com/en/careers"),
    ("Infosys", "https://www.infosys.com/careers.html"),
    ("Amazon (India)", "https://www.amazon.jobs/en/locations/india"),
    ("JPMorgan Chase (India)", "https://careers.jpmorgan.com/"),
    ("SAP Labs India", "https://jobs.sap.com/"),
    ("TCS", "https://www.tcs.com/careers"),
    ("Wipro", "https://careers.wipro.com/"),
    ("HCLTech", "https://www.hcltech.com/careers"),
    ("Cognizant (India)", "https://careers.cognizant.com/"),
    ("Capgemini India", "https://www.capgemini.com/in-en/careers/"),
    ("IBM India", "https://www.ibm.com/in-en/employment"),
    ("Deloitte India", "https://www2.deloitte.com/in/en/careers.html"),
    ("EY India", "https://www.ey.com/en_in/careers"),
    ("PwC India", "https://www.pwc.in/careers.html"),
    ("KPMG India", "https://home.kpmg/in/en/home/careers.html"),
    ("Flipkart", "https://www.flipkartcareers.com/"),
    ("Zomato", "https://www.zomato.com/careers"),
    ("Myntra", "https://careers.myntra.com/"),
    ("Zoho", "https://www.zoho.com/careers/"),
    ("Microsoft (India)", "https://jobs.careers.microsoft.com/global/en/search?lc=India"),
    ("HDFC Bank", "https://www.hdfcbank.com/personal/about-us/careers"),
    ("ICICI Bank", "https://www.icicicareers.com/"),
    ("Reliance Retail", "https://www.ril.com/careers"),
    ("Genpact", "https://www.genpact.com/careers"),
    ("Concentrix India", "https://www.concentrix.com/careers/"),
    ("Teleperformance India", "https://www.teleperformance.com/en-us/careers/"),
    ("Byju's", "https://byjus.com/careers/"),
    ("Ola", "https://www.olacabs.com/careers"),
    ("PhonePe", "https://www.phonepe.com/careers/"),
    ("Google (India)", "https://www.google.com/about/careers/applications/jobs/results/?location=India"),
    ("Apple (India)", "https://jobs.apple.com/en-in"),
    ("Salesforce (India)", "https://careers.salesforce.com/en/"),
    ("Oracle (India)", "https://www.oracle.com/careers/"),
    ("Barclays", "https://search.jobs.barclays/"),
    ("HSBC", "https://www.hsbc.com/careers"),
    ("Lloyds Banking Group", "https://www.lloydsbankinggroup.com/careers.html"),
    ("NatWest Group", "https://jobs.natwestgroup.com/"),
    ("Mastercard (UK)", "https://careers.mastercard.com/"),
    ("Amadeus", "https://amadeus.com/en/careers"),
    ("Softcat", "https://careers.softcat.com/"),
    ("Bloomberg (London)", "https://careers.bloomberg.com/"),
    ("Amazon (UK)", "https://www.amazon.jobs/en/locations/uk"),
    ("Google (UK)", "https://www.google.com/about/careers/applications/jobs/results/?location=United%20Kingdom"),
    ("Microsoft (UK)", "https://jobs.careers.microsoft.com/global/en/search?lc=United%20Kingdom"),
    ("Apple (UK)", "https://jobs.apple.com/en-gb"),
    ("Meta (UK)", "https://www.metacareers.com/locations/london"),
    ("Deloitte UK", "https://www2.deloitte.com/uk/en/careers.html"),
    ("PwC UK", "https://www.pwc.co.uk/careers.html"),
    ("EY UK", "https://www.ey.com/en_uk/careers"),
    ("KPMG UK", "https://home.kpmg/uk/en/home/careers.html"),
    ("Capgemini UK", "https://www.capgemini.com/gb-en/careers/"),
    ("IBM UK", "https://www.ibm.com/uk-en/employment"),
    ("BT Group", "https://www.bt.com/careers"),
    ("Vodafone UK", "https://careers.vodafone.com/"),
    ("Tesco", "https://www.tesco-careers.com/"),
    ("Sainsbury's", "https://www.sainsburys.jobs/"),
    ("Asda", "https://www.asda.jobs/"),
    ("Morrisons", "https://www.morrisons.jobs/"),
    ("Ocado", "https://www.ocadogroup.com/careers"),
    ("Experian", "https://www.experianplc.com/careers"),
    ("JPMorgan Chase (UK)", "https://careers.jpmorgan.com/"),
    ("Goldman Sachs (UK)", "https://www.goldmansachs.com/careers/"),
    ("BAE Systems", "https://www.baesystems.com/en/careers"),
    ("Rolls-Royce", "https://careers.rolls-royce.com/"),
    ("AstraZeneca", "https://careers.astrazeneca.com/"),
    ("GSK", "https://jobs.gsk.com/"),
    ("BT Openreach", "https://www.openreach.co.uk/careers"),
    ("Centrica / British Gas", "https://www.centrica.com/careers/"),
    ("National Grid", "https://www.nationalgrid.com/careers"),
    ("Marks & Spencer", "https://careers.marksandspencer.com/"),
    ("John Lewis Partnership", "https://www.jlpjobs.com/"),
    ("Capita", "https://careers.capita.com/"),
    ("Teleperformance UK", "https://www.teleperformance.com/en-us/careers/"),
    ("Salesforce (UK)", "https://careers.salesforce.com/en/"),
    ("Oracle (UK)", "https://www.oracle.com/careers/"),
    ("Inditex (Zara)", "https://www.inditexcareers.com/"),
    ("Santander", "https://www.santandercareers.com/"),
    ("BBVA", "https://www.bbva.com/en/careers/"),
    ("Telefonica", "https://www.telefonica.com/en/careers/"),
    ("Iberdrola", "https://www.iberdrola.com/careers"),
    ("CaixaBank", "https://www.caixabank.com/en/careers.html"),
    ("Repsol", "https://www.repsol.com/en/careers/"),
    ("Amadeus (Spain)", "https://amadeus.com/en/careers"),
    ("Indra", "https://www.indracompany.com/en/careers"),
    ("Mercadona", "https://empleo.mercadona.es/"),
    ("Grifols", "https://www.grifols.com/en/careers"),
    ("Deloitte Spain", "https://www2.deloitte.com/es/en/careers.html"),
    ("Capgemini Spain", "https://www.capgemini.com/es-en/careers/"),
    ("El Corte Ingles", "https://www.elcorteingles.es/empleo/"),
    ("Teleperformance Spain", "https://www.teleperformance.com/en-us/careers/"),
    ("PwC Spain", "https://www.pwc.es/en/careers.html"),
    ("EY Spain", "https://www.ey.com/es_es/careers"),
    ("KPMG Spain", "https://home.kpmg/es/en/home/careers.html"),
    ("Amazon (Spain)", "https://www.amazon.jobs/en/locations/spain"),
    ("Klarna", "https://www.klarna.com/careers/"),
    ("Ericsson", "https://www.ericsson.com/en/careers"),
    ("Volvo Group", "https://www.volvogroup.com/en/careers.html"),
    ("H&M Group", "https://hmgroup.com/careers/"),
    ("IKEA (Sweden)", "https://www.ikea.com/careers"),
    ("SEB", "https://sebgroup.com/careers"),
    ("Swedbank", "https://www.swedbank.com/about-swedbank/careers.html"),
    ("Nordea (Sweden)", "https://www.nordea.com/en/careers"),
    ("Sinch", "https://www.sinch.com/careers/"),
    ("King (Activision Blizzard)", "https://king.com/jobs"),
    ("ICA Gruppen", "https://www.icagruppen.se/en/career/"),
    ("Telia Company", "https://www.teliacompany.com/en/careers/"),
    ("Accenture Sweden", "https://accenture.wd103.myworkdayjobs.com/AccentureCareers"),
    ("Deloitte Sweden", "https://www2.deloitte.com/se/en/careers.html"),
    ("PwC Sweden", "https://www.pwc.se/en/careers.html"),
    ("EY Sweden", "https://www.ey.com/sv_se/careers"),
    ("KPMG Sweden", "https://home.kpmg/se/en/home/careers.html"),
    ("Amazon (Sweden)", "https://www.amazon.jobs/en/locations/sweden"),
    ("Qatar Airways", "https://careers.qatarairways.com/"),
    ("QNB Group", "https://www.qnb.com/sites/qnb/qnbcareers"),
    ("Ooredoo", "https://careers.ooredoo.qa/"),
    ("QatarEnergy", "https://qatarenergy.qa/en/Careers/"),
    ("Commercial Bank of Qatar", "https://www.cbq.qa/en/personal/pages/careers.aspx"),
    ("Doha Bank", "https://www.dohabank.com.qa/careers"),
    ("Vodafone Qatar", "https://careers.vodafone.com/"),
    ("Msheireb Properties", "https://www.msheireb.com/careers/"),
    ("Hamad International Airport (MATAR)", "https://www.dohahamadairport.com/corporate/careers"),
    ("LuLu Hypermarket Qatar", "https://www.luluhypermarket.com/en-qa/careers"),
    ("Accenture Qatar", "https://accenture.wd103.myworkdayjobs.com/AccentureCareers"),
    ("Deloitte Qatar", "https://www2.deloitte.com/qa/en/careers.html"),
    ("PwC Qatar", "https://www.pwc.com/m1/en/careers.html"),
    ("EY Qatar", "https://www.ey.com/en_qa/careers"),
    ("KPMG Qatar", "https://home.kpmg/qa/en/home/careers.html"),
    ("Shopify", "https://www.shopify.com/careers"),
    ("RBC (Royal Bank of Canada)", "https://jobs.rbc.com/"),
    ("TD Bank Group", "https://jobs.td.com/"),
    ("Scotiabank", "https://jobs.scotiabank.com/"),
    ("BMO Financial Group", "https://jobs.bmo.com/"),
    ("CIBC", "https://jobs.cibc.com/"),
    ("Manulife", "https://careers.manulife.com/"),
    ("Sun Life", "https://jobs.sunlife.com/"),
    ("Telus", "https://www.telus.com/en/careers"),
    ("Bell Canada", "https://jobs.bell.ca/"),
    ("Rogers Communications", "https://jobs.rogers.com/"),
    ("CGI Group", "https://www.cgi.com/en/careers"),
    ("Loblaw Companies", "https://www.loblaw.ca/en/careers.html"),
    ("Deloitte Canada", "https://www2.deloitte.com/ca/en/careers.html"),
    ("Amazon Canada", "https://www.amazon.jobs/en/locations/canada"),
    ("Wealthsimple", "https://www.wealthsimple.com/en-ca/careers"),
    ("Lightspeed Commerce", "https://www.lightspeedhq.com/careers/"),
    ("Air Canada", "https://careers.aircanada.com/"),
    ("Canadian Tire", "https://corp.canadiantire.ca/English/careers/default.aspx"),
    ("Metro Inc.", "https://carrieres.metro.ca/en"),
    ("CN Rail", "https://www.cn.ca/en/careers/"),
    ("Sobeys / Empire Company", "https://www.empireco.ca/careers/"),
    ("PwC Canada", "https://www.pwc.com/ca/en/careers.html"),
    ("EY Canada", "https://www.ey.com/en_ca/careers"),
    ("KPMG Canada", "https://home.kpmg/ca/en/home/careers.html"),
    ("IBM Canada", "https://www.ibm.com/ca-en/employment"),
    ("Google (Canada)", "https://www.google.com/about/careers/applications/jobs/results/?location=Canada"),
    ("Microsoft Canada", "https://jobs.careers.microsoft.com/global/en/search?lc=Canada"),
    ("Salesforce Canada", "https://careers.salesforce.com/en/"),
    ("Commonwealth Bank", "https://www.commbank.com.au/careers.html"),
    ("Westpac", "https://www.westpac.com.au/about-westpac/careers/"),
    ("NAB", "https://www.nab.com.au/about-us/careers"),
    ("ANZ Bank", "https://www.anz.com.au/about-us/careers/"),
    ("Telstra", "https://careers.telstra.com/"),
    ("Woolworths Group", "https://www.wowcareers.com.au/"),
    ("Coles Group", "https://www.colescareers.com.au/"),
    ("Atlassian", "https://www.atlassian.com/company/careers"),
    ("Qantas", "https://www.qantas.com/careers/"),
    ("BHP", "https://www.bhp.com/careers"),
    ("Wesfarmers", "https://www.wesfarmers.com.au/careers"),
    ("Deloitte Australia", "https://www2.deloitte.com/au/en/careers.html"),
    ("Amazon Australia", "https://www.amazon.jobs/en/locations/australia"),
    ("Rio Tinto", "https://www.riotinto.com/careers"),
    ("Bunnings (Wesfarmers)", "https://www.bunnings.com.au/careers"),
    ("Optus", "https://www.optus.com.au/about/careers"),
    ("Australia Post", "https://auspost.com.au/about-us/careers"),
    ("PwC Australia", "https://www.pwc.com.au/careers.html"),
    ("EY Australia", "https://www.ey.com/en_au/careers"),
    ("KPMG Australia", "https://home.kpmg/au/en/home/careers.html"),
    ("Google (Australia)", "https://www.google.com/about/careers/applications/jobs/results/?location=Australia"),
    ("Microsoft Australia", "https://jobs.careers.microsoft.com/global/en/search?lc=Australia"),
    ("Salesforce Australia", "https://careers.salesforce.com/en/"),
    ("DBS Bank", "https://www.dbs.com/careers/"),
    ("OCBC Bank", "https://www.ocbc.com/group/careers/"),
    ("UOB", "https://www.uobgroup.com/careers/"),
    ("Sea Limited (Shopee/Garena)", "https://www.sea.com/career"),
    ("Grab", "https://grab.careers/"),
    ("Singtel", "https://www.singtel.com/about-us/careers"),
    ("ByteDance / TikTok (APAC)", "https://careers.tiktok.com/"),
    ("Google (APAC HQ)", "https://www.google.com/about/careers/applications/jobs/results/?location=Singapore"),
    ("Microsoft (APAC HQ)", "https://jobs.careers.microsoft.com/global/en/search?lc=Singapore"),
    ("Goldman Sachs (Singapore)", "https://www.goldmansachs.com/careers/"),
    ("Barclays (Singapore)", "https://search.jobs.barclays/"),
    ("PropertyGuru", "https://www.propertygurugroup.com/careers/"),
    ("NTUC FairPrice", "https://careers.fairprice.com.sg/"),
    ("Deloitte Singapore", "https://www2.deloitte.com/sg/en/careers.html"),
    ("Apple (Singapore)", "https://jobs.apple.com/en-sg"),
    ("Meta (Singapore)", "https://www.metacareers.com/locations/singapore"),
    ("Amazon (Singapore)", "https://www.amazon.jobs/en/locations/singapore"),
    ("PwC Singapore", "https://www.pwc.com/sg/en/careers.html"),
    ("EY Singapore", "https://www.ey.com/en_sg/careers"),
    ("KPMG Singapore", "https://home.kpmg/sg/en/home/careers.html"),
    ("Salesforce Singapore", "https://careers.salesforce.com/en/"),
    ("Xero", "https://www.xero.com/careers/"),
    ("Fisher & Paykel Healthcare", "https://careers.fphcare.com/"),
    ("Air New Zealand", "https://careers.airnewzealand.co.nz/"),
    ("ANZ New Zealand", "https://www.anz.co.nz/about-us/careers/"),
    ("ASB Bank", "https://careers.asb.co.nz/"),
    ("Spark New Zealand", "https://careers.sparknz.co.nz/"),
    ("Trade Me", "https://www.trademe.co.nz/careers"),
    ("Datacom", "https://careers.datacom.com/"),
    ("Fonterra", "https://www.fonterra.com/careers"),
    ("Foodstuffs NZ", "https://careers.foodstuffs.co.nz/"),
    ("Countdown/Woolworths NZ", "https://careers.woolworths.co.nz/"),
    ("Accenture New Zealand", "https://accenture.wd103.myworkdayjobs.com/AccentureCareers"),
    ("Deloitte New Zealand", "https://www2.deloitte.com/nz/en/careers.html"),
    ("PwC New Zealand", "https://www.pwc.co.nz/careers.html"),
    ("EY New Zealand", "https://www.ey.com/en_nz/careers"),
    ("KPMG New Zealand", "https://home.kpmg/nz/en/home/careers.html"),
    ("Automattic (WordPress.com)", "https://automattic.com/work-with-us/"),
    ("Toptal", "https://www.toptal.com/careers"),
    ("Doist", "https://doist.com/careers"),
]

# ---------------------------------------------------------------------------
# Ireland company registry
#
# This is separate from the ATS connector lists. Every employer in this
# registry remains visible even when its ATS returns zero jobs or errors.
# Registry expanded with the uploaded 100-company Ireland career-page list.
# ireland_companies.csv is the runtime source of truth; this embedded list is the fallback.

# This gives the dashboard the same "live matches + manual-check companies"
# behaviour as the reference Job Radar.
# ---------------------------------------------------------------------------

IRELAND_COMPANY_REGISTRY = [
    'A&L Goodbody',
    'ABB',
    'Abbott',
    'AbbVie',
    'ABP Food Group',
    'Accenture',
    'Adecco Ireland',
    'Adobe',
    'Advanced Micro Devices (AMD)',
    'AECOM',
    'Aer Lingus',
    'AerCap',
    'Agilent Technologies',
    'AIB (Allied Irish Banks)',
    'Akamai',
    'Aldi Ireland',
    'Alexion Pharmaceuticals',
    'Alkermes',
    'Alvarez & Marsal',
    'Amazon',
    'American Express',
    'Amgen',
    'An Post',
    'Analog Devices',
    'Aon',
    'Apple',
    'Applied Materials',
    'Approach People Recruitment',
    'Arcadis',
    'Arista Networks',
    'Arthur Cox',
    'Arup',
    'Asana',
    'ASML',
    'AstraZeneca',
    'AtkinsRéalis',
    'Atlantic Technological University (ATU)',
    'Atlassian',
    'Autodesk',
    'Aviva Ireland',
    'Avolon',
    'AXA Ireland',
    'B&Q Ireland',
    'Bain & Company',
    'Baker Tilly Ireland',
    'BAM Ireland',
    'Bank of America',
    'Bank of Ireland',
    'Barclays',
    'Bausch + Lomb',
    'Baxter International',
    'Bayer',
    'BDO Ireland',
    'BearingPoint',
    'Becton Dickinson (BD)',
    'Bio-Rad Laboratories',
    'Biotronik',
    'BlackRock',
    'Bloomberg',
    'BNP Paribas Ireland',
    'BNY',
    'BNY Mellon',
    'Boehringer Ingelheim',
    'Boots Ireland',
    'Bord Gáis Energy',
    'Bord na Móna',
    'Boston Consulting Group (BCG)',
    'Boston Scientific',
    'Box',
    'Brightwater',
    'Bristol Myers Squibb',
    'Broadcom',
    'Brown Thomas Arnotts',
    'Bruker',
    'Bus Éireann',
    'ByrneWallace',
    'C&C Group',
    'Cadence Design Systems',
    'Cairn Homes',
    'Cantor Fitzgerald Ireland',
    'Canva',
    'Capgemini',
    'Carbery Group',
    'Carrier',
    'Catalent',
    'CDB Aviation',
    'Central Bank of Ireland',
    'CGI',
    'Charles River Laboratories',
    'Check Point Software',
    'Cisco',
    'Citi',
    'Citrix',
    'Clayton Hotels',
    'ClickUp',
    'Cloudflare',
    'Coca-Cola HBC Ireland',
    'Cognizant',
    'Cohesity',
    'Coillte',
    'Coinbase',
    'Coloplast',
    'Concentrix (Ireland)',
    'Convatec',
    'Cook Medical',
    'Cpl',
    'CPL Resources',
    'CRH',
    'CrowdStrike',
    'Currys Ireland',
    'CyberArk',
    'daa (Dublin Airport Authority)',
    'DAE Capital',
    'Dairygold',
    'Dalata Hotel Group',
    'Danaher Corporation',
    'Databricks',
    'Datadog',
    'Datalex',
    'Davy',
    'Dawn Meats',
    'Decathlon Ireland',
    'Dell Technologies',
    'Deloitte Ireland',
    'DePuy Synthes',
    'Deutsche Bank',
    'Dexcom',
    'DHL Ireland',
    'Diageo Ireland',
    'Dillon Eustace',
    'DocuSign',
    'DPS Group (Arcadis)',
    'DraftKings',
    'Dropbox',
    'DSV Ireland',
    'Dublin Bus',
    'Dublin City University (DCU)',
    'Dunnes Stores',
    'DXC Technology',
    'Dynatrace',
    'Eason',
    'Eaton',
    'Edwards Lifesciences',
    'Eir',
    'EirGrid',
    'EirGrid Group',
    'Elavon',
    'Eli Lilly',
    'Emerson',
    'Energia Group',
    'Enterprise Ireland',
    'Ergo',
    'Ericsson',
    'ESB',
    'ESB (Electricity Supply Board)',
    'Etsy',
    'Eurofins Scientific',
    'Eversheds Sutherland Ireland',
    'EY Ireland',
    'FactSet',
    'Fastly',
    'Fastway Couriers Ireland',
    'FBD Insurance',
    'FedEx Express Ireland',
    'Fenergo',
    'Fidelity Investments',
    'Figma',
    'Fiserv',
    'Fitch Ratings',
    'Flutter Entertainment',
    'Fortinet',
    'Forvis Mazars Ireland',
    'FRS Recruitment',
    'FTI Consulting',
    'Fujitsu',
    'Fáilte Ireland',
    'Gartner',
    'Gas Networks Ireland',
    'Genesis (formerly GECAS)',
    'Genesys',
    'Gilead Sciences',
    'Glanbia',
    'Glanbia / Tirlán',
    'GlaxoSmithKline (GSK)',
    'Glenveagh Properties',
    'Goldman Sachs',
    'Goodbody',
    'Google',
    'Grant Thornton Ireland',
    'Greencore',
    'Guidewire',
    'H&M Ireland',
    'Haleon',
    'Halfords Ireland',
    'Harvey Nash Ireland',
    'Hays Ireland',
    'Heineken Ireland',
    'Hewlett Packard Enterprise (HPE)',
    'HIQA',
    'Holland & Barrett Ireland',
    'Hollister Incorporated',
    'Honeywell',
    'Horizon Therapeutics (Amgen)',
    'HP (Hewlett-Packard)',
    'HSBC Ireland',
    'HSE (Health Service Executive)',
    'HubSpot',
    'IBM',
    'ICON plc',
    'IDA Ireland',
    'Illumina',
    'Indeed',
    'Indeed (Ireland)',
    'Infineon Technologies',
    'Infosys',
    'Insulet Corporation',
    'Integra LifeSciences',
    'Intel',
    'Intercom',
    'Intersport Elverys',
    'IQVIA',
    'Irish Distillers (Pernod Ricard)',
    'Irish Ferries',
    'Irish Life',
    'Irish Rail (Iarnród Éireann)',
    'Jacobs',
    'Jamf',
    'Jazz Pharmaceuticals',
    'JD Sports Ireland',
    'John Sisk & Son (Sisk Group)',
    'Johnson & Johnson',
    'Johnson Controls',
    'Jones Engineering',
    'JPMorgan Chase',
    'Kepak Group',
    'Kerry Group',
    'Keysight Technologies',
    'Kingspan Group',
    'Kirby Group Engineering',
    'KLA Corporation',
    'KPMG Ireland',
    'Kuehne+Nagel Ireland',
    'Labcorp',
    'Lam Research',
    'Laya Healthcare',
    'Lidl Ireland',
    'Life Style Sports',
    'Linesight',
    'LinkedIn',
    'LK Shields',
    'LloydsPharmacy Ireland',
    'Logitech',
    'Lonza',
    'Macquarie Group',
    'Maldron Hotels',
    'Manpower Ireland',
    'Maples Group Ireland',
    'Marks & Spencer Ireland',
    'Marsh McLennan',
    'Marvell Technology',
    'Mason Hayes & Curran',
    'Mastercard',
    'Matheson',
    'Maynooth University',
    'McCann FitzGerald',
    'McKinsey & Company',
    'Mediahuis Ireland',
    'Medpace',
    'Medtronic',
    'Mercer',
    'Merck Group',
    'Mercury Engineering',
    'Merit Medical',
    'Meta',
    'Microchip Technology',
    'Micron Technology',
    'Microsoft',
    'Microsoft Dynamics Partners',
    'Monday.com',
    'MongoDB',
    "Moody's",
    'Morgan McKinley',
    'Morgan Stanley',
    'Morningstar',
    'Mott MacDonald',
    'MSCI',
    'MSD (Merck Sharp & Dohme)',
    'Munster Technological University (MTU)',
    'Musgrave Group (SuperValu / Centra)',
    'NetApp',
    'Next Ireland',
    'Nokia',
    'Nordic Aviation Capital',
    'Northern Trust',
    'Notion',
    'Novartis',
    'NTMA',
    'Nutanix',
    'NVIDIA',
    'NXP Semiconductors',
    'Okta',
    'Oliver Wyman',
    'Oracle',
    'Ornua',
    'Palo Alto Networks',
    'PayPal',
    'Personio',
    'Pfizer',
    'Philip Lee',
    'Ping Identity',
    'Pinterest',
    'PM Group',
    'Press Up Hospitality Group',
    'Primark / Penneys',
    'Proofpoint',
    'Protiviti',
    'PTSB (Permanent TSB)',
    'Public Jobs / Civil Service',
    'PublicJobs.ie (PAS)',
    'Pure Storage',
    'PwC Ireland',
    'QIAGEN',
    'Qorvo',
    'Qualcomm',
    'Qualtrics',
    'Rapid7',
    'Reddit',
    'Refinitiv (LSEG)',
    'Regeneron',
    'Renesas Electronics',
    'Reperio Human Capital',
    'ResMed',
    'Revenue',
    'Revvity (PerkinElmer)',
    'Riot Games',
    'Roche',
    'Rockwell Automation',
    'RTÉ (Raidió Teilifís Éireann)',
    'Rubrik',
    'Ryanair',
    'S&P Global',
    'Sage',
    'Salesforce',
    'Sanofi',
    'SAP',
    'Schneider Electric',
    'Science Foundation Ireland (SFI)',
    'Seagate',
    'SentinelOne',
    'ServiceNow',
    'Shannon Airport Group',
    'Sigmar Recruitment',
    'Sky Ireland',
    'Slack',
    'Slalom',
    'SMBC Aviation Capital',
    'Smith & Nephew',
    'Smurfit Kappa',
    'Smurfit Westrock',
    'Smyths Toys Superstores',
    'Snowflake',
    'Societe Generale',
    'Sophos',
    'South East Technological University (SETU)',
    'Splunk',
    'Squarespace',
    'SSE Airtricity / SSE',
    'Stantec',
    'State Street',
    'Stena Line Ireland',
    'STMicroelectronics',
    'Storm3',
    'Stripe',
    'Stryker',
    'Superdrug Ireland',
    'SuperValu / Musgrave',
    'Susquehanna International Group (SIG)',
    'Syneos Health',
    'Synopsys',
    'Takeda',
    'Tandem Diabetes Care',
    'Tata Consultancy Services (TCS)',
    'Teagasc',
    'Technological University Dublin (TU Dublin)',
    'Teleflex',
    'Teleperformance (Ireland)',
    'Tenable',
    'Terumo',
    'Tesco Ireland',
    'Tetra Tech',
    'Teva Pharmaceuticals',
    'Texas Instruments',
    'The Doyle Collection',
    'The Irish Times',
    'Thermo Fisher Scientific',
    'Three Ireland',
    'TikTok',
    'TK Maxx Ireland',
    'Toast',
    'Tourism Ireland',
    'Trane Technologies',
    'Transport Infrastructure Ireland',
    'Trend Micro',
    'Trinity College Dublin (TCD)',
    'Twilio',
    'UBS',
    'Uisce Éireann (Irish Water)',
    'Uisce Éireann / Irish Water',
    'Uniphar Group',
    'University College Cork (UCC)',
    'University College Dublin (UCD)',
    'University of Galway',
    'University of Limerick (UL)',
    'UPS Ireland',
    'Veeam',
    'Version 1',
    'VHI Healthcare',
    'Viatris',
    'Virgin Media Ireland',
    'Visa',
    'VMware (Broadcom)',
    'Vodafone Ireland',
    'Walkers Ireland',
    'Waters Corporation',
    'Waterstones Ireland',
    'Wayflyer',
    'Western Digital',
    'William Fry',
    'Willis Towers Watson (WTW)',
    'Wipro',
    "Woodie's",
    'Workday',
    'Workhuman',
    'Workvivo',
    'WSP',
    'WTW',
    'WuXi Biologics',
    'Zara / Inditex Ireland',
    'Zendesk',
    'Zimmer Biomet',
    'Zscaler',
    'Zurich Insurance',
]

CAREERS_URL_OVERRIDES = {
    "Apple": "https://jobs.apple.com/en-ie/search",
    "EY Ireland": "https://careers.ey.com/ey",
}

def _company_key(value: str) -> str:
    value = (value or "").lower().replace("&", "and")
    return re.sub(r"[^a-z0-9]+", "", value)

def _registry_url_map():
    out = {}
    for company, url in JSONLD_CAREER_PAGES:
        key = _company_key(company)
        if key:
            out[key] = url
    for company, url in CAREERS_URL_OVERRIDES.items():
        out[_company_key(company)] = url
    return out

def _load_company_master():
    """Load the Ireland master registry. CSV is intentionally editable without touching Python."""
    try:
        import csv
        with open("ireland_companies.csv", encoding="utf-8-sig", newline="") as f:
            rows = list(csv.DictReader(f))
        if rows:
            return [
                (
                    (r.get("company_name") or "").strip(),
                    (r.get("career_url") or "").strip(),
                    (r.get("source_type") or "employer").strip() or "employer",
                    (r.get("category") or "").strip(),
                )
                for r in rows
            ]
    except Exception as exc:
        print(f"  ! ireland_companies.csv unavailable, using embedded registry: {exc}")
    return [(name, None, "employer", "") for name in IRELAND_COMPANY_REGISTRY]

def build_company_registry(include_cache: bool = False):
    url_map = _registry_url_map()
    connector_maps = [
        ({_company_key(x): "greenhouse" for x in GREENHOUSE_COMPANIES}),
        ({_company_key(x): "lever" for x in LEVER_COMPANIES}),
        ({_company_key(x): "ashby" for x in ASHBY_COMPANIES}),
        ({_company_key(x[0]): "workday" for x in WORKDAY_COMPANIES}),
        ({_company_key(x): "smartrecruiters" for x in SMARTRECRUITERS_COMPANIES}),
        ({_company_key(x): "workable" for x in WORKABLE_COMPANIES}),
        ({_company_key(x): "recruitee" for x in RECRUITEE_COMPANIES}),
        ({_company_key(x): "personio" for x in PERSONIO_COMPANIES}),
        ({_company_key(x): "pinpoint" for x in PINPOINT_COMPANIES}),
        ({_company_key(x): "direct" for x in DIRECT_COMPANY_CONNECTORS}),
        ({_company_key(x): "phenom" for x in KNOWN_PHENOM_MAPPINGS}),
        ({_company_key(x): "eightfold" for x in KNOWN_EIGHTFOLD_MAPPINGS}),
    ]
    status_by_key = {}
    for mapping in connector_maps:
        status_by_key.update(mapping)

    # Confirmed dynamic ATS mappings discovered in previous runs. Hard-coded
    # mappings remain authoritative; cache only fills companies that otherwise
    # would be manual-check.
    if include_cache:
        try:
            with open("ats_platform_cache.json", encoding="utf-8") as f:
                ats_cache = json.load(f)
            for company_name, info in ats_cache.items():
                if company_name.startswith("__") or not isinstance(info, dict):
                    continue
                platform = info.get("platform")
                key = _company_key(company_name)
                if platform and platform != "none" and key not in status_by_key:
                    status_by_key[key] = platform
        except Exception:
            pass

    registry = []
    for name, master_url, source_type, category in _load_company_master():
        if not name:
            continue
        key = _company_key(name)
        platform = status_by_key.get(key, "manual-check")
        url = CAREERS_URL_OVERRIDES.get(name) or master_url or url_map.get(key)

        # IMPORTANT: do not use substring matching here.
        # "Ergo" must not inherit Fenergo's connector, "Eir" must not inherit
        # another company containing "eir", etc. Dynamic ATS discovery below
        # validates real career-page/ATS endpoints instead.
        registry.append({
            "company": name,
            "country": "Ireland",
            "platform": platform,
            "careers_url": url,
            "automatic": platform != "manual-check",
            "source_type": source_type,
            "category": category,
        })
    return registry

def company_display_name(raw: str) -> str:
    key = _company_key(raw)
    for name in IRELAND_COMPANY_REGISTRY:
        if _company_key(name) == key:
            return name
    aliases = {
        "nvidia": "NVIDIA",
        "docusign": "DocuSign",
        "microsoft": "Microsoft",
        "linkedin": "LinkedIn",
        "meta": "Meta",
        "google": "Google",
        "apple": "Apple",
        "ey": "EY Ireland",
        "kpmg": "KPMG Ireland",
        "aib": "AIB (Allied Irish Banks)",
    }
    return aliases.get(key, raw)


# ---------------------------------------------------------------------------
# External job aggregator APIs -- optional, free, but need YOUR OWN key
# (I can't sign up on your behalf). These cover the "other well-known job
# posting websites" ground -- Indeed and LinkedIn don't offer free public
# search APIs anymore (Indeed closed its Publisher program to new
# applicants; LinkedIn requires a partnership), and scraping their HTML
# directly violates their terms of service and is aggressively bot-blocked,
# so they're not legitimate free options. These three are the real
# free equivalent: documented APIs, free tiers, no ToS violation.
#
# Important honest caveat from earlier: these aggregators crawl the same
# primary ATS sources this scraper already hits, just later -- they add
# BREADTH (companies/regions we don't otherwise cover), not SPEED. Left
# empty/inactive by default; each function is a no-op until you fill in a key.
#
#   Adzuna:    developer.adzuna.com            -- ADZUNA_APP_ID / ADZUNA_APP_KEY
#   Careerjet: careerjet.com/partners           -- CAREERJET_AFFID
#   Jooble:    jooble.org/api/about             -- JOOBLE_API_KEY
# ---------------------------------------------------------------------------

ADZUNA_APP_ID = os.environ.get("ADZUNA_APP_ID", "").strip()
ADZUNA_APP_KEY = os.environ.get("ADZUNA_APP_KEY", "").strip()

# Careerjet's API calls this value "affid". Keep both environment names for compatibility.
CAREERJET_AFFID = (
    os.environ.get("CAREERJET_API_KEY", "").strip()
    or os.environ.get("CAREERJET_AFFID", "").strip()
)

JOOBLE_API_KEY = os.environ.get("JOOBLE_API_KEY", "").strip()

# ---------------------------------------------------------------------------
# Direct-from-company-site sources, attempted with plain HTTP (no proxy).
# These use each company's own internal search API -- the same ones the
# Apify FAANG actor calls. GitHub Actions runners have full outbound internet
# access (unlike a restricted sandbox), so plain requests may well succeed
# here even though they failed when tested from a locked-down environment.
#
# Amazon and Netflix have simple, well-documented JSON search APIs and are
# implemented below. Google, Apple and Meta use heavier client-side
# rendering / GraphQL / session-signed requests that are genuinely fragile
# to reverse-engineer -- they are intentionally NOT attempted here. Keep
# pulling those three from the Apify FAANG actor (still free) rather than
# risk silently-wrong or empty data from a guessed integration.
# ---------------------------------------------------------------------------


# Direct company career-site connectors. These are intentionally separate from
# ATS discovery because the sites use proprietary/public search surfaces rather
# than a reusable third-party ATS board. A connector is allowed to return zero
# without failing the whole run; the dashboard then exposes it under
# "Zero jobs scraped" for diagnosis.
DIRECT_COMPANY_CONNECTORS = {
    "Apple": "apple",
    "Google": "google",
    "Microsoft": "microsoft",
    "Meta": "meta",
    "TikTok": "tiktok",
    "Oracle": "oracle",
    "Amazon": "amazon",
    "Netflix": "netflix",
}

# Exact enterprise-platform mappings learned from validated public career-site
# hosts. Unlike guessed ATS slugs, these are revalidated at runtime before use.
KNOWN_EIGHTFOLD_MAPPINGS = {
    "NetApp": "netapp",
    "STMicroelectronics": "stmicroelectronics",
    "Bayer": "bayer",
    "HSBC Ireland": "hsbc",
}

KNOWN_PHENOM_MAPPINGS = {
    "Cisco": "careers.cisco.com|CISCISGLOBAL",
    "Fiserv": "careers.fiserv.com|FFFYJUS",
    "Roche": "careers.roche.com|ROCHGLOBAL",
    "Merck Group": "jobs.merck.com|MERCUS",
    "Zimmer Biomet": "careers.zimmerbiomet.com|ZBUZBRUS",
    "Convatec": "careers.convatec.com|CONVGLOBAL",
    "Labcorp": "careers.labcorp.com|COVAGLOBAL",
    "Danaher Corporation": "jobs.danaher.com|DANAGLOBAL",
    "Catalent": "careers.catalent.com|CATAUS",
    "Kerry Group": "jobs.kerry.com|KGUKGRGLOBAL",
    "DHL Ireland": "careers.dhl.com|DPDHGLOBAL",
    "Kuehne+Nagel Ireland": "jobs.kuehne-nagel.com|KUNAGLOBAL",
    "State Street": "careers.statestreet.com|STSTGLOBAL",
    "Thermo Fisher Scientific": "jobs.thermofisher.com|TFSCGLOBAL",
}

DIRECT_QUERIES = [""]  # general search engine: retrieve all jobs; filter in the dashboard

# ---------------------------------------------------------------------------
# Role keyword filter (title must contain at least one of these)
# ---------------------------------------------------------------------------

TITLE_KEYWORDS = [
    "data analyst", "data scientist", "business intelligence",
    "business analyst", "consultant", "erp", "retail sales",
    "customer service", "store assistant",
    # Part-time / internship track, matching the Part Time CV's 3 target
    # categories (retail sales / customer service / store & stock assistant,
    # already covered above) plus general part-time and internship phrasing
    # so genuinely part-time or intern postings get caught even when the
    # title doesn't literally say "retail" or "customer service".
    "intern", "internship", "working student", "student job", "placement",
    "part time", "part-time", "sales assistant", "stock assistant",
    "seasonal", "temporary staff", "christmas temp", "weekend staff",
]

# Used to tag each matched job's employment_type after scraping (see main()).
# Order matters: internship is checked before part-time so "part-time
# internship" style titles land as "internship".
INTERNSHIP_KEYWORDS = ["intern", "internship", "working student", "student job", "placement", "co-op", "co op"]
PART_TIME_KEYWORDS = ["part time", "part-time", "seasonal", "temporary staff", "christmas temp", "weekend staff"]


def employment_type(title: str) -> str:
    t = (title or "").lower()
    if any(k in t for k in INTERNSHIP_KEYWORDS):
        return "internship"
    if any(k in t for k in PART_TIME_KEYWORDS):
        return "part_time"
    return "full_time"


# ---------------------------------------------------------------------------
# Location filter — Ireland-only pipeline (roles in IE or IE-remote/hybrid).
# ---------------------------------------------------------------------------

IRELAND_ONLY = True

IRELAND_LOCATION_KEYWORDS = [
    "ireland", "éire", "eire", "dublin", "cork", "galway", "limerick",
    "waterford", "kildare", "kilkenny", "wexford", "sligo", "mayo",
    "donegal", "kerry", "tipperary", "meath", "louth", "wicklow", "carlow",
    "laois", "offaly", "westmeath", "longford", "roscommon", "cavan",
    "monaghan", "clare", "ennis", "shannon", "athlone", "dundalk", "bray",
    "naas", "tralee", "letterkenny", "drogheda", "swords", "blanchardstown",
    "dún laoghaire", "dun laoghaire", "tallaght", "cork city", "dublin city",
    "irL",  # typo guard — removed below via normalized check
]
# Drop accidental typo token
IRELAND_LOCATION_KEYWORDS = [k for k in IRELAND_LOCATION_KEYWORDS if k != "irL"]

IRELAND_REMOTE_HINTS = [
    "remote, ireland", "remote ireland", "ireland remote", "remote (ireland)",
    "remote - ireland", "remote/hybrid ireland", "hybrid ireland",
    "ireland (remote", "ireland - remote", "based in ireland",
]

# Canonical county/city bucket for the dashboard location filter.
IRELAND_AREA_KEYWORDS = [
    ("dublin", "Dublin"),
    ("cork", "Cork"),
    ("galway", "Galway"),
    ("limerick", "Limerick"),
    ("waterford", "Waterford"),
    ("kildare", "Kildare"),
    ("remote", "Remote / Hybrid"),
    ("hybrid", "Remote / Hybrid"),
]

_REGION_TAG_RE = re.compile(r"\(([^)]+)\)")

IRISH_DOMESTIC_CAREER_PAGES = {
    "aib", "an post", "ryanair", "aer lingus", "eir", "version 1",
    "dunnes stores", "supervalu / musgrave", "musgrave",
    "penneys / primark ireland", "bank of ireland", "ibm ireland", "sap ireland",
}

VISA_SPONSOR_KEYWORDS = [
    "visa sponsorship", "sponsor visa", "will sponsor", "sponsorship available",
    "employment permit", "work permit sponsorship", "stamp 1g", "stamp 1",
]
VISA_NO_SPONSOR_KEYWORDS = [
    "no visa sponsorship", "no sponsorship", "unable to sponsor",
    "will not sponsor", "cannot sponsor", "without sponsorship",
    "must have the right to work", "right to work in ireland without restriction",
    "eligible to work in ireland without",
]

ADZUNA_COUNTRIES = ["ie"] if IRELAND_ONLY else ["gb", "ie", "de", "nl", "at", "es", "pl", "in", "sg", "au", "nz", "ca"]
CAREERJET_LOCALES = ["en_IE"] if IRELAND_ONLY else ["en_GB", "en_IE", "en_US", "en_AU", "en_CA", "en_SG", "en_IN"]

# ---------------------------------------------------------------------------
# Recency filter. Aggregators (Adzuna/Careerjet/Jooble) mostly buy you
# breadth, not speed -- they crawl the same primary ATS sources we do, just
# later. The actual lever for "earliest" is how often THIS scrapes (see
# scrape.yml's cron) plus being able to see, at a glance, how fresh each
# listing is. MAX_AGE_DAYS optionally drops stale postings entirely at
# scrape time; set to None to keep everything and just rely on the
# recency tag + dashboard filter instead.
# ---------------------------------------------------------------------------

MAX_AGE_DAYS = None  # e.g. 30 to auto-drop postings older than a month; None = keep all


def parse_posted_date(value):
    """Best-effort parse of a posting date/recency string into a UTC datetime.
    Handles ISO8601 (Greenhouse/Lever/Ashby/SmartRecruiters/Workable/Recruitee/
    Personio/Amazon/Netflix all return this) and Workday's human-readable
    relative strings ("Posted Today", "Posted 3 Days Ago", "Posted 30+ Days Ago").
    """
    if not value:
        return None
    s = str(value).strip()

    try:
        iso = s.replace("Z", "+00:00")
        dt = datetime.fromisoformat(iso)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except ValueError:
        pass

    sl = s.lower()
    now = datetime.now(timezone.utc)
    if "today" in sl:
        return now
    if "yesterday" in sl:
        return now - timedelta(days=1)
    m = re.search(r"(\d+)\+?\s*day", sl)
    if m:
        return now - timedelta(days=int(m.group(1)))
    return None


def recency_bucket(posted_dt):
    if not posted_dt:
        return "unknown"
    age = datetime.now(timezone.utc) - posted_dt
    if age <= timedelta(hours=24):
        return "24h"
    if age <= timedelta(days=7):
        return "7d"
    if age <= timedelta(days=30):
        return "30d"
    return "older"


def title_matches(title: str) -> bool:
    """Preference tag only. Never use this to decide whether a job is ingested."""
    t = (title or "").lower()
    return any(k in t for k in TITLE_KEYWORDS)


def _strip_html(text: str) -> str:
    if not text:
        return ""
    return re.sub(r"<[^>]+>", " ", str(text))


def ireland_area(location: str) -> str:
    loc = (location or "").lower()
    for keyword, label in IRELAND_AREA_KEYWORDS:
        if keyword in loc:
            return label
    if any(k in loc for k in IRELAND_LOCATION_KEYWORDS):
        return "Ireland (other)"
    return "Ireland (other)"


def visa_sponsorship_from_text(*parts: str) -> str:
    text = " ".join(_strip_html(p) for p in parts if p).lower()
    if not text.strip():
        return "not_mentioned"
    if any(k in text for k in VISA_NO_SPONSOR_KEYWORDS):
        return "no_sponsorship"
    if any(k in text for k in VISA_SPONSOR_KEYWORDS):
        return "sponsors"
    return "not_mentioned"


def jsonld_page_is_ireland(company: str, url: str) -> bool:
    """Keep JSON-LD career pages that target Ireland (skip other regions)."""
    u = (url or "").lower()
    c = (company or "").lower()
    if ".ie/" in u or "/ie/" in u or "en-ie" in u or "en_ie" in u:
        return True
    if "bankofireland" in u or "dublin-ireland" in u:
        return True
    if " ireland" in c or c.endswith(" ireland"):
        return True
    tags = [t.lower() for t in _REGION_TAG_RE.findall(company or "")]
    if tags:
        return any("ireland" in t for t in tags)
    if c in IRISH_DOMESTIC_CAREER_PAGES:
        return True
    return False


def region_ok(location: str) -> bool:
    loc = (location or "").lower()
    if IRELAND_ONLY:
        if any(h in loc for h in IRELAND_REMOTE_HINTS):
            return True
        if any(k in loc for k in IRELAND_LOCATION_KEYWORDS):
            return True
        if "remote" in loc or "hybrid" in loc:
            # Generic remote with no country — too broad for an Ireland-only board.
            return False
        return False

    # Legacy multi-region mode (set IRELAND_ONLY = False to re-enable).
    REGION_KEYWORDS = [
        "ireland", "dublin", "cork", "uk", "united kingdom", "london", "europe",
        "eu", "germany", "berlin", "france", "paris", "netherlands", "amsterdam",
        "spain", "madrid", "barcelona", "italy", "milan", "sweden", "stockholm",
        "denmark", "copenhagen", "finland", "helsinki", "norway", "oslo",
        "poland", "warsaw", "portugal", "lisbon", "belgium", "brussels",
        "austria", "vienna", "switzerland", "zurich", "singapore", "dubai",
        "uae", "united arab emirates", "india", "bangalore", "bengaluru",
        "mumbai", "delhi", "hyderabad", "pune", "chennai", "gurgaon", "gurugram",
        "australia", "sydney", "melbourne", "brisbane", "nsw", "queensland",
        "victoria", "new zealand", "auckland", "wellington", "nz",
        "saudi arabia", "riyadh", "jeddah", "qatar", "doha",
    ]
    US_KEYWORDS = ["usa", "united states", "u.s.a", "u.s."]
    if any(k in loc for k in REGION_KEYWORDS):
        return True
    if any(k in loc for k in US_KEYWORDS):
        return "remote" in loc
    if "remote" in loc:
        return True
    return False


# ---------------------------------------------------------------------------
# Sector + country tagging. SECTOR_BY_COMPANY is built from the 'Sector'
# column of company_shortlist_by_region.xlsx (704 companies) so the dashboard
# can filter by industry. Keys are lowercase company names as they appear in
# that spreadsheet -- JSON-LD entries carry a '(Region)' suffix (e.g.
# 'google (ireland)') which matches the ATS-scraper 'company' field for those
# rows exactly; bare-slug entries (greenhouse/lever/ashby/etc., e.g. 'stripe')
# match directly too. sector_for() falls back to stripping any '(...)' suffix
# so a company can still resolve even if the two names drift slightly.
# ---------------------------------------------------------------------------

SECTOR_BY_COMPANY = {
    "a1 telekom austria": "Telecom",
    "ab inbev": "Consumer",
    "abn amro": "Bank",
    "accenture (india)": "Consulting",
    "accenture australia": "Consulting",
    "accenture austria": "Consulting",
    "accenture belgium": "Consulting",
    "accenture canada": "Consulting",
    "accenture finland": "Consulting",
    "accenture germany": "Consulting",
    "accenture hong kong": "Consulting",
    "accenture ireland": "Consulting",
    "accenture malaysia": "Consulting/GBS",
    "accenture netherlands": "Consulting",
    "accenture new zealand": "Consulting",
    "accenture poland": "Consulting/GBS",
    "accenture portugal": "Consulting/GBS",
    "accenture qatar": "Consulting",
    "accenture saudi arabia": "Consulting",
    "accenture singapore": "Consulting",
    "accenture spain": "Consulting",
    "accenture sweden": "Consulting",
    "accenture uae": "Consulting",
    "accenture uk": "Consulting",
    "acs group": "Construction",
    "adani group": "Conglomerate",
    "adidas": "Sports Apparel",
    "adnoc": "Energy",
    "adyen": "Fintech",
    "aegon": "Insurance",
    "aeon malaysia": "Retail",
    "aer lingus": "Airline",
    "ahold delhaize": "Retail",
    "aia group": "Insurance",
    "aia malaysia": "Insurance",
    "aib": "Bank",
    "air canada": "Airline",
    "air india": "Airline",
    "air new zealand": "Airline",
    "airasia": "Airline",
    "airwallex": "Fintech",
    "al meera": "Retail",
    "al othaim": "Retail",
    "al rajhi bank": "Bank",
    "aldar properties": "Real Estate",
    "aldi": "Retail",
    "aldi ireland": "Retail",
    "allegro": "E-commerce",
    "allianz": "Insurance",
    "almarai": "Consumer/FMCG",
    "amadeus": "Travel Tech",
    "amadeus (spain)": "Travel Tech",
    "amazon (germany)": "Tech/Retail/Logistics",
    "amazon (hong kong)": "Tech/Retail",
    "amazon (india)": "Tech/Retail",
    "amazon (ireland)": "Tech/Retail",
    "amazon (saudi arabia)": "Tech/AWS",
    "amazon (singapore)": "Tech/Retail",
    "amazon (spain)": "Tech/Retail/Logistics",
    "amazon (sweden)": "Tech/Retail",
    "amazon (uk)": "Tech/Retail",
    "amazon australia": "Tech/Retail",
    "amazon canada": "Tech/Retail",
    "amazon poland": "Tech/Retail/Logistics",
    "amazon uae": "Tech/Retail",
    "an post": "Postal/Semi-state",
    "andritz": "Industrial/Engineering",
    "anz bank": "Bank",
    "anz new zealand": "Bank",
    "apple (germany)": "Tech",
    "apple (india)": "Tech",
    "apple (ireland)": "Tech",
    "apple (singapore)": "Tech",
    "apple (uk)": "Tech",
    "applegreen": "Retail/Convenience",
    "articulate": "Tech",
    "asb bank": "Bank",
    "asda": "Retail",
    "ashghal (public works authority)": "Government/Semi-state",
    "asml": "Tech/Semiconductor",
    "astrazeneca": "Pharma",
    "atlassian": "Tech",
    "auckland airport": "Aviation/Semi-state",
    "australia post": "Logistics",
    "automattic (wordpress.com)": "Tech",
    "aviva": "Insurance",
    "axel springer": "Media",
    "bae systems": "Defence",
    "bajaj auto": "Automotive",
    "bam group": "Construction",
    "bank of china (hong kong)": "Bank",
    "bank of ireland": "Bank",
    "barclays": "Bank",
    "barclays (singapore)": "Bank",
    "barratt developments": "Construction",
    "base company": "Telecom",
    "basecamp": "Tech",
    "basf": "Chemicals",
    "bawag group": "Bank",
    "bayer": "Pharma",
    "bbc": "Media",
    "bbva": "Bank",
    "belfius": "Bank",
    "bell canada": "Telecom",
    "bhp": "Mining",
    "bloomberg (london)": "Fintech/Data",
    "bmo financial group": "Bank",
    "bmw group": "Automotive",
    "bol.com": "E-commerce",
    "booking.com": "Travel Tech",
    "boots ireland": "Retail",
    "bosch": "Industrial",
    "bpost": "Logistics",
    "brookfield": "Real Estate/Infrastructure",
    "bt group": "Telecom",
    "bt openreach": "Telecom",
    "budimex": "Construction",
    "buffer": "Tech",
    "bunnings (wesfarmers)": "Retail",
    "byju's": "Edtech",
    "bytedance / tiktok (apac)": "Tech",
    "cabify": "Tech",
    "caixabank": "Bank",
    "canada post": "Postal/Semi-state",
    "canadian tire": "Retail",
    "canva": "Tech",
    "capgemini germany": "Consulting/ERP",
    "capgemini india": "Consulting/GBS",
    "capgemini netherlands": "Consulting/ERP",
    "capgemini poland": "Consulting/GBS",
    "capgemini portugal": "Consulting/GBS",
    "capgemini spain": "Consulting/ERP",
    "capgemini uk": "Consulting/ERP",
    "capita": "BPO/Outsourcing",
    "capitaland": "Real Estate",
    "careem": "Tech",
    "cathay pacific": "Airline",
    "ccc": "Shoe Retail",
    "cd projekt": "Gaming",
    "celonis": "Tech/Process Mining",
    "centra / spar (bwg foods)": "Retail/Convenience",
    "centrica / british gas": "Energy",
    "cgi group": "IT Consulting",
    "chalhoub group": "Retail",
    "cibc": "Bank",
    "cimb group": "Bank",
    "cipla": "Pharma",
    "circle k ireland": "Retail/Convenience",
    "cisco poland": "Tech",
    "cisco portugal": "Tech",
    "citi (ireland)": "Bank",
    "city developments limited (cdl)": "Real Estate",
    "close": "Tech",
    "clp group": "Energy",
    "cn rail": "Transport",
    "cofinimmo": "Real Estate",
    "cognizant (india)": "IT Services",
    "coles group": "Retail",
    "colruyt group": "Retail",
    "comarch": "IT/ERP",
    "commercial bank of qatar": "Bank",
    "commerzbank": "Bank",
    "commonwealth bank": "Bank",
    "concentrix (ireland)": "BPO/Call Centre",
    "concentrix india": "BPO/Call Centre",
    "concentrix portugal": "BPO/Call Centre",
    "continental": "Automotive",
    "coolblue": "E-commerce",
    "correos": "Postal",
    "costa coffee": "Hospitality/Food Service",
    "countdown/woolworths nz": "Retail",
    "cred": "Fintech",
    "credit suisse/ubs (krakow gbs)": "Bank/GBS",
    "crh": "Construction Materials",
    "critical techworks (bmw)": "Automotive/Tech",
    "crown resorts": "Hospitality",
    "ctt correios": "Postal",
    "culture amp": "Tech",
    "daa (dublin airport authority)": "Aviation/Semi-state",
    "dalata hotel group": "Hospitality",
    "damac properties": "Real Estate",
    "datacom": "IT Services",
    "dbs (hong kong)": "Bank",
    "dbs bank": "Bank",
    "deel": "HR Tech/EOR",
    "delhaize belgium": "Retail",
    "deliveroo": "Tech",
    "delivery hero": "Tech",
    "deloitte australia": "Consulting",
    "deloitte austria": "Consulting",
    "deloitte belgium": "Consulting",
    "deloitte canada": "Consulting",
    "deloitte finland": "Consulting",
    "deloitte germany": "Consulting",
    "deloitte hong kong": "Consulting",
    "deloitte india": "Consulting",
    "deloitte ireland": "Consulting",
    "deloitte malaysia": "Consulting",
    "deloitte netherlands": "Consulting",
    "deloitte new zealand": "Consulting",
    "deloitte poland": "Consulting",
    "deloitte portugal": "Consulting",
    "deloitte qatar": "Consulting",
    "deloitte saudi arabia": "Consulting",
    "deloitte singapore": "Consulting",
    "deloitte spain": "Consulting",
    "deloitte sweden": "Consulting",
    "deloitte uae": "Consulting",
    "deloitte uk": "Consulting",
    "deutsche bahn": "Transport",
    "deutsche bank": "Bank",
    "deutsche telekom": "Telecom",
    "dhl / deutsche post": "Logistics",
    "dino polska": "Retail",
    "dlf": "Real Estate",
    "doha bank": "Bank",
    "doist": "Tech",
    "dp world": "Logistics",
    "dr. reddy's laboratories": "Pharma",
    "dropbox": "Tech",
    "du (eitc)": "Telecom",
    "dubai duty free": "Retail",
    "dunnes stores": "Retail",
    "dxc technology malaysia": "IT/GBS",
    "e& (etisalat)": "Telecom",
    "e.on": "Energy",
    "ebay/paypal ireland ops": "Tech/Retail",
    "edp": "Energy",
    "eir": "Telecom",
    "el corte ingles": "Retail",
    "elastic": "Tech",
    "ellisdon": "Construction",
    "emaar properties": "Real Estate",
    "emirates group": "Airline",
    "emirates nbd": "Bank",
    "employment hero": "Tech",
    "ericsson": "Telecom/Tech",
    "erste group": "Bank",
    "esb": "Energy/Semi-state",
    "etihad airways": "Airline",
    "etihad rail": "Transport/Semi-state",
    "euroclear": "Fintech",
    "experian": "Data/Analytics",
    "extra (united electronics)": "Retail",
    "ey australia": "Consulting",
    "ey austria": "Consulting",
    "ey belgium": "Consulting",
    "ey canada": "Consulting",
    "ey finland": "Consulting",
    "ey germany": "Consulting",
    "ey hong kong": "Consulting",
    "ey india": "Consulting",
    "ey ireland": "Consulting",
    "ey malaysia": "Consulting",
    "ey netherlands": "Consulting",
    "ey new zealand": "Consulting",
    "ey poland": "Consulting",
    "ey portugal": "Consulting",
    "ey qatar": "Consulting",
    "ey saudi arabia": "Consulting",
    "ey singapore": "Consulting",
    "ey spain": "Consulting",
    "ey sweden": "Consulting",
    "ey uae": "Consulting",
    "ey uk": "Consulting",
    "farfetch": "E-commerce",
    "feedzai": "Fintech",
    "fenergo": "Fintech",
    "ferrovial": "Construction/Infrastructure",
    "finnair": "Airline",
    "first abu dhabi bank (fab)": "Bank",
    "fisher & paykel healthcare": "Health Tech",
    "fletcher building": "Construction",
    "flipkart": "E-commerce",
    "flynas": "Airline",
    "fonterra": "Consumer/FMCG",
    "foodstuffs nz": "Retail",
    "fortum": "Energy",
    "fresenius": "Healthcare",
    "freshworks": "Tech",
    "galp energia": "Energy",
    "genpact": "BPO/GBS",
    "genting group": "Conglomerate/Hospitality",
    "gitlab": "Tech",
    "glanbia": "FMCG",
    "glenveagh properties": "Real Estate",
    "glovo": "Tech",
    "goldman sachs (singapore)": "Bank",
    "goldman sachs (uk)": "Bank",
    "google (apac hq)": "Tech",
    "google (australia)": "Tech",
    "google (canada)": "Tech",
    "google (germany)": "Tech",
    "google (hong kong)": "Tech",
    "google (india)": "Tech",
    "google (ireland)": "Tech",
    "google (uae)": "Tech",
    "google (uk)": "Tech",
    "google malaysia": "Tech",
    "google poland": "Tech",
    "grab": "Tech",
    "grab malaysia": "Tech",
    "great eastern": "Insurance",
    "great-west lifeco": "Insurance",
    "greggs": "Food Retail",
    "grifols": "Pharma",
    "groww": "Fintech",
    "gsk": "Pharma",
    "h&m group": "Retail",
    "halter": "Tech",
    "hamad international airport (matar)": "Aviation/Ops",
    "hang seng bank": "Bank",
    "hashicorp": "Tech",
    "hcltech": "IT Services",
    "hdfc bank": "Bank",
    "heineken": "Consumer",
    "hellofresh": "Consumer/Tech",
    "help scout": "Tech",
    "hema": "Retail",
    "hindustan unilever": "FMCG",
    "hsbc": "Bank",
    "hsbc (hong kong)": "Bank",
    "hsbc electronic data processing (malaysia)": "Bank/GBS",
    "hsbc gsc krakow": "Bank/GBS",
    "hugo boss": "Fashion Retail",
    "iag insurance": "Insurance",
    "iberdrola": "Energy",
    "ibm canada": "Tech",
    "ibm india": "Tech",
    "ibm ireland": "Tech",
    "ibm malaysia": "Tech/GBS",
    "ibm poland": "Tech/GBS",
    "ibm uk": "Tech",
    "ica gruppen": "Retail",
    "icici bank": "Bank",
    "ihg hotels & resorts": "Hospitality",
    "ijm corporation": "Construction",
    "ikea (sweden)": "Retail",
    "indeed (ireland)": "Tech",
    "indian hotels company (taj hotels)": "Hospitality",
    "indigo": "Airline",
    "inditex (zara)": "Retail",
    "indra": "IT/Defense",
    "infineon": "Semiconductor",
    "infosys": "IT Services",
    "ing": "Bank",
    "ing belgium": "Bank",
    "ing poland": "Bank",
    "inpost": "Logistics",
    "intact financial": "Insurance",
    "intercom": "Tech",
    "irish life": "Insurance",
    "irish rail (iarnrod eireann)": "Transport/Semi-state",
    "itc limited": "FMCG",
    "itv": "Media",
    "j.p. morgan (ireland)": "Bank",
    "jahez": "Tech",
    "jardine matheson": "Conglomerate",
    "jarir bookstore": "Retail",
    "jd sports": "Sports Retail",
    "jeronimo martins": "Retail",
    "john lewis partnership": "Retail",
    "jpmorgan chase (india)": "Bank",
    "jpmorgan chase (uk)": "Bank",
    "judo bank": "Bank",
    "jumbo supermarkten": "Retail",
    "kbc group": "Bank",
    "keppel corporation": "Conglomerate",
    "kerry group": "FMCG",
    "kesko": "Retail",
    "king (activision blizzard)": "Gaming",
    "kingspan group": "Construction",
    "klarna": "Fintech",
    "klm": "Airline",
    "kone": "Industrial",
    "kpmg australia": "Consulting",
    "kpmg austria": "Consulting",
    "kpmg belgium": "Consulting",
    "kpmg canada": "Consulting",
    "kpmg finland": "Consulting",
    "kpmg germany": "Consulting",
    "kpmg hong kong": "Consulting",
    "kpmg india": "Consulting",
    "kpmg ireland": "Consulting",
    "kpmg malaysia": "Consulting",
    "kpmg netherlands": "Consulting",
    "kpmg new zealand": "Consulting",
    "kpmg poland": "Consulting",
    "kpmg portugal": "Consulting",
    "kpmg qatar": "Consulting",
    "kpmg saudi arabia": "Consulting",
    "kpmg singapore": "Consulting",
    "kpmg spain": "Consulting",
    "kpmg sweden": "Consulting",
    "kpmg uae": "Consulting",
    "kpmg uk": "Consulting",
    "kpn": "Telecom",
    "larsen & toubro": "Construction/Engineering",
    "legal & general": "Insurance",
    "lendlease": "Construction/Real Estate",
    "lidl / schwarz group": "Retail",
    "lidl ireland": "Retail",
    "lightspeed commerce": "Tech",
    "linkedin (ireland)": "Tech",
    "lloyds banking group": "Bank",
    "loblaw companies": "Retail",
    "lpp (reserved)": "Fashion Retail",
    "lufthansa": "Airline",
    "lulu group (uae)": "Retail",
    "lulu hypermarket qatar": "Retail",
    "luxoft (dxc)": "IT/GBS",
    "mahindra group": "Automotive/Conglomerate",
    "mahle": "Automotive",
    "majid al futtaim": "Retail/Real Estate",
    "manulife": "Insurance",
    "manulife hong kong": "Insurance",
    "mapfre": "Insurance",
    "marina bay sands": "Hospitality",
    "marks & spencer": "Retail",
    "mashreq bank": "Bank",
    "mastercard (ireland)": "Fintech",
    "mastercard (uk)": "Fintech",
    "maybank": "Bank",
    "mbank": "Bank",
    "mcdonald's ireland": "Hospitality/Food Service",
    "mcdonald's uk": "Hospitality/Food Service",
    "meesho": "E-commerce",
    "melia hotels international": "Hospitality",
    "mercadona": "Retail",
    "mercedes-benz group": "Automotive",
    "mercedes-benz.io": "Automotive/Tech",
    "merck kgaa": "Pharma",
    "meta (ireland)": "Tech",
    "meta (singapore)": "Tech",
    "meta (uae)": "Tech",
    "meta (uk)": "Tech",
    "metro ag": "Retail/Wholesale",
    "metro inc.": "Retail",
    "microsoft (apac hq)": "Tech",
    "microsoft (hong kong)": "Tech",
    "microsoft (india)": "Tech",
    "microsoft (ireland)": "Tech",
    "microsoft (uk)": "Tech",
    "microsoft australia": "Tech",
    "microsoft canada": "Tech",
    "microsoft germany": "Tech",
    "microsoft malaysia": "Tech",
    "microsoft netherlands": "Tech",
    "microsoft poland": "Tech",
    "microsoft saudi arabia": "Tech",
    "microsoft uae": "Tech",
    "mirvac": "Real Estate",
    "mollie": "Fintech",
    "monzo": "Fintech",
    "morrisons": "Retail",
    "mota-engil": "Construction",
    "msheireb properties": "Real Estate",
    "mtr corporation": "Transport/Semi-state",
    "munich re": "Insurance",
    "myntra": "E-commerce",
    "n26": "Fintech",
    "nab": "Bank",
    "national grid": "Energy",
    "natixis (porto gbs)": "Bank/GBS",
    "natwest group": "Bank",
    "ncc": "Construction",
    "neom": "Giga-project",
    "neste": "Energy",
    "new world development": "Real Estate",
    "next plc": "Retail",
    "nh hotel group": "Hospitality",
    "nn group": "Insurance",
    "nokia": "Tech/Telecom",
    "noon": "E-commerce",
    "nordea (finland)": "Bank",
    "nordea (sweden)": "Bank",
    "nordea poland (gbs)": "Bank/GBS",
    "ntuc fairprice": "Retail",
    "nvidia (india)": "Tech",
    "nz post": "Postal/Semi-state",
    "obb (austrian federal railways)": "Transport/Semi-state",
    "ocado": "Retail/Tech",
    "ocbc bank": "Bank",
    "ola": "Tech",
    "omv": "Energy",
    "ooredoo": "Telecom",
    "op financial group": "Bank/Insurance",
    "optus": "Telecom",
    "oracle (india)": "Tech/ERP",
    "oracle (ireland)": "Tech/ERP",
    "oracle (uk)": "Tech/ERP",
    "orange polska": "Telecom",
    "outsystems": "Tech",
    "panda retail company": "Retail",
    "parknshop / as watson group": "Retail",
    "paypal (ireland)": "Fintech",
    "pccw": "Telecom",
    "pcl construction": "Construction",
    "penneys / primark ireland": "Retail",
    "permanent tsb": "Bank",
    "persimmon homes": "Construction",
    "personio": "HR Tech",
    "pestana hotel group": "Hospitality",
    "petronas": "Energy",
    "pge polska grupa energetyczna": "Energy",
    "philips": "Tech/Health",
    "phonepe": "Fintech",
    "pkn orlen": "Energy",
    "pko bank polski": "Bank",
    "poczta polska": "Postal",
    "porr": "Construction",
    "pos malaysia": "Postal",
    "posti group": "Postal",
    "postnl": "Postal/Logistics",
    "postnord": "Postal/Logistics",
    "primark": "Retail",
    "propertyguru": "Tech",
    "proximus": "Telecom",
    "prudential hong kong": "Insurance",
    "public bank": "Bank",
    "puma": "Sports Apparel",
    "pwc australia": "Consulting",
    "pwc austria": "Consulting",
    "pwc belgium": "Consulting",
    "pwc canada": "Consulting",
    "pwc finland": "Consulting",
    "pwc germany": "Consulting",
    "pwc hong kong": "Consulting",
    "pwc india": "Consulting",
    "pwc ireland": "Consulting",
    "pwc malaysia": "Consulting",
    "pwc netherlands": "Consulting",
    "pwc new zealand": "Consulting",
    "pwc poland": "Consulting",
    "pwc portugal": "Consulting",
    "pwc qatar": "Consulting",
    "pwc saudi arabia": "Consulting",
    "pwc singapore": "Consulting",
    "pwc spain": "Consulting",
    "pwc sweden": "Consulting",
    "pwc uae": "Consulting",
    "pwc uk": "Consulting",
    "pzu": "Insurance",
    "qantas": "Airline",
    "qatar airways": "Airline",
    "qatar islamic bank": "Bank",
    "qatarenergy": "Energy",
    "qiddiya": "Giga-project",
    "qnb group": "Bank",
    "rabobank": "Bank",
    "radisson hotel group (ireland)": "Hospitality",
    "raiffeisen bank international": "Bank",
    "randstad": "Staffing/HR",
    "razorpay": "Fintech",
    "rbc (royal bank of canada)": "Bank",
    "red bull": "Consumer",
    "red sea global": "Giga-project",
    "reliance retail": "Retail",
    "repsol": "Energy",
    "revolut": "Fintech",
    "rewe austria (billa/merkur)": "Retail",
    "rewe group": "Retail",
    "rio tinto": "Mining",
    "riyad bank": "Bank",
    "rogers communications": "Telecom",
    "rolls-royce": "Industrial",
    "roshn": "Real Estate/Giga-project",
    "royal mail": "Postal/Logistics",
    "ryanair": "Airline",
    "s group (s-ryhma)": "Retail",
    "sabic": "Chemicals",
    "safetyculture": "Tech",
    "sainsbury's": "Retail",
    "salesforce (india)": "Tech",
    "salesforce (ireland)": "Tech",
    "salesforce (uae)": "Tech",
    "salesforce (uk)": "Tech",
    "salesforce australia": "Tech",
    "salesforce canada": "Tech",
    "salesforce germany": "Tech",
    "salesforce singapore": "Tech",
    "santander": "Bank",
    "santander bank polska": "Bank",
    "sap": "Tech/ERP",
    "sap ireland": "Tech/ERP",
    "sap labs india": "Tech/ERP",
    "sas airlines": "Airline",
    "saudi aramco": "Energy",
    "saudi electricity company": "Utility/Semi-state",
    "saudi national bank (snb)": "Bank",
    "saudia (airline)": "Airline",
    "scandic hotels": "Hospitality",
    "schiphol group": "Aviation/Semi-state",
    "scotiabank": "Bank",
    "sea limited (shopee/garena)": "Tech",
    "seb": "Bank",
    "shell (nl)": "Energy",
    "shell business operations krakow": "Energy/GBS",
    "shopee malaysia": "E-commerce",
    "shopify": "Tech/E-commerce",
    "siemens": "Industrial/Tech",
    "sime darby": "Conglomerate",
    "sinch": "Tech",
    "singtel": "Telecom",
    "skanska": "Construction",
    "sky city": "Hospitality",
    "sobeys / empire company": "Retail",
    "softcat": "IT Reseller",
    "software ag": "Tech/ERP",
    "solvay": "Chemicals",
    "sonae": "Retail/Conglomerate",
    "spar austria": "Retail",
    "spark new zealand": "Telecom",
    "spotify": "Tech",
    "standard chartered (hk)": "Bank",
    "starbucks ireland": "Hospitality/Food Service",
    "state street (ireland)": "Fintech/GBS",
    "state street (krakow gbs)": "GBS/Fintech",
    "stc (saudi telecom)": "Telecom",
    "stockland": "Real Estate",
    "stora enso": "Forestry/Materials",
    "strabag": "Construction",
    "stripe": "Fintech",
    "sun hung kai properties": "Real Estate",
    "sun life": "Insurance",
    "sun pharma": "Pharma",
    "suncorp": "Insurance/Bank",
    "sunway group": "Construction/Property",
    "supercell": "Gaming",
    "supervalu / musgrave": "Retail",
    "swedbank": "Bank",
    "swift": "Fintech",
    "swiggy": "Tech",
    "talabat": "Tech",
    "talkdesk": "Tech",
    "tap air portugal": "Airline",
    "tata motors": "Automotive",
    "tata steel": "Manufacturing",
    "taylor wimpey": "Construction",
    "tcs": "IT Services",
    "td bank group": "Bank",
    "telefonica": "Telecom",
    "teleperformance (ireland)": "BPO/Call Centre",
    "teleperformance india": "BPO/Call Centre",
    "teleperformance portugal": "BPO/Call Centre",
    "teleperformance spain": "BPO/Call Centre",
    "teleperformance uk": "BPO/Call Centre",
    "telia company": "Telecom",
    "telstra": "Telecom",
    "telus": "Telecom",
    "tesco": "Retail",
    "tesco ireland": "Retail",
    "three ireland": "Telecom",
    "tiktok (ireland)": "Tech",
    "titan company": "Retail/Consumer",
    "tomtom": "Tech",
    "toptal": "Tech/Staffing",
    "trade me": "Tech",
    "trade republic": "Fintech",
    "tui group": "Travel/Hospitality",
    "twilio": "Tech",
    "uber (netherlands ops)": "Tech",
    "ucb": "Pharma",
    "umicore": "Materials",
    "union coop": "Retail",
    "uniqa insurance group": "Insurance",
    "uob": "Bank",
    "upm": "Forestry/Materials",
    "van der valk": "Hospitality",
    "verbund": "Energy",
    "version 1": "IT Consulting/ERP",
    "vienna insurance group": "Insurance",
    "vodafone portugal": "Telecom",
    "vodafone qatar": "Telecom",
    "vodafone uk": "Telecom",
    "voestalpine": "Industrial",
    "volkerwessels": "Construction",
    "volkswagen group": "Automotive",
    "volvo group": "Automotive/Industrial",
    "vonovia": "Real Estate",
    "wartsila": "Industrial",
    "wayflyer": "Fintech",
    "wealthsimple": "Fintech",
    "wesfarmers": "Retail/Conglomerate",
    "westpac": "Bank",
    "whitbread / premier inn": "Hospitality",
    "wipro": "IT Services",
    "wise": "Fintech",
    "wolt (doordash)": "Tech",
    "wolters kluwer": "Info Services",
    "woolworths group": "Retail",
    "workday (ireland)": "Tech/ERP",
    "xero": "Tech/ERP",
    "yit": "Construction",
    "zabka": "Retail",
    "zalando": "E-commerce",
    "zapier": "Tech",
    "zendesk (ireland)": "Tech",
    "zf friedrichshafen": "Automotive",
    "zoho": "Tech/ERP",
    "zomato": "Tech",
    "zurich insurance ireland": "Insurance"
}

# Secondary lookup keyed by company name with any trailing "(Region)" suffix
# stripped, e.g. "google (ireland)" -> "google". Built once at import time.
_SUFFIX_RE = re.compile(r"\s*\([^)]*\)\s*$")
BASE_SECTOR_BY_COMPANY = {}
for _k, _v in SECTOR_BY_COMPANY.items():
    _base = _SUFFIX_RE.sub("", _k).strip()
    BASE_SECTOR_BY_COMPANY.setdefault(_base, _v)


def sector_for(company: str) -> str:
    """Best-effort industry sector for a company, used to tag/filter jobs."""
    if not company:
        return "Other"
    key = company.strip().lower()
    if key in SECTOR_BY_COMPANY:
        return SECTOR_BY_COMPANY[key]
    base = _SUFFIX_RE.sub("", key).strip()
    if base in BASE_SECTOR_BY_COMPANY:
        return BASE_SECTOR_BY_COMPANY[base]
    return "Other"


# ISO alpha-3 country codes some ATSs (mostly Workday) append after a comma,
# e.g. "Dubai, ARE" -- checked before the keyword scan below since it's exact.
ISO3_TO_COUNTRY = {
    "ARE": "UAE", "GBR": "UK", "DEU": "Germany", "IRL": "Ireland",
    "IND": "India", "SGP": "Singapore", "AUS": "Australia", "NZL": "New Zealand",
    "CAN": "Canada", "USA": "United States", "SAU": "Saudi Arabia", "QAT": "Qatar",
    "MYS": "Malaysia", "HKG": "Hong Kong", "POL": "Poland", "PRT": "Portugal",
    "NLD": "Netherlands", "AUT": "Austria", "BEL": "Belgium", "ESP": "Spain",
    "SWE": "Sweden", "FIN": "Finland", "FRA": "France", "ITA": "Italy",
    "DNK": "Denmark", "NOR": "Norway", "CHE": "Switzerland",
}

# Keyword -> canonical country name, checked in order (first match wins) if
# the ISO3 check above doesn't hit. Mirrors REGION_KEYWORDS but resolves to a
# single display name per country instead of a yes/no.
COUNTRY_KEYWORDS = [
    ("ireland", "Ireland"), ("dublin", "Ireland"), ("cork", "Ireland"),
    ("united kingdom", "UK"), ("london", "UK"), ("england", "UK"),
    ("scotland", "UK"), ("wales", "UK"), ("uk", "UK"),
    ("germany", "Germany"), ("berlin", "Germany"), ("munich", "Germany"),
    ("frankfurt", "Germany"), ("hamburg", "Germany"), ("cologne", "Germany"),
    ("netherlands", "Netherlands"), ("amsterdam", "Netherlands"),
    ("france", "France"), ("paris", "France"),
    ("spain", "Spain"), ("madrid", "Spain"), ("barcelona", "Spain"),
    ("italy", "Italy"), ("milan", "Italy"), ("milano", "Italy"), ("rome", "Italy"),
    ("roma", "Italy"), ("florence", "Italy"), ("firenze", "Italy"),
    ("sweden", "Sweden"), ("stockholm", "Sweden"),
    ("denmark", "Denmark"), ("copenhagen", "Denmark"),
    ("finland", "Finland"), ("helsinki", "Finland"),
    ("norway", "Norway"), ("oslo", "Norway"),
    ("poland", "Poland"), ("warsaw", "Poland"), ("krakow", "Poland"), ("kraków", "Poland"),
    ("portugal", "Portugal"), ("lisbon", "Portugal"), ("lisboa", "Portugal"), ("porto", "Portugal"),
    ("belgium", "Belgium"), ("brussels", "Belgium"),
    ("austria", "Austria"), ("vienna", "Austria"),
    ("switzerland", "Switzerland"), ("zurich", "Switzerland"), ("zürich", "Switzerland"),
    ("singapore", "Singapore"),
    ("united arab emirates", "UAE"), ("dubai", "UAE"), ("abu dhabi", "UAE"), ("uae", "UAE"),
    ("saudi arabia", "Saudi Arabia"), ("riyadh", "Saudi Arabia"), ("jeddah", "Saudi Arabia"),
    ("qatar", "Qatar"), ("doha", "Qatar"),
    ("india", "India"), ("bangalore", "India"), ("bengaluru", "India"), ("mumbai", "India"),
    ("delhi", "India"), ("hyderabad", "India"), ("pune", "India"), ("chennai", "India"),
    ("gurgaon", "India"), ("gurugram", "India"),
    ("hong kong", "Hong Kong"),
    ("malaysia", "Malaysia"), ("kuala lumpur", "Malaysia"),
    ("australia", "Australia"), ("sydney", "Australia"), ("melbourne", "Australia"),
    ("brisbane", "Australia"), ("perth", "Australia"),
    ("new zealand", "New Zealand"), ("auckland", "New Zealand"), ("wellington", "New Zealand"),
    ("canada", "Canada"), ("toronto", "Canada"), ("ontario", "Canada"),
    ("vancouver", "Canada"), ("montreal", "Canada"),
    ("united states", "United States"), ("usa", "United States"), ("u.s.a", "United States"),
    ("u.s.", "United States"),
]


def country_from_location(location: str) -> str:
    """Best-effort country name for a job, parsed from its location string
    (not the company) since one company posts across many countries."""
    if not location:
        return "Other"
    loc = location.strip()
    loc_lower = loc.lower()

    last_part = loc.split(",")[-1].strip().upper()
    if last_part in ISO3_TO_COUNTRY:
        return ISO3_TO_COUNTRY[last_part]

    for keyword, country in COUNTRY_KEYWORDS:
        if keyword in loc_lower:
            return country

    if "remote" in loc_lower:
        return "Remote / Other"

    return "Other"


def fetch_json(url: str, timeout: int = 20):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (job-dashboard-bot)"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as e:
        print(f"  ! fetch failed for {url}: {e}")
        return None


def scrape_greenhouse(slug: str):
    data = fetch_json(f"https://boards-api.greenhouse.io/v1/boards/{slug}/jobs?content=true")
    if not data or "jobs" not in data:
        return []
    out = []
    for j in data["jobs"]:
        title = j.get("title", "")
        location = (j.get("location") or {}).get("name", "")
        if region_ok(location):
            content_html = j.get("content") or ""
            out.append({
                "company": slug,
                "ats": "greenhouse",
                "title": title,
                "location": location,
                "url": j.get("absolute_url"),
                "updated_at": j.get("updated_at"),
                "description_text": _strip_html(content_html),
            })
    return out


def scrape_lever(slug: str):
    data = fetch_json(f"https://api.lever.co/v0/postings/{slug}?mode=json")
    if not data or not isinstance(data, list):
        return []
    out = []
    for j in data:
        title = j.get("text", "")
        cats = j.get("categories") or {}
        location = cats.get("location", "")
        if region_ok(location):
            created = j.get("createdAt")
            created_iso = None
            if created:
                try:
                    created_iso = datetime.fromtimestamp(created / 1000, tz=timezone.utc).isoformat()
                except Exception:
                    pass
            out.append({
                "company": slug,
                "ats": "lever",
                "title": title,
                "location": location,
                "url": j.get("hostedUrl"),
                "updated_at": created_iso,
            })
    return out


def scrape_ashby(slug: str):
    data = fetch_json(f"https://api.ashbyhq.com/posting-api/job-board/{slug}")
    if not data:
        return []
    jobs = data.get("jobs") or data.get("jobPostings") or []
    out = []
    for j in jobs:
        title = j.get("title", "")
        location = j.get("location", "") or j.get("locationName", "")
        if j.get("isRemote") and "remote" not in (location or "").lower():
            location = f"{location} (Remote)".strip()
        if region_ok(location):
            out.append({
                "company": slug,
                "ats": "ashby",
                "title": title,
                "location": location,
                "url": j.get("jobUrl") or j.get("applyUrl"),
                "updated_at": j.get("publishedAt"),
            })
    return out


def scrape_workday(company: str, tenant: str, wd_host: str, site: str, max_pages: int = 25):
    base = f"https://{tenant}.{wd_host}.myworkdayjobs.com/wday/cxs/{tenant}/{site}/jobs"
    out = []
    offset = 0
    page_size = 20  # Workday hard-caps at 20 per page
    for _ in range(max_pages):
        payload = json.dumps({
            "appliedFacets": {},
            "limit": page_size,
            "offset": offset,
            "searchText": "",
        }).encode("utf-8")
        req = urllib.request.Request(
            base,
            data=payload,
            method="POST",
            headers={
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "Mozilla/5.0 (job-dashboard-bot)",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                data = json.loads(resp.read().decode("utf-8"))
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as e:
            print(f"  ! fetch failed for {base} (offset {offset}): {e}")
            break

        postings = (data or {}).get("jobPostings") or []
        if not postings:
            break

        for j in postings:
            title = j.get("title", "")
            location = j.get("locationsText", "") or j.get("bulletFields", [""])[0]
            if region_ok(location):
                path = j.get("externalPath", "")
                out.append({
                    "company": company,
                    "ats": "workday",
                    "title": title,
                    "location": location,
                    "url": f"https://{tenant}.{wd_host}.myworkdayjobs.com/{site}{path}" if path else None,
                    "updated_at": j.get("postedOn"),
                })

        if len(postings) < page_size:
            break
        offset += page_size
        time.sleep(0.3)

    return out


def scrape_smartrecruiters(company_id: str, max_pages: int = 15):
    out = []
    offset = 0
    page_size = 100
    for _ in range(max_pages):
        url = (
            f"https://api.smartrecruiters.com/v1/companies/{company_id}/postings"
            f"?limit={page_size}&offset={offset}"
        )
        data = fetch_json(url)
        if not data or "content" not in data:
            break

        postings = data.get("content") or []
        for j in postings:
            title = j.get("name", "")
            loc = j.get("location") or {}
            location = ", ".join(filter(None, [loc.get("city"), loc.get("region"), loc.get("country")]))
            if loc.get("remote"):
                location = f"{location} (Remote)".strip(", ")
            if region_ok(location):
                out.append({
                    "company": company_id,
                    "ats": "smartrecruiters",
                    "title": title,
                    "location": location,
                    "url": (j.get("applyUrl") or (j.get("ref", {}) or {}).get("jobAd")),
                    "updated_at": j.get("releasedDate"),
                })

        if len(postings) < page_size:
            break
        offset += page_size
        time.sleep(0.3)

    return out


def scrape_workable(slug: str):
    data = fetch_json(f"https://apply.workable.com/api/v1/widget/accounts/{slug}")
    if not data or "jobs" not in data:
        return []
    out = []
    for j in data["jobs"]:
        title = j.get("title", "")
        location = j.get("location", {}) or {}
        loc_str = ", ".join(filter(None, [
            location.get("city"), location.get("region"), location.get("country"),
        ]))
        if location.get("telecommuting"):
            loc_str = f"{loc_str} (Remote)".strip(", ")
        if region_ok(loc_str):
            out.append({
                "company": slug,
                "ats": "workable",
                "title": title,
                "location": loc_str,
                "url": j.get("url") or j.get("shortlink"),
                "updated_at": j.get("published_on") or j.get("created_at"),
            })
    return out


def scrape_recruitee(slug: str):
    data = fetch_json(f"https://{slug}.recruitee.com/api/offers/")
    if not data or "offers" not in data:
        return []
    out = []
    for j in data["offers"]:
        title = j.get("title", "")
        location = j.get("location", "") or j.get("city", "")
        if j.get("remote"):
            location = f"{location} (Remote)".strip(", ")
        if region_ok(location):
            out.append({
                "company": slug,
                "ats": "recruitee",
                "title": title,
                "location": location,
                "url": j.get("careers_url"),
                "updated_at": j.get("created_at"),
            })
    return out


def scrape_personio(slug: str):
    url = f"https://{slug}.jobs.personio.de/xml?language=en"
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (job-dashboard-bot)"})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            xml_text = resp.read().decode("utf-8")
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
        print(f"  ! fetch failed for {url}: {e}")
        return []

    out = []
    for m in re.finditer(r"<position>(.*?)</position>", xml_text, re.DOTALL):
        block = m.group(1)

        def field(name):
            fm = re.search(rf"<{name}><!\[CDATA\[(.*?)\]\]></{name}>", block, re.DOTALL) \
                 or re.search(rf"<{name}>(.*?)</{name}>", block, re.DOTALL)
            return fm.group(1).strip() if fm else ""

        title = field("name")
        location = ", ".join(filter(None, [field("office"), field("city")]))
        if region_ok(location):
            out.append({
                "company": slug,
                "ats": "personio",
                "title": title,
                "location": location,
                "url": field("careerSiteUrl") or None,
                "updated_at": field("createdAt"),
            })
    return out



def scrape_pinpoint(slug: str):
    data = fetch_json(f"https://{slug}.pinpointhq.com/postings.json")
    if not data:
        return []
    postings = data if isinstance(data, list) else (data.get("data") or data.get("jobs") or data.get("postings") or [])
    out = []
    for j in postings:
        if not isinstance(j, dict):
            continue
        title = j.get("title") or j.get("name") or ""
        location = j.get("location") or j.get("location_name") or ""
        if isinstance(location, dict):
            location = ", ".join(filter(None, [location.get("city"), location.get("region"), location.get("country")]))
        if region_ok(str(location)):
            out.append({
                "company": slug,
                "ats": "pinpoint",
                "title": title,
                "location": str(location),
                "url": j.get("url") or j.get("apply_url") or j.get("external_url"),
                "updated_at": j.get("published_at") or j.get("created_at") or j.get("updated_at"),
                "description_text": _strip_html(j.get("description") or ""),
            })
    return out

def _jsonld_location(job_location):
    """jobLocation can be a dict, a list of dicts, or absent entirely."""
    def one(loc):
        if not isinstance(loc, dict):
            return ""
        addr = loc.get("address")
        if isinstance(addr, dict):
            return ", ".join(filter(None, [
                addr.get("addressLocality"), addr.get("addressRegion"), addr.get("addressCountry"),
            ]))
        if isinstance(addr, str):
            return addr
        return ""

    if isinstance(job_location, list):
        parts = [one(l) for l in job_location]
        return " / ".join(p for p in parts if p)
    return one(job_location)



# ---------------------------------------------------------------------------
# Dynamic ATS discovery + cached coverage expansion
# ---------------------------------------------------------------------------

ATS_PROBE_VERSION = 31
ATS_PROBE_LIMIT = int(os.environ.get("ATS_PROBE_LIMIT", "60"))
ATS_CACHE_PATH = "ats_platform_cache.json"

_CORP_WORDS = re.compile(r"\b(?:limited|ltd|plc|inc|incorporated|corporation|corp|company|group|holdings|ireland|international)\b", re.I)
_EF_GROUP_ID_RE = re.compile(r'_EF_GROUP_ID[\'\"]?\]?\s*[=:]\s*[\'\"]([^\'\"]+)[\'\"]')
_PHENOM_REFNUM_RE = re.compile(r'"refNum"\s*:\s*"([A-Za-z0-9_-]+)"')


def candidate_slugs(company_name: str):
    """Bounded ATS-board slug guesses. Exact cached mappings are tried first."""
    base = re.sub(r"\([^)]*\)", " ", company_name or "")
    base = _CORP_WORDS.sub(" ", base)
    words = re.findall(r"[a-zA-Z0-9]+", base.lower())
    if not words:
        return []
    cands = []
    joined = "".join(words)
    dashed = "-".join(words)
    for x in (joined, dashed, words[0], joined + "jobs", joined + "careers"):
        # Very short guesses create false-positive boards (e.g. "abb", "eir").
        # Require 4+ characters unless the full normalized company name itself is short.
        min_len = 2 if len(joined) <= 3 and x == joined else 4
        if x and x not in cands and len(x) >= min_len:
            cands.append(x)
    # Parenthetical brand is often the actual ATS slug, e.g. VMware (Broadcom).
    for paren in re.findall(r"\(([^)]*)\)", company_name or ""):
        pwords = re.findall(r"[a-zA-Z0-9]+", paren.lower())
        if pwords:
            x = "".join(pwords)
            if x not in cands:
                cands.append(x)
    return cands[:6]



def _careers_page_ats_candidates(company: str, careers_url: str, sess):
    """Discover ATS identifiers from the employer's actual careers page.

    This is deliberately preferred over guessed slugs. It follows redirects and
    scans public HTML for known ATS hosts, then validates every candidate.
    """
    if not sess or not careers_url:
        return []
    try:
        r = sess.get(careers_url, timeout=15, allow_redirects=True)
        if r.status_code >= 400:
            return []
        text = (r.text or "") + "\n" + str(r.url or "")
    except Exception:
        return []

    patterns = [
        ("greenhouse", r"(?:boards|job-boards)\.greenhouse\.io/([A-Za-z0-9_-]+)"),
        ("lever", r"jobs\.lever\.co/([A-Za-z0-9_-]+)"),
        ("ashby", r"jobs\.ashbyhq\.com/([A-Za-z0-9_-]+)"),
        ("smartrecruiters", r"(?:jobs\.)?smartrecruiters\.com/([A-Za-z0-9_-]+)"),
        ("workable", r"apply\.workable\.com/([A-Za-z0-9_-]+)"),
        ("recruitee", r"https?://([A-Za-z0-9-]+)\.recruitee\.com"),
        ("personio", r"https?://([A-Za-z0-9-]+)\.jobs\.personio\.(?:de|com)"),
        ("pinpoint", r"https?://([A-Za-z0-9-]+)\.pinpointhq\.com"),
        ("eightfold", r"https?://([A-Za-z0-9-]+)\.eightfold\.ai"),
    ]

    out = []
    seen = set()
    for platform, pattern in patterns:
        for m in re.finditer(pattern, text, re.I):
            slug = m.group(1).strip()
            key = (platform, slug.lower())
            if not slug or key in seen:
                continue
            seen.add(key)
            out.append((platform, slug))
    return out


def _session():
    if requests is None:
        return None
    sess = requests.Session()
    sess.headers.update({"User-Agent": "Mozilla/5.0 (compatible; IrelandJobRadar/2.0)"})
    return sess


def _probe_platform(platform: str, slug: str, sess) -> bool:
    """Validate that a slug really resolves to an ATS board. Does NOT require an Ireland vacancy."""
    if not sess or not slug:
        return False
    try:
        if platform == "greenhouse":
            r=sess.get(f"https://boards-api.greenhouse.io/v1/boards/{slug}/jobs", timeout=10)
            return r.status_code == 200 and isinstance(r.json().get("jobs"), list)
        if platform == "lever":
            r=sess.get(f"https://api.lever.co/v0/postings/{slug}?mode=json", timeout=10)
            return r.status_code == 200 and isinstance(r.json(), list)
        if platform == "smartrecruiters":
            r=sess.get(f"https://api.smartrecruiters.com/v1/companies/{slug}/postings?limit=1", timeout=10)
            return r.status_code == 200 and isinstance(r.json(), dict) and "content" in r.json()
        if platform == "ashby":
            r=sess.get(f"https://api.ashbyhq.com/posting-api/job-board/{slug}", timeout=10)
            d=r.json() if r.status_code == 200 else {}
            return r.status_code == 200 and isinstance(d, dict) and ("jobs" in d or "jobPostings" in d)
        if platform == "recruitee":
            r=sess.get(f"https://{slug}.recruitee.com/api/offers/", timeout=10)
            d=r.json() if r.status_code == 200 else {}
            return r.status_code == 200 and isinstance(d, dict) and "offers" in d
        if platform == "personio":
            r=sess.get(f"https://{slug}.jobs.personio.de/xml?language=en", timeout=10)
            return r.status_code == 200 and ("<position" in r.text or "<workzag-jobs" in r.text)
        if platform == "pinpoint":
            r=sess.get(f"https://{slug}.pinpointhq.com/postings.json", timeout=10)
            if r.status_code != 200: return False
            d=r.json()
            return isinstance(d, (list, dict))
        if platform == "eightfold":
            r=sess.get(f"https://{slug}.eightfold.ai/careers", timeout=10)
            if r.status_code != 200: return False
            m=_EF_GROUP_ID_RE.search(r.text)
            if not m: return False
            rr=sess.get(f"https://{slug}.eightfold.ai/api/pcsx/search", params={"domain":m.group(1),"query":"","location":"","start":0}, timeout=10)
            return rr.status_code == 200 and isinstance(rr.json(), dict)
        if platform == "phenom":
            if "|" not in slug: return False
            domain, refnum = slug.split("|",1)
            payload={"lang":"en_global","deviceType":"desktop","country":"global","pageName":"search-results","size":1,"from":0,"jobs":True,"counts":True,"all_fields":["category","country","city","type"],"clearAll":False,"jdsource":"facets","isSliderEnable":False,"pageId":"page20","siteType":"external","keywords":"","global":True,"selected_fields":{},"sort":{"order":"desc","field":"postedDate"},"locationData":{},"refNum":refnum,"ddoKey":"refineSearch"}
            rr=sess.post(f"https://{domain}/widgets",json=payload,timeout=15)
            return rr.status_code == 200 and isinstance(rr.json(), dict)
    except Exception:
        return False
    return False


def _scrape_eightfold(company: str, slug: str, sess):
    out=[]
    try:
        page=sess.get(f"https://{slug}.eightfold.ai/careers",timeout=10)
        m=_EF_GROUP_ID_RE.search(page.text)
        if not m: return out
        start=0
        seen_ids=set()
        for _ in range(20):
            r=sess.get(f"https://{slug}.eightfold.ai/api/pcsx/search",params={"domain":m.group(1),"query":"","location":"","start":start},timeout=15)
            if r.status_code!=200: break
            d=r.json(); jobs=d.get("positions") or d.get("results") or []
            if not jobs: break
            new=0
            for j in jobs:
                jid=str(j.get("id") or j.get("position_id") or j.get("canonicalPositionUrl") or "")
                if jid and jid in seen_ids: continue
                if jid: seen_ids.add(jid)
                new+=1
                loc=j.get("location") or j.get("locations") or j.get("city") or ""
                if isinstance(loc,list): loc=", ".join(str(x) for x in loc)
                loc=str(loc)
                if not region_ok(loc): continue
                posted=j.get("t_create") or j.get("start_date") or j.get("posted_date")
                updated=None
                if posted:
                    try:
                        updated=datetime.fromtimestamp(posted,timezone.utc).isoformat() if isinstance(posted,(int,float)) else str(posted)
                    except Exception: updated=str(posted)
                out.append({"company":company,"ats":"eightfold","title":j.get("name") or j.get("title") or "","location":loc,"url":j.get("canonicalPositionUrl") or j.get("apply_url") or f"https://{slug}.eightfold.ai/careers/job/{jid}","updated_at":updated,"description_text":_strip_html(j.get("job_description") or j.get("description") or "")})
            if new==0: break
            start += len(jobs)
            if len(jobs)<10: break
    except Exception as e:
        print(f"  ! eightfold/{slug}: {e}")
    return out


def _scrape_phenom(company: str, slug: str, sess):
    if "|" not in slug: return []
    domain, refnum=slug.split("|",1)
    out=[]; offset=0
    for _ in range(25):
        payload={"lang":"en_global","deviceType":"desktop","country":"global","pageName":"search-results","size":20,"from":offset,"jobs":True,"counts":True,"all_fields":["category","country","city","type"],"clearAll":False,"jdsource":"facets","isSliderEnable":False,"pageId":"page20","siteType":"external","keywords":"","global":True,"selected_fields":{},"sort":{"order":"desc","field":"postedDate"},"locationData":{},"refNum":refnum,"ddoKey":"refineSearch"}
        try:
            r=sess.post(f"https://{domain}/widgets",json=payload,timeout=15)
            if r.status_code!=200: break
            jobs=((r.json().get("refineSearch") or {}).get("data") or {}).get("jobs") or []
        except Exception: break
        if not jobs: break
        for j in jobs:
            loc=j.get("locationDisplay") or j.get("cityStateCountry") or j.get("cityCountry") or j.get("city") or ""
            if not region_ok(str(loc)): continue
            jid=j.get("jobId") or j.get("id") or ""
            url=j.get("applyUrl") or j.get("jdUrl") or f"https://{domain}/job/{jid}"
            out.append({"company":company,"ats":"phenom","title":j.get("title") or j.get("jobTitle") or "","location":str(loc),"url":url,"updated_at":j.get("postedDate"),"description_text":_strip_html(j.get("descriptionTeaser") or j.get("description") or "")})
        if len(jobs)<20: break
        offset += len(jobs)
    return out


def _scrape_cached_mapping(company: str, platform: str, slug: str, sess):
    try:
        if platform == "greenhouse": jobs=scrape_greenhouse(slug)
        elif platform == "lever": jobs=scrape_lever(slug)
        elif platform == "smartrecruiters": jobs=scrape_smartrecruiters(slug)
        elif platform == "ashby": jobs=scrape_ashby(slug)
        elif platform == "recruitee": jobs=scrape_recruitee(slug)
        elif platform == "personio": jobs=scrape_personio(slug)
        elif platform == "pinpoint": jobs=scrape_pinpoint(slug)
        elif platform == "workable": jobs=scrape_workable(slug)
        elif platform == "eightfold": jobs=_scrape_eightfold(company,slug,sess)
        elif platform == "phenom": jobs=_scrape_phenom(company,slug,sess)
        else: return []
        for j in jobs:
            j["company"] = company
        return jobs
    except Exception as e:
        print(f"  ! cached {platform}/{company}: {e}")
        return []


def discover_and_scrape_manual(company_registry):
    """Convert unresolved companies to automatic ATS coverage over time.

    Cached confirmed mappings are reused every run. Cached misses are retained,
    but a probe-version bump automatically rechecks them after discovery logic
    changes. A bounded number of never-probed companies is attempted per run so
    the GitHub Action remains predictable rather than turning into a multi-hour crawl.
    """
    sess=_session()
    if not sess:
        print("  ! requests not installed; dynamic ATS discovery skipped")
        return [], {}
    try:
        with open(ATS_CACHE_PATH,encoding="utf-8") as f: raw=json.load(f)
        stored_version=raw.pop("__probe_version__",0)
        cache=raw
        if stored_version != ATS_PROBE_VERSION:
            cache={k:v for k,v in cache.items() if isinstance(v,dict) and v.get("platform") not in (None,"none")}
    except Exception:
        cache={}

    # Seed exact enterprise mappings, but still validate each endpoint before use.
    for company, slug in KNOWN_EIGHTFOLD_MAPPINGS.items():
        cache.setdefault(company, {"platform": "eightfold", "slug": slug})
    for company, slug in KNOWN_PHENOM_MAPPINGS.items():
        cache.setdefault(company, {"platform": "phenom", "slug": slug})

    dynamic_jobs=[]; confirmed={}; fresh=0
    platforms=("greenhouse","lever","smartrecruiters","ashby","workable","recruitee","personio","pinpoint","eightfold")

    for entry in company_registry:
        company=entry["company"]
        info=cache.get(company) if isinstance(cache.get(company),dict) else None
        platform=info.get("platform") if info else None
        slug=info.get("slug") if info else None

        if platform and platform != "none":
            # Never trust a stale/guessed cache entry without validating its endpoint.
            if not _probe_platform(platform,slug,sess):
                cache.pop(company,None); platform=slug=None
            else:
                confirmed[company]={"platform":platform,"slug":slug}
        elif platform == "none":
            continue

        if not platform:
            if fresh >= ATS_PROBE_LIMIT:
                continue
            fresh += 1

            # First inspect the company's real careers page. This is much more
            # reliable than guessing ATS board names from company strings.
            for plat, cand in _careers_page_ats_candidates(
                company, entry.get("careers_url") or "", sess
            ):
                if plat in platforms and _probe_platform(plat, cand, sess):
                    platform, slug = plat, cand
                    break

            # Only fall back to bounded slug guesses if the careers page did not
            # expose a recognizable ATS link.
            if not platform:
                for cand in candidate_slugs(company):
                    for plat in platforms:
                        if _probe_platform(plat,cand,sess):
                            platform,slug=plat,cand
                            break
                    if platform:
                        break

            cache[company]={"platform":platform or "none","slug":slug}
            if platform:
                confirmed[company]={"platform":platform,"slug":slug}
                print(f"  + discovered {company}: {platform}/{slug}")

        if platform:
            jobs=_scrape_cached_mapping(company,platform,slug,sess)
            dynamic_jobs.extend(jobs)
            print(f"dynamic/{company} [{platform}]: {len(jobs)} Ireland jobs")

    cache["__probe_version__"]=ATS_PROBE_VERSION
    with open(ATS_CACHE_PATH,"w",encoding="utf-8") as f:
        json.dump(cache,f,indent=2)
    print(f"Dynamic ATS discovery: {len(confirmed)} confirmed cached/discovered platforms; {fresh} new companies probed this run")
    return dynamic_jobs, confirmed

def scrape_jsonld(company: str, url: str):
    if not url:
        return []
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (job-dashboard-bot)"})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            html_text = resp.read().decode("utf-8", errors="ignore")
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
        print(f"  ! fetch failed for {url}: {e}")
        return []

    out = []
    for m in re.finditer(
        r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
        html_text, re.DOTALL | re.IGNORECASE,
    ):
        block = m.group(1).strip()
        try:
            data = json.loads(block)
        except ValueError:
            continue

        candidates = data if isinstance(data, list) else [data]
        expanded = []
        for c in candidates:
            if isinstance(c, dict) and isinstance(c.get("@graph"), list):
                expanded.extend(c["@graph"])
            else:
                expanded.append(c)

        for c in expanded:
            if not isinstance(c, dict):
                continue
            t = c.get("@type")
            is_job = t == "JobPosting" or (isinstance(t, list) and "JobPosting" in t)
            if not is_job:
                continue

            title = c.get("title", "")
            location = _jsonld_location(c.get("jobLocation"))
            if c.get("jobLocationType") == "TELECOMMUTE" or c.get("applicantLocationRequirements"):
                location = f"{location} (Remote)".strip(", ")

            if region_ok(location):
                desc = c.get("description") or ""
                out.append({
                    "company": company,
                    "ats": "jsonld",
                    "title": title,
                    "location": location,
                    "url": c.get("url") or url,
                    "updated_at": c.get("datePosted"),
                    "description_text": _strip_html(desc) if isinstance(desc, str) else "",
                })
    return out


def scrape_adzuna(country: str, query: str):
    if not ADZUNA_APP_ID or not ADZUNA_APP_KEY:
        return []
    url = (
        f"https://api.adzuna.com/v1/api/jobs/{country}/search/1"
        f"?app_id={ADZUNA_APP_ID}&app_key={ADZUNA_APP_KEY}"
        f"&what={urllib.parse.quote(query)}&results_per_page=50&content-type=application/json"
    )
    data = fetch_json(url)
    if not data or "results" not in data:
        return []
    out = []
    for j in data["results"]:
        title = j.get("title", "")
        location = (j.get("location") or {}).get("display_name", "")
        if region_ok(location):
            out.append({
                "company": (j.get("company") or {}).get("display_name", "unknown"),
                "ats": "adzuna",
                "title": title,
                "location": location,
                "url": j.get("redirect_url"),
                "updated_at": j.get("created"),
                "description_text": j.get("description") or "",
                "source_type": "aggregator",
            })
    return out


def scrape_careerjet(locale: str, query: str):
    if not CAREERJET_AFFID:
        return []
    url = (
        "https://public-api.careerjet.net/search"
        f"?locale_code={locale}&keywords={urllib.parse.quote(query)}"
        f"&affid={CAREERJET_AFFID}&pagesize=50&user_ip=127.0.0.1&user_agent=job-dashboard-bot"
    )
    data = fetch_json(url)
    if not data or "jobs" not in data:
        return []
    out = []
    for j in data["jobs"]:
        title = j.get("title", "")
        location = j.get("locations", "")
        if region_ok(location):
            out.append({
                "company": j.get("company", "unknown"),
                "ats": "careerjet",
                "title": title,
                "location": location,
                "url": j.get("url"),
                "updated_at": j.get("date"),
                "description_text": j.get("description") or j.get("snippet") or "",
                "source_type": "aggregator",
            })
    return out


def scrape_jooble(keywords: str, location: str = ""):
    if not JOOBLE_API_KEY:
        return []
    url = f"https://jooble.org/api/{JOOBLE_API_KEY}"
    payload = json.dumps({"keywords": keywords, "location": location}).encode("utf-8")
    req = urllib.request.Request(
        url, data=payload, method="POST",
        headers={"Content-Type": "application/json", "User-Agent": "Mozilla/5.0 (job-dashboard-bot)"},
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as e:
        print(f"  ! fetch failed for jooble ({keywords}): {e}")
        return []
    out = []
    for j in (data or {}).get("jobs", []):
        title = j.get("title", "")
        loc = j.get("location", "")
        if region_ok(loc):
            out.append({
                "company": j.get("company", "unknown"),
                "ats": "jooble",
                "title": title,
                "location": loc,
                "url": j.get("link"),
                "updated_at": j.get("updated"),
                "description_text": j.get("snippet") or j.get("description") or "",
                "source_type": "aggregator",
            })
    return out


def scrape_amazon(query: str):
    url = f"https://www.amazon.jobs/en/search.json?base_query={urllib.parse.quote(query)}&result_limit=50&offset=0"
    data = fetch_json(url)
    if not data or "jobs" not in data:
        return []
    out = []
    for j in data["jobs"]:
        title = j.get("title", "")
        location = j.get("normalized_location", "") or j.get("location", "")
        if region_ok(location):
            path = j.get("job_path", "")
            out.append({
                "company": "amazon",
                "ats": "direct",
                "title": title,
                "location": location,
                "url": f"https://www.amazon.jobs{path}" if path else None,
                "updated_at": j.get("posted_date"),
            })
    return out


def scrape_netflix(query: str):
    url = (
        "https://explore.jobs.netflix.net/api/apply/v2/jobs"
        f"?domain=netflix.com&start=0&num=50&query={urllib.parse.quote(query)}"
    )
    data = fetch_json(url)
    if not data:
        return []
    positions = data.get("positions") or []
    out = []
    for j in positions:
        title = j.get("name", "")
        location = j.get("location", "")
        if region_ok(location):
            t_update = j.get("t_update")
            updated_iso = None
            if t_update:
                try:
                    updated_iso = datetime.fromtimestamp(t_update, tz=timezone.utc).isoformat()
                except Exception:
                    pass
            out.append({
                "company": "netflix",
                "ats": "direct",
                "title": title,
                "location": location,
                "url": j.get("canonicalPositionUrl"),
                "updated_at": updated_iso,
            })
    return out



def _fetch_html(url: str, timeout: int = 25):
    if requests is None:
        return ""
    try:
        r = requests.get(url, headers={"User-Agent": "Mozilla/5.0 (compatible; IrelandJobSearch/3.0)"}, timeout=timeout)
        if r.status_code != 200:
            return ""
        return r.text
    except Exception:
        return ""


def _html_text(fragment: str) -> str:
    return re.sub(r"\\s+", " ", html.unescape(_strip_html(fragment or ""))).strip()


def _absolute_url(base: str, href: str) -> str:
    return urllib.parse.urljoin(base, href or "")


def scrape_apple():
    """Apple's Ireland search is server-rendered enough to parse without login/API keys."""
    base = "https://jobs.apple.com"
    url = base + "/en-ie/search?location=ireland-IRL"
    page = _fetch_html(url)
    if not page:
        return []
    out=[]
    # Each result links to /en-ie/details/<role-number>/<slug>. Capture the
    # surrounding list-item/card so location/date/description can be extracted.
    blocks = re.findall(r"(<li[^>]*>.*?/en-ie/details/.*?</li>)", page, flags=re.I|re.S)
    if not blocks:
        blocks = re.split(r'(?=<a[^>]+href=["\\\']/en-ie/details/)', page, flags=re.I)
    seen=set()
    for block in blocks:
        m=re.search(r'href=["\\\']([^"\\\']*/en-ie/details/[^"\\\']+)["\\\'][^>]*>(.*?)</a>', block, flags=re.I|re.S)
        if not m:
            continue
        href=_absolute_url(base,m.group(1)); title=_html_text(m.group(2))
        if not title or href in seen:
            continue
        seen.add(href)
        txt=_html_text(block)
        lm=re.search(r'Location\\s+([^|•]+?)(?:Actions|Role Number|Weekly Hours|$)', txt, flags=re.I)
        location=(lm.group(1).strip() if lm else "Ireland")
        if not region_ok(location):
            continue
        dm=re.search(r'\\b(\\d{1,2}\\s+[A-Za-z]{3}\\s+20\\d{2}|[A-Za-z]{3}\\s+\\d{1,2},?\\s+20\\d{2})\\b', txt)
        out.append({"company":"Apple","ats":"direct","title":title,"location":location,"url":href,"updated_at":dm.group(1) if dm else None,"description_text":txt[:5000]})
    return out


def _scrape_public_careers_page(company: str, url: str, href_hints, default_location="Ireland"):
    """Conservative server-rendered careers-page parser for proprietary sites.

    Only emits cards whose surrounding text clearly contains an Irish location.
    It is a fallback, not a claim that every JS-only site is fully covered.
    """
    page=_fetch_html(url)
    if not page:
        return []
    out=[]; seen=set()
    # Work with bounded chunks around anchors so one Ireland mention elsewhere on
    # the page cannot incorrectly tag a non-Ireland role.
    for m in re.finditer(r'<a\\b[^>]*href=["\\\']([^"\\\']+)["\\\'][^>]*>(.*?)</a>', page, flags=re.I|re.S):
        href=m.group(1); label=_html_text(m.group(2))
        if not label or len(label)<3 or len(label)>220:
            continue
        full=_absolute_url(url,href)
        low=full.lower()
        if not any(h in low for h in href_hints):
            continue
        start=max(0,m.start()-1800); end=min(len(page),m.end()+2600)
        chunk=_html_text(page[start:end])
        if not region_ok(chunk):
            continue
        # Prefer a compact location phrase if visible.
        lm=re.search(r'((?:Dublin|Cork|Galway|Limerick|Waterford|Kilkenny|Athlone|Ireland)(?:[^|•<>]{0,80}))', chunk, flags=re.I)
        location=lm.group(1).strip()[:140] if lm else default_location
        key=(label.lower(),full.split('?')[0])
        if key in seen:
            continue
        seen.add(key)
        dm=re.search(r'\\b(20\\d{2}-\\d{2}-\\d{2}|\\d{1,2}\\s+[A-Za-z]{3,9}\\s+20\\d{2}|[A-Za-z]{3,9}\\s+\\d{1,2},?\\s+20\\d{2})\\b', chunk)
        out.append({"company":company,"ats":"direct","title":label,"location":location,"url":full,"updated_at":dm.group(1) if dm else None,"description_text":chunk[:5000]})
    return out


def scrape_google():
    return _scrape_public_careers_page(
        "Google",
        "https://www.google.com/about/careers/applications/jobs/results/?location=Ireland",
        ("/about/careers/applications/jobs/results/", "/jobs/results/"),
    )


def scrape_microsoft():
    # The Dublin location page is server-rendered and currently exposes the
    # Ireland vacancies plus their dates/descriptions.
    return _scrape_public_careers_page(
        "Microsoft",
        "https://careers.microsoft.com/v2/global/en/locations/dublin.html",
        ("/job/", "/jobs/", "jobid", "job-id"),
    )


def scrape_meta():
    return _scrape_public_careers_page(
        "Meta",
        "https://www.metacareers.com/jobs?offices[0]=Dublin%2C%20Ireland",
        ("/jobs/",),
    )


def scrape_tiktok():
    return _scrape_public_careers_page(
        "TikTok",
        "https://careers.tiktok.com/position?keyword=&location=Dublin%2C+Ireland",
        ("/position/", "position/detail", "/jobs/"),
    )


def scrape_oracle():
    # Oracle Recruiting Cloud pages vary by tenant/site. This conservative
    # parser follows publicly rendered requisition links and requires Ireland
    # context in the same local card/chunk.
    return _scrape_public_careers_page(
        "Oracle",
        "https://eeho.fa.us2.oraclecloud.com/hcmUI/CandidateExperience/en/sites/CX_1/requisitions?location=Ireland",
        ("/job/", "/requisitions/", "candidateexperience"),
    )


def scrape_direct_company(company: str):
    fn={
        "Apple": scrape_apple,
        "Google": scrape_google,
        "Microsoft": scrape_microsoft,
        "Meta": scrape_meta,
        "TikTok": scrape_tiktok,
        "Oracle": scrape_oracle,
    }.get(company)
    return fn() if fn else []


RESUME_MATCH_STOPWORDS = {
    "the","and","for","with","that","this","from","your","you","our","are","will","have","has","job","role","work","team","company","candidate","candidates","skills","skill","experience","years","year","including","within","across","using","into","about","more","their","they","them","who","what","when","where","which","while","also","all","any","but","not","can","may","must","should","would","could","a","an","as","at","be","by","in","is","it","of","on","or","to","we","i","us"
}

def resume_match_keywords(*parts, limit=60):
    """Return compact, generic searchable terms for browser-side CV/job matching.
    Descriptions are intentionally not shipped wholesale to keep data.json smaller.
    """
    text = " ".join(str(p or "") for p in parts).lower()
    tokens = re.findall(r"[a-z][a-z0-9+#.\-]{2,}", text)
    counts = {}
    for token in tokens:
        token = token.strip(".-")
        if len(token) < 3 or token in RESUME_MATCH_STOPWORDS or token.isdigit():
            continue
        counts[token] = counts.get(token, 0) + 1
    # Stable weighting: repeated description terms first, then alphabetically.
    return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:limit]]


def load_candidate_profile(path="profile.json"):
    """Load optional ranking profile. Collection remains profile-agnostic."""
    try:
        with open(path, encoding="utf-8") as f:
            profile = json.load(f)
        return profile if isinstance(profile, dict) else {}
    except Exception as e:
        print(f"profile: unavailable ({e}); candidate ranking disabled")
        return {}


def _norm_phrase(text):
    return re.sub(r"[^a-z0-9+#]+", " ", str(text or "").lower()).strip()


def normalized_title(title):
    text = _norm_phrase(title)
    replacements = {
        "business intelligence": "bi",
        "jr ": "junior ",
        "graduate programme": "graduate",
        "graduate program": "graduate",
    }
    for a, b in replacements.items():
        text = text.replace(a, b)
    return re.sub(r"\s+", " ", text).strip()


def classify_role_family(title, description, profile):
    title_n = normalized_title(title)
    text = f"{title_n} {_norm_phrase(description)}"
    best = ("Other", "None", 0, [])
    for family, cfg in (profile.get("role_families") or {}).items():
        hits = []
        for phrase in cfg.get("titles", []):
            p = _norm_phrase(phrase)
            if p and (p in title_n or (len(p.split()) >= 2 and p in text)):
                hits.append(phrase)
        score = cfg.get("weight", 0) + min(8, len(hits) * 2) if hits else 0
        if score > best[2]:
            best = (family, cfg.get("tier", "C"), score, hits)
    return {"family": best[0], "tier": best[1], "role_score": best[2], "role_hits": best[3]}


def extract_profile_skills(text, profile):
    text_n = _norm_phrase(text)
    aliases = profile.get("skill_aliases") or {}
    canonical = {}
    for group, skills in (profile.get("skills") or {}).items():
        for skill in skills:
            canonical[_norm_phrase(skill)] = skill
    for alias, target in aliases.items():
        canonical[_norm_phrase(alias)] = target

    found = []
    for token, label in canonical.items():
        if token and re.search(r"(?<![a-z0-9])" + re.escape(token) + r"(?![a-z0-9])", text_n):
            if label not in found:
                found.append(label)
    return found


def parse_experience_range(text):
    text_n = str(text or "").lower()
    ranges = []
    patterns = [
        r"(\d+)\s*(?:-|–|to)\s*(\d+)\s*\+?\s*years?",
        r"(\d+)\s*\+\s*years?",
        r"(?:minimum of |at least )(\d+)\s*years?",
        r"(\d+)\s*years?\s+(?:of )?experience",
    ]
    for pat in patterns:
        for m in re.finditer(pat, text_n):
            nums = [int(x) for x in m.groups() if x is not None]
            if len(nums) == 2:
                ranges.append((nums[0], nums[1]))
            elif nums:
                ranges.append((nums[0], nums[0] + 2))
    if not ranges:
        return (None, None)
    # Prefer the lowest plausible requirement, since descriptions often mention multiple unrelated ranges.
    ranges.sort(key=lambda x: (x[0], x[1]))
    return ranges[0]


def experience_fit(title, description, candidate_years):
    title_n = normalized_title(title)
    minimum, maximum = parse_experience_range(description)
    senior_terms = ["director", "vice president", "vp", "head of", "principal", "staff", "senior manager"]
    if any(term in title_n for term in senior_terms):
        return "Too Senior", minimum, maximum
    if any(term in title_n for term in ["graduate", "entry", "junior", "associate", "analyst"]):
        if candidate_years >= 5 and "graduate" in title_n:
            return "Overqualified", minimum, maximum
        return "Strong", minimum, maximum
    if minimum is None:
        return "Possible", minimum, maximum
    if minimum <= candidate_years <= (maximum or candidate_years + 2):
        return "Strong", minimum, maximum
    if minimum <= candidate_years + 2:
        return "Possible", minimum, maximum
    if minimum <= candidate_years + 4:
        return "Stretch", minimum, maximum
    return "Too Senior", minimum, maximum


def candidate_match(job, description, profile):
    if not profile:
        return {
            "candidate_match_score": None, "match_reasons": [], "missing_skills": [],
            "matched_skills": [], "experience_fit": "Unknown"
        }

    title = job.get("title") or ""
    role = classify_role_family(title, description, profile)
    skills = extract_profile_skills(f"{title} {description}", profile)
    candidate_skills = []
    for values in (profile.get("skills") or {}).values():
        candidate_skills.extend(values)
    candidate_skill_set = set(candidate_skills)

    matched = [s for s in skills if s in candidate_skill_set]
    years = int(profile.get("experience_years") or 0)
    exp_fit, exp_min, exp_max = experience_fit(title, description, years)

    score = role["role_score"]
    score += min(34, len(matched) * 4)
    score += {"Strong": 16, "Possible": 9, "Stretch": 3, "Overqualified": -5, "Too Senior": -25, "Unknown": 0}.get(exp_fit, 0)

    loc_text = _norm_phrase(job.get("location"))
    if any(_norm_phrase(x) in loc_text for x in profile.get("preferred_locations", []) if x != "Ireland"):
        score += 5
    elif "ireland" in loc_text or job.get("country") == "Ireland":
        score += 3

    title_n = normalized_title(title)
    for term, penalty in (profile.get("seniority_penalties") or {}).items():
        if _norm_phrase(term) in title_n:
            score -= int(penalty)
            break

    # Noise penalty for clearly irrelevant job families, without deleting the job from the broad engine.
    for term in profile.get("negative_title_terms", []):
        if _norm_phrase(term) in title_n:
            score -= 18
            break

    score = max(0, min(100, int(round(score))))
    reasons = []
    if role["family"] != "Other":
        reasons.append(f"{role['family']} role family")
    reasons.extend(matched[:7])
    if exp_fit in {"Strong", "Possible"}:
        reasons.append(f"Experience fit: {exp_fit}")

    # Missing skills are candidate skills commonly referenced in the same role family but not present in this ad.
    priority_missing = ["SQL", "Power BI", "Python", "ERP", "UAT", "Requirements Gathering", "ETL", "Stakeholder Management"]
    missing = [x for x in priority_missing if x in candidate_skill_set and x not in matched][:4]

    return {
        "candidate_match_score": score,
        "match_reasons": reasons[:10],
        "missing_skills": missing,
        "matched_skills": matched[:15],
        "experience_fit": exp_fit,
        "experience_min": exp_min,
        "experience_max": exp_max,
        "role_family": role["family"],
        "role_tier": role["tier"],
        "normalized_title": normalized_title(title),
    }


def discovery_value(job, now_dt=None):
    """Value of discovering the listing, independent of candidate fit."""
    now_dt = now_dt or datetime.now(timezone.utc)
    score = 25
    source = (job.get("ats") or "").lower()
    directish = {"direct", "workday", "greenhouse", "lever", "ashby", "smartrecruiters",
                 "workable", "recruitee", "personio", "pinpoint", "phenom", "eightfold"}
    if source in directish:
        score += 20
    first_seen = job.get("first_seen_at")
    try:
        dt = datetime.fromisoformat(first_seen.replace("Z", "+00:00")) if first_seen else None
    except Exception:
        dt = None
    if dt:
        hours = max(0, (now_dt - dt).total_seconds() / 3600)
        if hours <= 24:
            score += 25
        elif hours <= 72:
            score += 15
        elif hours <= 168:
            score += 7
    if job.get("new_since_last_check"):
        score += 12
    if job.get("closing_date"):
        try:
            close_dt = datetime.fromisoformat(str(job["closing_date"]).replace("Z", "+00:00"))
            days = (close_dt - now_dt).total_seconds() / 86400
            if 0 <= days <= 7:
                score += 15
        except Exception:
            pass
    return max(0, min(100, int(score)))


def job_state_identity(job):
    stable_url = (job.get("url") or "").split("?")[0].rstrip("/").lower()
    if stable_url:
        return stable_url
    return "|".join([
        _company_key(job.get("company", "")),
        normalized_title(job.get("title")),
        _norm_phrase(job.get("location")),
    ])

def main():
    profile = load_candidate_profile()
    results = []
    errors = []

    for slug in GREENHOUSE_COMPANIES:
        try:
            found = scrape_greenhouse(slug)
            results.extend(found)
            print(f"greenhouse/{slug}: {len(found)} matches")
        except Exception as e:
            errors.append(f"greenhouse/{slug}: {e}")
        time.sleep(0.3)

    for slug in LEVER_COMPANIES:
        try:
            found = scrape_lever(slug)
            results.extend(found)
            print(f"lever/{slug}: {len(found)} matches")
        except Exception as e:
            errors.append(f"lever/{slug}: {e}")
        time.sleep(0.3)

    for slug in ASHBY_COMPANIES:
        try:
            found = scrape_ashby(slug)
            results.extend(found)
            print(f"ashby/{slug}: {len(found)} matches")
        except Exception as e:
            errors.append(f"ashby/{slug}: {e}")
        time.sleep(0.3)

    for company, tenant, wd_host, site in WORKDAY_COMPANIES:
        try:
            found = scrape_workday(company, tenant, wd_host, site)
            results.extend(found)
            print(f"workday/{tenant}: {len(found)} matches")
        except Exception as e:
            errors.append(f"workday/{tenant}: {e}")
        time.sleep(0.3)

    for company_id in SMARTRECRUITERS_COMPANIES:
        try:
            found = scrape_smartrecruiters(company_id)
            results.extend(found)
            print(f"smartrecruiters/{company_id}: {len(found)} matches")
        except Exception as e:
            errors.append(f"smartrecruiters/{company_id}: {e}")
        time.sleep(0.3)

    for slug in WORKABLE_COMPANIES:
        try:
            found = scrape_workable(slug)
            results.extend(found)
            print(f"workable/{slug}: {len(found)} matches")
        except Exception as e:
            errors.append(f"workable/{slug}: {e}")
        time.sleep(0.3)

    for slug in RECRUITEE_COMPANIES:
        try:
            found = scrape_recruitee(slug)
            results.extend(found)
            print(f"recruitee/{slug}: {len(found)} matches")
        except Exception as e:
            errors.append(f"recruitee/{slug}: {e}")
        time.sleep(0.3)

    for slug in PERSONIO_COMPANIES:
        try:
            found = scrape_personio(slug)
            results.extend(found)
            print(f"personio/{slug}: {len(found)} matches")
        except Exception as e:
            errors.append(f"personio/{slug}: {e}")
        time.sleep(0.3)

    for slug in PINPOINT_COMPANIES:
        try:
            found = scrape_pinpoint(slug)
            results.extend(found)
            print(f"pinpoint/{slug}: {len(found)} Ireland jobs")
        except Exception as e:
            errors.append(f"pinpoint/{slug}: {e}")
        time.sleep(0.3)

    # Exact enterprise-platform mappings (Phenom / Eightfold). Validate before
    # scraping so a stale mapping cannot silently pollute the dataset.
    enterprise_sess = _session()
    if enterprise_sess:
        for company, slug in KNOWN_EIGHTFOLD_MAPPINGS.items():
            try:
                if _probe_platform("eightfold", slug, enterprise_sess):
                    found = _scrape_eightfold(company, slug, enterprise_sess)
                    results.extend(found)
                    print(f"eightfold/{company}: {len(found)} Ireland jobs")
                else:
                    errors.append(f"eightfold/{company}: endpoint validation failed")
            except Exception as e:
                errors.append(f"eightfold/{company}: {e}")
        for company, slug in KNOWN_PHENOM_MAPPINGS.items():
            try:
                if _probe_platform("phenom", slug, enterprise_sess):
                    found = _scrape_phenom(company, slug, enterprise_sess)
                    results.extend(found)
                    print(f"phenom/{company}: {len(found)} Ireland jobs")
                else:
                    errors.append(f"phenom/{company}: endpoint validation failed")
            except Exception as e:
                errors.append(f"phenom/{company}: {e}")

    # Proprietary/direct company search surfaces. These are deliberately
    # conservative and only emit records with local Ireland context.
    for company in ("Apple", "Google", "Microsoft", "Meta", "TikTok", "Oracle"):
        try:
            found = scrape_direct_company(company)
            results.extend(found)
            print(f"direct/{company}: {len(found)} Ireland jobs")
        except Exception as e:
            errors.append(f"direct/{company}: {e}")
        time.sleep(0.4)

    # Suman-style dynamic ATS discovery for companies not already wired into a
    # known connector. Confirmed mappings persist in ats_platform_cache.json.
    initial_registry = build_company_registry(include_cache=False)
    try:
        dynamic_found, _dynamic_mappings = discover_and_scrape_manual(initial_registry)
        results.extend(dynamic_found)
    except Exception as e:
        errors.append(f"dynamic ATS discovery: {e}")

    for company, url in JSONLD_CAREER_PAGES:
        if IRELAND_ONLY and not jsonld_page_is_ireland(company, url):
            continue
        try:
            found = scrape_jsonld(company, url)
            results.extend(found)
            print(f"jsonld/{company}: {len(found)} matches")
        except Exception as e:
            errors.append(f"jsonld/{company}: {e}")
        time.sleep(0.3)

    for country in ADZUNA_COUNTRIES:
        for query in DIRECT_QUERIES:
            try:
                found = scrape_adzuna(country, query)
                results.extend(found)
                if found:
                    print(f"adzuna/{country} ({query}): {len(found)} matches")
            except Exception as e:
                errors.append(f"adzuna/{country} ({query}): {e}")
            time.sleep(0.3)

    for locale in CAREERJET_LOCALES:
        for query in DIRECT_QUERIES:
            try:
                found = scrape_careerjet(locale, query)
                results.extend(found)
                if found:
                    print(f"careerjet/{locale} ({query}): {len(found)} matches")
            except Exception as e:
                errors.append(f"careerjet/{locale} ({query}): {e}")
            time.sleep(0.3)

    for query in DIRECT_QUERIES:
        try:
            found = scrape_jooble(query, "Ireland" if IRELAND_ONLY else "")
            results.extend(found)
            if found:
                print(f"jooble ({query}): {len(found)} matches")
        except Exception as e:
            errors.append(f"jooble ({query}): {e}")
        time.sleep(0.3)

    try:
        found = scrape_amazon("")
        results.extend(found)
        print(f"direct/Amazon: {len(found)} Ireland jobs")
    except Exception as e:
        errors.append(f"direct/Amazon: {e}")
    time.sleep(0.5)

    try:
        found = scrape_netflix("")
        results.extend(found)
        print(f"direct/Netflix: {len(found)} Ireland jobs")
    except Exception as e:
        errors.append(f"direct/Netflix: {e}")
    time.sleep(0.5)

    # Source-priority de-duplication. Direct employer/ATS records win over
    # aggregator copies of the same vacancy.
    source_priority = {
        "direct": 100, "workday": 95, "greenhouse": 95, "lever": 95, "ashby": 95,
        "smartrecruiters": 95, "workable": 94, "recruitee": 94, "personio": 94,
        "pinpoint": 94, "phenom": 93, "eightfold": 93, "jsonld": 90,
        "adzuna": 30, "jooble": 25, "careerjet": 20,
    }
    aggregator_sources = {"adzuna", "jooble", "careerjet"}
    results.sort(key=lambda j: source_priority.get((j.get("ats") or "").lower(), 50), reverse=True)

    seen_urls = set()
    seen_signatures = set()
    deduped = []
    for j in results:
        company_key = _company_key(company_display_name(j.get("company", "")))
        url_key = (j.get("url") or "").split("?")[0].rstrip("/").lower()
        title_key = normalized_title(j.get("title"))
        loc_key = _norm_phrase(j.get("location"))
        signature = (company_key, title_key, loc_key)
        source = (j.get("ats") or "").lower()

        if url_key and url_key in seen_urls:
            continue
        if source in aggregator_sources and signature in seen_signatures:
            continue

        deduped.append(j)
        if url_key:
            seen_urls.add(url_key)
        if any(signature):
            seen_signatures.add(signature)

    results = deduped

    # Tag every job with a parsed posting date + recency bucket, so the
    # dashboard can filter by "last 24h / 7d / 30d" without re-parsing.
    for j in results:
        j["company"] = company_display_name(j.get("company", ""))
        posted_dt = parse_posted_date(j.get("updated_at"))
        j["posted_at_parsed"] = posted_dt.isoformat() if posted_dt else None
        j["recency"] = recency_bucket(posted_dt)
        j["employment_type"] = employment_type(j.get("title"))
        j["sector"] = sector_for(j.get("company"))
        j["country"] = "Ireland" if IRELAND_ONLY else country_from_location(j.get("location"))
        j["ireland_area"] = ireland_area(j.get("location"))
        description_text = j.get("description_text") or ""
        j["visa_sponsorship"] = visa_sponsorship_from_text(
            j.get("title"), j.get("location"), description_text,
        )
        # Generic CV/job matching metadata. No user-profile-specific title filtering.
        j["match_keywords"] = resume_match_keywords(
            j.get("title"), j.get("company"), j.get("sector"), j.get("location"), description_text
        )
        # Broad collection stays untouched; profile ranking is metadata only.
        j.update(candidate_match(j, description_text, profile))
        j.setdefault("work_mode", "remote" if "remote" in (j.get("location") or "").lower()
                     else "hybrid" if "hybrid" in (j.get("location") or "").lower() else "unspecified")
        j.setdefault("closing_date", None)
        j.setdefault("requisition_id", None)
        j.setdefault("salary", None)
        if not j.get("source_type"):
            j["source_type"] = (
                "employer_direct"
                if (j.get("ats") or "").lower() in
                {"direct","workday","greenhouse","lever","ashby","smartrecruiters",
                 "workable","recruitee","personio","pinpoint","phenom","eightfold","jsonld"}
                else "aggregator" if (j.get("ats") or "").lower() in {"adzuna","jooble","careerjet"}
                else "other"
            )
        j.pop("description_text", None)

    # Persistent freshness state: supports old {id: "timestamp"} files and richer v2 objects.
    now_dt = datetime.now(timezone.utc)
    now_iso = now_dt.isoformat()
    try:
        with open("seen_jobs.json", encoding="utf-8") as f:
            seen_jobs = json.load(f)
        if not isinstance(seen_jobs, dict):
            seen_jobs = {}
    except Exception:
        seen_jobs = {}

    current_seen = dict(seen_jobs)
    for j in results:
        identity = job_state_identity(j)
        prior = seen_jobs.get(identity)
        if isinstance(prior, dict):
            first_seen = prior.get("first_seen") or prior.get("first_seen_at") or now_iso
        elif isinstance(prior, str):
            first_seen = prior
        else:
            first_seen = now_iso

        j["new_since_last_check"] = prior is None
        j["first_seen_at"] = first_seen
        j["last_seen_at"] = now_iso
        j["last_verified_at"] = now_iso
        j["active"] = True
        j["discovery_score"] = discovery_value(j, now_dt)

        current_seen[identity] = {
            "first_seen": first_seen,
            "last_seen": now_iso,
            "last_verified": now_iso,
            "company": j.get("company"),
            "title": j.get("title"),
        }

    with open("seen_jobs.json", "w", encoding="utf-8") as f:
        json.dump(current_seen, f, indent=2)

    company_registry = build_company_registry(include_cache=True)

    manual_check = []
    for item in company_registry:
        if item["automatic"]:
            continue
        manual_check.append({
            "company": item["company"],
            "url": item["careers_url"],
            "platform": item["platform"],
            "status": "manual-check" if item["careers_url"] else "needs-careers-url",
        })
    manual_check.sort(key=lambda x: x["company"].lower())

    if MAX_AGE_DAYS is not None:
        cutoff = datetime.now(timezone.utc) - timedelta(days=MAX_AGE_DAYS)
        before = len(results)
        results = [
            j for j in results
            if not j["posted_at_parsed"] or datetime.fromisoformat(j["posted_at_parsed"]) >= cutoff
        ]
        print(f"MAX_AGE_DAYS={MAX_AGE_DAYS}: dropped {before - len(results)} stale postings")

    recency_counts = {"24h": 0, "7d": 0, "30d": 0, "older": 0, "unknown": 0}
    for j in results:
        recency_counts[j["recency"]] += 1

    source_counts = {}
    company_job_counts = {}
    for j in results:
        source_counts[j.get("ats") or "unknown"] = source_counts.get(j.get("ats") or "unknown", 0) + 1
        company_job_counts[j.get("company") or "Unknown"] = company_job_counts.get(j.get("company") or "Unknown", 0) + 1

    # Coverage diagnostics. "No live jobs" is not automatically the same as
    # "the company has no jobs"; distinguish missing connectors from configured
    # connectors that yielded no Ireland records.
    live_company_keys = {_company_key(name) for name in company_job_counts}
    coverage_diagnostics = []
    for item in company_registry:
        key = _company_key(item["company"])
        if key in live_company_keys:
            state = "working"
            reason = "Ireland jobs returned in this run"
        elif item.get("automatic"):
            state = "configured_zero"
            reason = "Connector is configured but returned no qualifying Ireland jobs; mapping/filter may need verification"
        else:
            state = "no_validated_connector"
            reason = "No validated automatic connector yet"
        coverage_diagnostics.append({
            "company": item["company"],
            "platform": item.get("platform"),
            "state": state,
            "reason": reason,
            "careers_url": item.get("careers_url"),
        })

    output = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "focus": "ireland" if IRELAND_ONLY else "multi_region",
        "integrations": {
            "adzuna": bool(ADZUNA_APP_ID and ADZUNA_APP_KEY),
            "jooble": bool(JOOBLE_API_KEY),
            "careerjet": bool(CAREERJET_AFFID),
        },
        "ranking_profile": {
            "profile_id": profile.get("profile_id"),
            "version": profile.get("version"),
            "name": profile.get("name"),
        } if profile else None,
        "recency_counts": recency_counts,
        "total_companies_checked": len(company_registry),
        "registry_companies": company_registry,
        "total_matches": len(results),
        "new_since_last_check": sum(1 for j in results if j.get("new_since_last_check")),
        "source_counts": source_counts,
        "companies_with_live_jobs": len(company_job_counts),
        "company_job_counts": company_job_counts,
        "coverage_diagnostics": coverage_diagnostics,
        "coverage_state_counts": {
            state: sum(1 for x in coverage_diagnostics if x["state"] == state)
            for state in ("working", "configured_zero", "no_validated_connector")
        },
        "manual_check_companies": manual_check,
        "manual_check_count": len(manual_check),
        "automatic_company_count": sum(1 for x in company_registry if x["automatic"]),
        "companies_with_careers_url": sum(1 for x in company_registry if x["careers_url"]),
        "errors": errors,
        "jobs": results,
        "note": (
            "Broad Ireland job-data engine with persistent ATS discovery and optional "
            "profile-aware ranking metadata. Collection is profile-agnostic; personalization "
            "is applied after normalization so all jobs remain available."
        ),
    }

    with open("data.json", "w") as f:
        json.dump(output, f, indent=2)

    print(f"\nDone. {len(results)} matching jobs written to data.json ({len(errors)} companies errored).")


if __name__ == "__main__":
    main()
