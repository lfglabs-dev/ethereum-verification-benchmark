"""Publication constants for generated release artifacts."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.identity import BADGE_LABEL, BENCHMARK_ID, BENCHMARK_TITLE, HARNESS_USER_AGENT

GITHUB_OWNER = "lfglabs-dev"
GITHUB_REPO = BENCHMARK_ID
GITHUB_REPO_SLUG = f"{GITHUB_OWNER}/{GITHUB_REPO}"
GITHUB_REPO_URL = f"https://github.com/{GITHUB_REPO_SLUG}"
RAW_MAIN_URL = f"https://raw.githubusercontent.com/{GITHUB_REPO_SLUG}/main"
PUBLIC_DASHBOARD_URL = "https://lfglabs.dev/benchmark"
