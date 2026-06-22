#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = Path(os.environ.get("MINIMAX_CASCADE_OUTPUT", ROOT / "analysis" / "budget_scaling_minimax_remaining_85"))
PROFILES = [
    "p01_ultra_tiny",
    "p02_tiny",
    "p03_ultra_cheap",
    "p04_cheap",
    "p05_quick_minus",
    "p06_quick",
    "p07_medium",
    "p08_normal",
    "p09_high",
    "p10_ultra_high",
]


def load_json(path: Path, default):
    if not path.is_file():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def pid_alive(path: Path) -> tuple[str, bool]:
    if not path.is_file():
        return "", False
    pid = path.read_text(encoding="utf-8").strip()
    if not pid.isdigit():
        return pid, False
    result = subprocess.run(["kill", "-0", pid], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return pid, result.returncode == 0


def valid_model_row(row: dict) -> bool:
    if row.get("skipped_already_solved"):
        return True
    if row.get("provider_setup_error"):
        return False
    if int(row.get("requests") or 0) > 0:
        return True
    return bool(row.get("passed"))


def main() -> int:
    selected = load_json(OUTPUT / "selected_tasks.json", [])
    rows = load_json(OUTPUT / "cascade_results.json", [])
    summary = load_json(OUTPUT / "cascade_summary.json", [])
    task_count = len(selected)
    valid_rows = [row for row in rows if valid_model_row(row)]
    invalid_rows = [row for row in rows if not valid_model_row(row)]
    solved = {row["task_ref"] for row in valid_rows if row.get("passed")}

    supervisor_pid, supervisor_alive = pid_alive(OUTPUT / "supervisor.pid")
    runner_pid, runner_alive = pid_alive(OUTPUT / "cascade.pid")

    print(f"output: {OUTPUT}")
    print(f"supervisor: {'alive' if supervisor_alive else 'down'} {supervisor_pid}".rstrip())
    print(f"runner: {'alive' if runner_alive else 'down'} {runner_pid}".rstrip())
    print("worker slots: 4 when launched by supervise_minimax_complement_cascade.sh")
    print(f"selected tasks: {task_count}")
    print(f"valid result rows: {len(valid_rows)}")
    print(f"invalid result rows: {len(invalid_rows)}")
    print(f"solved complement tasks: {len(solved)}/{task_count if task_count else 85}")

    latest_profile = ""
    if valid_rows:
        latest_profile = max((row.get("profile", "") for row in valid_rows), key=lambda profile: PROFILES.index(profile) if profile in PROFILES else -1)

    if summary and latest_profile:
        last = next((item for item in summary if item.get("profile") == latest_profile), summary[-1])
        print(
            "latest profile with valid rows: "
            f"{last.get('profile')} rows={last.get('executed_tasks')} "
            f"cumulative_solved={last.get('cumulative_solved')} "
            f"requests={last.get('cumulative_requests')} "
            f"tokens={last.get('cumulative_total_tokens')}"
        )
    else:
        print("latest profile with valid rows: none yet")

    by_profile = {profile: 0 for profile in PROFILES}
    for row in valid_rows:
        profile = row.get("profile")
        if profile in by_profile and not row.get("skipped_already_solved"):
            by_profile[profile] += 1
    profile_progress = ", ".join(f"{profile}={count}" for profile, count in by_profile.items() if count)
    print(f"profile rows: {profile_progress or 'none yet'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
