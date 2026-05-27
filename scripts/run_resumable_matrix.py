#!/usr/bin/env python3
"""Resumable benchmark matrix runner.

Runs every task in the active suite against each configured profile.
Skips (task, profile) combos that already have a result file, so the
script can be re-invoked after interruption (rate-limit, crash, etc.)
to continue where it left off.

Logs progress to `results/matrix_runs/<run_id>/progress.jsonl` and
emits a summary at `results/matrix_runs/<run_id>/summary.json` after
every completed task — so even a partial run leaves analyzable output.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def utc_now() -> str:
    return datetime.now(tz=timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def load_profile(profile_name: str) -> dict:
    path = ROOT / "harness" / "agents" / f"{profile_name}.json"
    return json.loads(path.read_text(encoding="utf-8"))


def result_file_for(profile: dict, task_ref: str) -> Path:
    track = profile.get("track", "custom")
    slug = profile.get("run_slug", profile.get("agent_id", "unknown"))
    safe_task = task_ref.replace("/", "__")
    return ROOT / "results" / "agent_runs" / track / slug / f"{safe_task}.json"


def list_active_tasks() -> list[str]:
    env = os.environ.copy()
    env["PYTHONPATH"] = str(ROOT / "harness") + os.pathsep + env.get("PYTHONPATH", "")
    result = subprocess.run(
        ["python3", "harness/agent_runner.py", "list", "--suite", "active"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    if result.returncode != 0:
        print("failed to list tasks:", result.stderr, file=sys.stderr)
        sys.exit(1)
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def run_one(
    profile_name: str,
    task_ref: str,
    *,
    timeout_seconds: int,
    extra_env: dict[str, str] | None = None,
) -> tuple[int, str, str, float]:
    """Run one task; return (exit_code, stdout, stderr, elapsed)."""
    env = os.environ.copy()
    if extra_env:
        env.update(extra_env)
    # Ensure lake is on PATH. Use the invoking user's HOME rather than a
    # hard-coded "/root/.elan/bin" so non-root shells (local dev, CI runners)
    # still pick up elan-installed toolchains.
    elan_bin = os.path.join(env.get("HOME") or os.path.expanduser("~"), ".elan", "bin")
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
    cmd = [
        "bash",
        "scripts/exec_with_dotenvx.sh",
        "python3",
        "harness/agent_runner.py",
        "run",
        task_ref,
        "--profile",
        profile_name,
    ]
    start = time.perf_counter()
    try:
        result = subprocess.run(
            cmd,
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
            env=env,
            timeout=timeout_seconds,
        )
        elapsed = time.perf_counter() - start
        return result.returncode, result.stdout, result.stderr, elapsed
    except subprocess.TimeoutExpired as e:
        elapsed = time.perf_counter() - start
        return 124, e.stdout or "", (e.stderr or "") + f"\n[runner] timeout after {timeout_seconds}s", elapsed


def classify_failure(stderr: str, exit_code: int) -> str:
    low = (stderr or "").lower()
    if exit_code == 124:
        return "timeout"
    if "rate limit" in low or "429" in low or "rate_limit" in low or "too many requests" in low:
        return "rate_limited"
    if "401" in low or "unauthorized" in low or "invalid_api_key" in low:
        return "auth_error"
    if "connection" in low and ("refused" in low or "reset" in low or "timed out" in low):
        return "connection_error"
    if exit_code != 0:
        return "harness_error"
    return "ok"


def read_result(path: Path) -> dict | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def summarize(run_dir: Path, profiles: list[str], tasks: list[str]) -> dict:
    summary: dict = {
        "generated_at": utc_now(),
        "profiles": {},
        "total_tasks": len(tasks),
    }
    for name in profiles:
        try:
            profile = load_profile(name)
        except Exception as e:
            summary["profiles"][name] = {"error": f"cannot load profile: {e}"}
            continue
        counts = {"passed": 0, "failed": 0, "missing": 0, "error": 0}
        details = []
        for task in tasks:
            path = result_file_for(profile, task)
            if not path.exists():
                counts["missing"] += 1
                details.append({"task": task, "state": "missing"})
                continue
            r = read_result(path)
            if not r:
                counts["error"] += 1
                details.append({"task": task, "state": "unreadable"})
                continue
            ev = r.get("evaluation") or {}
            status = ev.get("status", "unknown")
            if status == "passed":
                counts["passed"] += 1
            else:
                counts["failed"] += 1
            details.append(
                {
                    "task": task,
                    "state": status,
                    "failure_mode": ev.get("failure_mode"),
                    "elapsed_seconds": r.get("elapsed_seconds"),
                    "tool_calls_used": r.get("tool_calls_used"),
                }
            )
        summary["profiles"][name] = {
            "track": profile.get("track"),
            "run_slug": profile.get("run_slug"),
            "model": profile.get("model"),
            "counts": counts,
            "pass_rate": (counts["passed"] / len(tasks)) if tasks else None,
            "tasks": details,
        }
    return summary


def write_summary(run_dir: Path, profiles: list[str], tasks: list[str]) -> None:
    s = summarize(run_dir, profiles, tasks)
    (run_dir / "summary.json").write_text(json.dumps(s, indent=2), encoding="utf-8")


def append_progress(run_dir: Path, record: dict) -> None:
    with (run_dir / "progress.jsonl").open("a", encoding="utf-8") as f:
        f.write(json.dumps(record) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", nargs="+", required=True, help="Agent profile names")
    parser.add_argument("--run-id", default=None, help="Run id (default: timestamp)")
    parser.add_argument("--timeout", type=int, default=600, help="Per-task timeout (s)")
    parser.add_argument(
        "--rate-limit-backoff",
        type=int,
        default=60,
        help="Seconds to pause after a rate-limit error before continuing to next task",
    )
    parser.add_argument(
        "--max-rate-limits-per-profile",
        type=int,
        default=5,
        help="Skip remaining tasks for a profile after N rate-limit hits in a row",
    )
    parser.add_argument(
        "--tasks",
        nargs="*",
        default=None,
        help="Specific tasks to run; defaults to the full active suite",
    )
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    run_id = args.run_id or datetime.now().strftime("matrix-%Y%m%d-%H%M%S")
    run_dir = ROOT / "results" / "matrix_runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    tasks = args.tasks or list_active_tasks()
    print(f"[runner] run_id={run_id} profiles={args.profiles} tasks={len(tasks)}")
    append_progress(
        run_dir,
        {
            "event": "run_start",
            "ts": utc_now(),
            "profiles": args.profiles,
            "task_count": len(tasks),
            "run_id": run_id,
        },
    )

    # Initial summary snapshot so partial runs always leave analyzable output.
    write_summary(run_dir, args.profiles, tasks)

    for profile_name in args.profiles:
        try:
            profile = load_profile(profile_name)
        except Exception as e:
            print(f"[runner] cannot load profile {profile_name}: {e}", file=sys.stderr)
            append_progress(
                run_dir,
                {"event": "profile_error", "ts": utc_now(), "profile": profile_name, "error": str(e)},
            )
            continue

        print(f"[runner] === profile {profile_name} (model={profile.get('model')}) ===")
        append_progress(
            run_dir,
            {"event": "profile_start", "ts": utc_now(), "profile": profile_name, "model": profile.get("model")},
        )

        consecutive_rate_limits = 0
        profile_passed = 0
        profile_failed = 0
        profile_skipped_existing = 0
        profile_errors = 0

        for idx, task_ref in enumerate(tasks, 1):
            result_path = result_file_for(profile, task_ref)
            if result_path.exists():
                r = read_result(result_path)
                # Treat unreadable/corrupted artifacts as missing rather than
                # silently marking the task as SKIP. A previous run may have
                # been interrupted mid-write, leaving a truncated JSON file
                # that `read_result` returns None for. If we trusted the
                # existence check alone, a resumed matrix would silently
                # skip the task and finish with stale `unknown` status
                # entries — the whole point of resume is to fill those gaps,
                # so delete the corrupt artifact and fall through to RUN.
                if r is None:
                    # Keep dry-run read-only: never unlink artifacts when
                    # --dry-run is set; report what a real run would do.
                    if args.dry_run:
                        print(
                            f"[runner]   [{idx:>2}/{len(tasks)}] {task_ref} -> "
                            f"DRY (existing artifact unreadable; would delete and rerun)"
                        )
                        continue
                    try:
                        result_path.unlink()
                    except OSError:
                        pass
                    print(
                        f"[runner]   [{idx:>2}/{len(tasks)}] {task_ref} -> "
                        f"RERUN (existing artifact was unreadable; deleted)"
                    )
                    append_progress(
                        run_dir,
                        {
                            "event": "task_unreadable_rerun",
                            "ts": utc_now(),
                            "profile": profile_name,
                            "task": task_ref,
                        },
                    )
                else:
                    status = r.get("evaluation", {}).get("status", "unknown")
                    print(f"[runner]   [{idx:>2}/{len(tasks)}] {task_ref} -> SKIP (exists, status={status})")
                    append_progress(
                        run_dir,
                        {
                            "event": "task_skip_existing",
                            "ts": utc_now(),
                            "profile": profile_name,
                            "task": task_ref,
                            "status": status,
                        },
                    )
                    profile_skipped_existing += 1
                    if status == "passed":
                        profile_passed += 1
                    else:
                        profile_failed += 1
                    continue

            if args.dry_run:
                print(f"[runner]   [{idx:>2}/{len(tasks)}] {task_ref} -> DRY (would run)")
                continue

            print(f"[runner]   [{idx:>2}/{len(tasks)}] {task_ref} -> RUN")
            append_progress(
                run_dir,
                {"event": "task_start", "ts": utc_now(), "profile": profile_name, "task": task_ref},
            )

            exit_code, stdout, stderr, elapsed = run_one(
                profile_name, task_ref, timeout_seconds=args.timeout
            )

            # Determine outcome
            classified = classify_failure(stderr, exit_code)
            status = None
            failure_mode = None
            if result_path.exists():
                r = read_result(result_path)
                if r:
                    ev = r.get("evaluation") or {}
                    status = ev.get("status")
                    failure_mode = ev.get("failure_mode")

            outcome_record = {
                "event": "task_end",
                "ts": utc_now(),
                "profile": profile_name,
                "task": task_ref,
                "exit_code": exit_code,
                "elapsed_seconds": round(elapsed, 2),
                "classified": classified,
                "evaluation_status": status,
                "failure_mode": failure_mode,
                "stderr_tail": (stderr or "")[-500:],
            }
            append_progress(run_dir, outcome_record)

            short = status or classified
            print(f"[runner]      -> {short} (exit={exit_code}, {elapsed:.1f}s)")

            if status == "passed":
                profile_passed += 1
                consecutive_rate_limits = 0
            elif classified == "rate_limited":
                consecutive_rate_limits += 1
                profile_errors += 1
                print(
                    f"[runner]   rate-limit hit ({consecutive_rate_limits}/"
                    f"{args.max_rate_limits_per_profile}), sleeping {args.rate_limit_backoff}s"
                )
                time.sleep(args.rate_limit_backoff)
                if consecutive_rate_limits >= args.max_rate_limits_per_profile:
                    print(
                        f"[runner]   too many rate limits for {profile_name}; "
                        f"skipping remaining {len(tasks) - idx} tasks for this profile"
                    )
                    append_progress(
                        run_dir,
                        {
                            "event": "profile_rate_limit_skip",
                            "ts": utc_now(),
                            "profile": profile_name,
                            "remaining": len(tasks) - idx,
                        },
                    )
                    break
            elif result_path.exists():
                profile_failed += 1
                consecutive_rate_limits = 0
            else:
                profile_errors += 1
                consecutive_rate_limits = 0

            # Refresh summary after every task so a killed run leaves useful output.
            write_summary(run_dir, args.profiles, tasks)

        append_progress(
            run_dir,
            {
                "event": "profile_end",
                "ts": utc_now(),
                "profile": profile_name,
                "passed": profile_passed,
                "failed": profile_failed,
                "skipped_existing": profile_skipped_existing,
                "errors": profile_errors,
            },
        )

    write_summary(run_dir, args.profiles, tasks)
    append_progress(run_dir, {"event": "run_end", "ts": utc_now()})

    # Print final summary
    s = summarize(run_dir, args.profiles, tasks)
    print("\n" + "=" * 60)
    print(f"Final summary (run_id={run_id})")
    print("=" * 60)
    for name, info in s["profiles"].items():
        if "error" in info:
            print(f"  {name}: ERROR {info['error']}")
            continue
        c = info["counts"]
        pr = info["pass_rate"]
        print(
            f"  {name:30s} passed={c['passed']:>3} "
            f"failed={c['failed']:>3} missing={c['missing']:>3} "
            f"error={c['error']:>3} rate={pr:.1%}"
            if pr is not None
            else f"  {name:30s} passed={c['passed']:>3} failed={c['failed']:>3}"
        )
    print(f"\nSummary JSON: {run_dir / 'summary.json'}")
    print(f"Progress log: {run_dir / 'progress.jsonl'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
