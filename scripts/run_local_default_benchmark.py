#!/usr/bin/env python3
"""Run the default harness locally over an explicit task list.

This mirrors the benchmark workflow's per-task loop while making local runs
resumable: if a completed run for the same model/task already exists, it is
skipped.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
RUNS_DIR = ROOT / "results" / "runs"


def completed_run_exists(model: str, task_ref: str) -> bool:
    for run_json in RUNS_DIR.glob("*/run.json"):
        try:
            run = json.loads(run_json.read_text(encoding="utf-8"))
        except Exception:
            continue
        if (
            run.get("harness_id") == "default"
            and run.get("model") == model
            and run.get("task_ref") == task_ref
            and run.get("harness_status") == "completed"
        ):
            return True
    return False


def list_active_tasks() -> list[str]:
    result = subprocess.run(
        [sys.executable, "-m", "harness.cli", "list", "--suite", "active", "--unit", "task"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--budget", default="normal", choices=["quick", "normal", "deep"])
    parser.add_argument("--log-dir", type=Path, default=ROOT.parent / "output" / "bench-logs")
    parser.add_argument("--tasks", nargs="*", default=None)
    args = parser.parse_args()

    tasks = args.tasks or list_active_tasks()
    args.log_dir.mkdir(parents=True, exist_ok=True)
    model_slug = "".join(ch if ch.isalnum() else "-" for ch in args.model).strip("-").lower()
    summary_path = args.log_dir / f"{model_slug}-local-summary.jsonl"

    failures = 0
    for index, task in enumerate(tasks, start=1):
        if completed_run_exists(args.model, task):
            print(f"[{index}/{len(tasks)}] skip completed {task}", flush=True)
            continue
        print(f"[{index}/{len(tasks)}] start {task}", flush=True)
        env = os.environ.copy()
        env["DEFAULT_HARNESS_MODEL"] = args.model
        log_path = args.log_dir / f"{model_slug}--{task.replace('/', '__')}.log"
        last_line = ""
        with log_path.open("a", encoding="utf-8") as log:
            proc = subprocess.Popen(
                [
                    sys.executable,
                    "-m",
                    "harness.cli",
                    "run-task",
                    task,
                    "--harness",
                    "default",
                    "--budget",
                    args.budget,
                ],
                cwd=ROOT,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            assert proc.stdout is not None
            for line in proc.stdout:
                log.write(line)
                log.flush()
                if line.strip():
                    last_line = line.strip()
            returncode = proc.wait()
        run_dir = last_line
        status = ""
        score = None
        if run_dir:
            run_json = Path(run_dir) / "run.json"
            if run_json.is_file():
                run = json.loads(run_json.read_text(encoding="utf-8"))
                status = str(run.get("harness_status") or "")
                score = run.get("score") or (run.get("verifier") or {}).get("score")
        record = {
            "model": args.model,
            "task_ref": task,
            "returncode": returncode,
            "run_dir": run_dir,
            "harness_status": status,
            "score": score,
        }
        with summary_path.open("a", encoding="utf-8") as summary:
            summary.write(json.dumps(record) + "\n")
        print(f"[{index}/{len(tasks)}] done {task} rc={returncode} status={status}", flush=True)
        if status not in {"completed"}:
            failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
