#!/usr/bin/env python3
"""Run one or more models on a frozen STRAT-50 panel.

Models run in parallel lanes; tasks within a model remain sequential. Results are
checkpointed atomically after every task. Infrastructure failures open a
recoverable circuit and re-probe after a bounded cooldown; they are never scored
as model failures.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

VALID = {"SOLVED", "GENUINE_FAIL"}
INFRA = {"INFRA_INVALID", "preflight_failed", "provider_setup_error"}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--panel", type=Path, required=True, help="JSON array of ordered task refs")
    p.add_argument("--workdir", type=Path, required=True, help="immutable benchmark checkout")
    p.add_argument("--benchmark-head", default="c5a2344b121040445ccd745a3f839548ca8f9158")
    p.add_argument("--model", action="append", required=True, dest="models")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--max-attempts", type=int, default=16)
    p.add_argument("--max-tool-calls", type=int, default=120)
    p.add_argument("--recovery-delay", type=int, default=600)
    p.add_argument("--infra-threshold", type=int, default=5)
    p.add_argument("--omit-stop", action="store_true")
    p.add_argument("--omit-sampling-model", action="append", default=[])
    return p.parse_args()


def atomic_json(path: Path, value: object) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(path)


def run_dir(stdout: str) -> str | None:
    return next((s for s in reversed(stdout.splitlines()) if s.startswith("/") and "/results/runs/" in s), None)


def classify(path: str | None) -> tuple[str, dict[str, int]]:
    if not path or not (Path(path) / "run.json").is_file():
        return "INFRA_INVALID", {}
    data = json.loads((Path(path) / "run.json").read_text())
    targets = (data.get("classification") or {}).get("targets") or []
    usage = data.get("usage") or {}
    result = targets[0].get("final_class") if targets else None
    if not result:
        response = Path(path) / "harness-response.json"
        if response.is_file():
            status = json.loads(response.read_text()).get("status")
            result = "INFRA_INVALID" if status == "preflight_failed" else status
    return result or "INFRA_INVALID", {k: int(usage.get(k, 0) or 0) for k in ("prompt_tokens", "completion_tokens", "total_tokens", "requests")}


def main() -> int:
    args = parse_args()
    actual_head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=args.workdir, text=True
    ).strip()
    if actual_head != args.benchmark_head:
        raise SystemExit(
            f"benchmark checkout mismatch: expected {args.benchmark_head}, got {actual_head}"
        )
    tasks = json.loads(args.panel.read_text())
    if not isinstance(tasks, list) or len(tasks) != 50 or len(set(tasks)) != 50:
        raise SystemExit("panel must contain exactly 50 unique ordered task refs")
    args.output.mkdir(parents=True, exist_ok=True)
    results_path = args.output / "results.json"
    rows = json.loads(results_path.read_text()) if results_path.is_file() else []
    lock = threading.Lock()

    def save(row: dict[str, object]) -> None:
        with lock:
            rows.append(row)
            atomic_json(results_path, rows)

    def lane(model: str) -> None:
        with lock:
            done = {r["task_ref"] for r in rows if r.get("model") == model and r.get("final_class") in VALID}
        pending = [task for task in tasks if task not in done]
        streak = 0
        for index, task in enumerate(pending, 1):
            while True:
                env = os.environ.copy()
                env["DEFAULT_HARNESS_MODEL"] = model
                if args.omit_stop:
                    env["DEFAULT_HARNESS_STOP_SEQUENCES"] = ""
                if model in args.omit_sampling_model:
                    env["DEFAULT_HARNESS_OMIT_SAMPLING"] = "1"
                cmd = [sys.executable, "-m", "harness.cli", "run-task", task, "--harness", "default", "--suite", "all", "--max-attempts", str(args.max_attempts), "--max-tool-calls", str(args.max_tool_calls)]
                started = time.time()
                try:
                    proc = subprocess.run(
                        cmd,
                        cwd=args.workdir,
                        capture_output=True,
                        text=True,
                        env=env,
                        timeout=args.max_tool_calls * 120 + 600,
                    )
                    rd = run_dir(proc.stdout)
                    final_class, usage = classify(rd)
                except subprocess.TimeoutExpired:
                    proc = None
                    rd = None
                    final_class, usage = "INFRA_INVALID", {}
                row = {"model": model, "panel": "STRAT-50", "profile": "p4_normal", "max_attempts": args.max_attempts, "max_tool_calls": args.max_tool_calls, "task_ref": task, "final_class": final_class, "passed": final_class == "SOLVED", "run_dir": rd, "returncode": proc.returncode if proc else 124, "elapsed_seconds": round(time.time() - started, 1), **usage}
                save(row)
                print(f"[{model}] {index}/{len(pending)} {task} {final_class}", flush=True)
                if final_class not in INFRA:
                    streak = 0
                    break
                streak += 1
                if streak < args.infra_threshold:
                    time.sleep(30)
                    continue
                print(f"[{model}] circuit open; re-probing in {args.recovery_delay}s", flush=True)
                time.sleep(args.recovery_delay)
                streak = 0

    threads = [threading.Thread(target=lane, args=(m,), name=m) for m in args.models]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    print("STRAT50_COMPLETE", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
