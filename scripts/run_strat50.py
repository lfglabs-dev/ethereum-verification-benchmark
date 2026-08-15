#!/usr/bin/env python3
"""Run one or more models on a frozen STRAT-50 panel.

Models run in parallel lanes; tasks within a model remain sequential. Results are
checkpointed atomically after every task. Infrastructure failures open a
recoverable circuit and re-probe after a bounded cooldown; they are never scored
as model failures.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

VALID = {"SOLVED", "GENUINE_FAIL"}
INFRA = {"INFRA_INVALID", "preflight_failed", "provider_setup_error"}
SECRET_ENV_MARKERS = ("KEY", "TOKEN", "SECRET", "PASSWORD", "CREDENTIAL")
CANONICAL_STRAT50 = {
    "0.2": {
        "benchmark_head": "c5a2344b121040445ccd745a3f839548ca8f9158",
        "benchmark_manifest_sha256": "04552f2fb5ea7b743c9ed8b09019878d4758efca0bec8e9b3031ccc1d65fcc5b",
        "panel_sha256": "ddb8459aa158d5a0271ba73046bc53bad6768cfff7cd4b3c3f7b0887ed9e3865",
        "task_set_id": "sha256:ddfd5ad518a6cb840be16a04651f6d5db81690023dda9953250a70e6da8009fe",
        "environment_id": "sha256:63ba1672d2c275905329bcd2b7188d7a75eb3431492debccb5953ce4742ff41e",
        "harness_id": "sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867",
    },
    "0.3": {
        "benchmark_head": "d46684dcaf04a8d24dabee3330df1aea517c3a54",
        "benchmark_manifest_sha256": "98961c8ab23a4855d9eb4422b3a0d87517249ea4c8c98cc6f717cdb8ad7c942e",
        "panel_sha256": "6921cc27d522ecbfd0798e9bca9251526f10923855cc28dde4b22507f92eaf25",
        "task_set_id": "sha256:ad4a77b5d7176edf532b7baab1a376df92416dee9ecd973eaffe3525bd88072b",
        "environment_id": "sha256:c2b6593676b790a2ce3e0ba258b70438e286b809ff26811fe4099ff6d8dd897a",
        "harness_id": "sha256:98bbe897aa65ec83d32d577a183cea1a21ba6122851048d4c591f3f55c10c729",
    },
}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--panel", type=Path, required=True, help="JSON array of ordered task refs")
    p.add_argument("--workdir", type=Path, required=True, help="immutable benchmark checkout")
    p.add_argument("--benchmark-head", required=True)
    p.add_argument(
        "--benchmark-manifest",
        type=Path,
        required=True,
        help="version manifest whose commit and task set define this cohort",
    )

    p.add_argument("--model", action="append", required=True, dest="models")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--max-attempts", type=int, default=16)
    p.add_argument("--max-tool-calls", type=int, default=120)
    p.add_argument("--recovery-delay", type=int, default=600)
    p.add_argument("--infra-threshold", type=int, default=5)
    p.add_argument("--max-recovery-cycles", type=int, default=3)
    p.add_argument("--omit-stop-model", action="append", default=[])
    p.add_argument("--omit-sampling-model", action="append", default=[])
    p.add_argument(
        "--reasoning-effort",
        action="append",
        default=[],
        metavar="MODEL=EFFORT",
        help="pin provider reasoning effort for one model",
    )
    return p.parse_args()


def atomic_json(path: Path, value: object) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(path)


def run_dir(stdout: str) -> str | None:
    return next((s for s in reversed(stdout.splitlines()) if s.startswith("/") and "/results/runs/" in s), None)


def validate_panel_identity(path: Path, expected_sha256: str) -> str:
    actual_sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual_sha256 != expected_sha256:
        raise SystemExit(
            f"panel does not match frozen STRAT-50 identity: {actual_sha256}"
        )
    return actual_sha256


def benchmark_identity(
    manifest_path: Path,
    benchmark_head: str,
    panel_tasks: list[str],
    canonical_panels: dict[str, dict[str, str]] = CANONICAL_STRAT50,
) -> dict[str, object]:
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    if manifest.get("git_sha") != benchmark_head:
        raise SystemExit(
            "benchmark manifest commit mismatch: "
            f"expected {benchmark_head}, got {manifest.get('git_sha')}"
        )
    manifest_tasks = {
        task.get("task_ref") for task in manifest.get("tasks", []) if isinstance(task, dict)
    }
    unknown = sorted(set(panel_tasks) - manifest_tasks)
    if unknown:
        raise SystemExit(f"panel contains tasks absent from benchmark manifest: {unknown}")
    required = ("benchmark_version", "task_set_id", "environment_id", "harness_id")
    missing = [key for key in required if not manifest.get(key)]
    if missing:
        raise SystemExit(f"benchmark manifest is missing identity fields: {missing}")
    version = manifest["benchmark_version"]
    canonical = canonical_panels.get(version)
    if not canonical:
        raise SystemExit(f"no canonical STRAT-50 identity registered for v{version}")
    actual_identity = {
        "benchmark_head": benchmark_head,
        "benchmark_manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
        "task_set_id": manifest["task_set_id"],
        "environment_id": manifest["environment_id"],
        "harness_id": manifest["harness_id"],
    }
    mismatches = {
        key: {"expected": canonical[key], "actual": actual_identity[key]}
        for key in actual_identity
        if actual_identity[key] != canonical[key]
    }
    if mismatches:
        raise SystemExit(f"benchmark identity is not canonical STRAT-50 v{version}: {mismatches}")
    return {
        "benchmark_version": version,
        **actual_identity,
        "canonical_panel_sha256": canonical["panel_sha256"],
    }


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
    if len(args.models) != len(set(args.models)):
        raise SystemExit("duplicate --model values are not allowed")
    if (args.max_attempts, args.max_tool_calls) != (16, 120):
        raise SystemExit("STRAT-50 p4_normal requires --max-attempts 16 and --max-tool-calls 120")
    reasoning_efforts = dict(item.split("=", 1) for item in args.reasoning_effort)
    unknown_effort_models = set(reasoning_efforts) - set(args.models)
    if unknown_effort_models:
        raise SystemExit(f"reasoning effort configured for absent models: {sorted(unknown_effort_models)}")
    actual_head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=args.workdir, text=True
    ).strip()
    if actual_head != args.benchmark_head:
        raise SystemExit(
            f"benchmark checkout mismatch: expected {args.benchmark_head}, got {actual_head}"
        )
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=args.workdir, text=True).strip():
        raise SystemExit("benchmark checkout must be clean")
    tasks = json.loads(args.panel.read_text())
    if not isinstance(tasks, list) or len(tasks) != 50 or len(set(tasks)) != 50:
        raise SystemExit("panel must contain exactly 50 unique ordered task refs")
    manifest_identity = benchmark_identity(
        args.benchmark_manifest, args.benchmark_head, tasks
    )
    args.output.mkdir(parents=True, exist_ok=True)
    results_path = args.output / "results.json"
    state_path = args.output / "cohort.json"
    panel_sha256 = validate_panel_identity(
        args.panel, str(manifest_identity.pop("canonical_panel_sha256"))
    )
    unknown_omit_stop_models = set(args.omit_stop_model) - set(args.models)
    if unknown_omit_stop_models:
        raise SystemExit(f"omit-stop configured for absent models: {sorted(unknown_omit_stop_models)}")
    effective_env = {
        key: value
        for key, value in sorted(os.environ.items())
        if key.startswith("DEFAULT_HARNESS_")
        and not any(marker in key for marker in SECRET_ENV_MARKERS)
    }
    cohort = {
        "benchmark_head": args.benchmark_head,
        **manifest_identity,
        "panel_sha256": panel_sha256,
        "profile": "p4_normal",
        "max_attempts": args.max_attempts,
        "max_tool_calls": args.max_tool_calls,
        "omit_stop_models": sorted(args.omit_stop_model),
        "omit_sampling_models": sorted(args.omit_sampling_model),
        "reasoning_efforts": dict(sorted(reasoning_efforts.items())),
        "models": sorted(args.models),
        "max_recovery_cycles": args.max_recovery_cycles,
        "effective_transport_env": effective_env,
    }
    if state_path.is_file() and json.loads(state_path.read_text()) != cohort:
        raise SystemExit("output directory belongs to an incompatible cohort")
    if results_path.is_file() and not state_path.is_file():
        raise SystemExit("refusing to resume results without cohort metadata")
    atomic_json(state_path, cohort)
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
        recovery_cycles = 0
        for index, task in enumerate(pending, 1):
            while True:
                env = os.environ.copy()
                env["DEFAULT_HARNESS_MODEL"] = model
                if model in args.omit_stop_model:
                    env["DEFAULT_HARNESS_STOP_SEQUENCES"] = ""
                if model in args.omit_sampling_model:
                    env["DEFAULT_HARNESS_OMIT_SAMPLING"] = "1"
                if model in reasoning_efforts:
                    env["DEFAULT_HARNESS_REASONING_EFFORT"] = reasoning_efforts[model]
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
                    recovery_cycles = 0
                    break
                streak += 1
                if streak < args.infra_threshold:
                    time.sleep(30)
                    continue
                print(f"[{model}] circuit open; re-probing in {args.recovery_delay}s", flush=True)
                recovery_cycles += 1
                if recovery_cycles >= args.max_recovery_cycles:
                    raise RuntimeError(f"infrastructure remained unavailable after {recovery_cycles} recovery cycles for {task}")
                time.sleep(args.recovery_delay)
                streak = 0

    lane_errors: list[tuple[str, BaseException]] = []

    def guarded_lane(model: str) -> None:
        try:
            lane(model)
        except BaseException as exc:
            with lock:
                lane_errors.append((model, exc))

    threads = [threading.Thread(target=guarded_lane, args=(m,), name=m) for m in args.models]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    if lane_errors:
        for model, exc in lane_errors:
            print(f"[{model}] lane failed: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    print("STRAT50_COMPLETE", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
