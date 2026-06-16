#!/usr/bin/env python3
"""Plan incremental benchmark reruns between two benchmark versions."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from compute_fingerprints import digest_json  # noqa: E402


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def result_key(
    *,
    model: str,
    benchmark_version: str,
    task_ref: str,
    task_fingerprint: str,
    harness_id: str,
    environment_id: str,
    mode: str,
    budget: str,
    temperature_policy: object = None,
    provider_caveats: object = None,
) -> str:
    return digest_json(
        {
            "model": model,
            "benchmark_version": benchmark_version,
            "task_ref": task_ref,
            "task_fingerprint": task_fingerprint,
            "harness_id": harness_id,
            "environment_id": environment_id,
            "mode": mode,
            "budget": budget,
            "temperature_policy": temperature_policy,
            "provider_caveats": provider_caveats,
        }
    )


def model_result(manifest: dict[str, Any], model: str) -> dict[str, Any] | None:
    for entry in manifest.get("models", []):
        if isinstance(entry, dict) and entry.get("model_id") == model:
            return entry
    return None


def task_results_by_ref(model_entry: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if not model_entry:
        return {}
    return {
        str(entry.get("task_ref")): entry
        for entry in model_entry.get("task_results", [])
        if isinstance(entry, dict) and entry.get("task_ref")
    }


def reusable_result(entry: dict[str, Any] | None) -> tuple[bool, str | None]:
    if not entry:
        return False, "missing previous result"
    usage = entry.get("usage") if isinstance(entry.get("usage"), dict) else {}
    total_tokens = int(usage.get("total_tokens") or usage.get("prompt_tokens") or 0) + int(usage.get("completion_tokens") or 0)
    if total_tokens <= 0:
        return False, "zero usage"
    if not entry.get("verifier_output_present", False):
        return False, "missing verifier output"
    if entry.get("artifact_status") == "error-only" or entry.get("harness_status") not in {None, "completed"}:
        return False, "error-only artifact"
    return True, None


def plan_rerun(
    from_version: dict[str, Any],
    to_version: dict[str, Any],
    *,
    model: str,
    results_manifest: dict[str, Any],
    allow_env_compatible: bool = False,
) -> dict[str, Any]:
    from_tasks = {str(task["task_ref"]): task for task in from_version.get("tasks", [])}
    to_tasks = {str(task["task_ref"]): task for task in to_version.get("tasks", [])}
    previous = task_results_by_ref(model_result(results_manifest, model))
    model_entry = model_result(results_manifest, model)
    temperature_policy = (model_entry or {}).get("temperature_policy") or None
    provider_caveats = (model_entry or {}).get("caveats") or None

    rerun: list[dict[str, str]] = []
    reuse: list[dict[str, str]] = []
    removed: list[str] = []
    changed: list[str] = []

    harness_changed = from_version.get("harness_id") != to_version.get("harness_id")
    env_changed = from_version.get("environment_id") != to_version.get("environment_id")
    env_blocks_reuse = env_changed and not allow_env_compatible

    for task_ref in sorted(set(from_tasks) - set(to_tasks)):
        removed.append(task_ref)

    for task_ref in sorted(to_tasks):
        old_task = from_tasks.get(task_ref)
        new_task = to_tasks[task_ref]
        reason: str | None = None
        if harness_changed:
            reason = "harness_id changed"
        elif env_blocks_reuse:
            reason = "environment_id changed"
        elif old_task is None:
            reason = "task added"
        elif old_task.get("task_fingerprint") != new_task.get("task_fingerprint"):
            reason = "task_fingerprint changed"

        if reason is None:
            ok, invalid_reason = reusable_result(previous.get(task_ref))
            if not ok:
                reason = invalid_reason or "previous result is invalid"

        new_key = result_key(
            model=model,
            benchmark_version=str(to_version.get("benchmark_version")),
            task_ref=task_ref,
            task_fingerprint=str(new_task.get("task_fingerprint")),
            harness_id=str(to_version.get("harness_id")),
            environment_id=str(to_version.get("environment_id")),
            mode=str(to_version.get("mode")),
            budget=str(to_version.get("budget")),
            temperature_policy=temperature_policy,
            provider_caveats=provider_caveats,
        )
        if reason is None:
            reuse.append({"task_ref": task_ref, "from_result_key": str(previous[task_ref].get("result_key")), "to_result_key": new_key})
        else:
            rerun.append({"task_ref": task_ref, "reason": reason, "result_key": new_key})
            if reason.endswith("changed"):
                changed.append(task_ref)

    return {
        "schema_version": 1,
        "model_id": model,
        "from_version": from_version.get("benchmark_version"),
        "to_version": to_version.get("benchmark_version"),
        "allow_env_compatible": allow_env_compatible,
        "harness_changed": harness_changed,
        "environment_changed": env_changed,
        "task_count": len(to_tasks),
        "reuse_count": len(reuse),
        "rerun_count": len(rerun),
        "removed_count": len(removed),
        "reuse": reuse,
        "rerun": rerun,
        "removed": removed,
    }


def render_summary(plan: dict[str, Any]) -> str:
    lines = [
        f"Model: {plan['model_id']}",
        f"Versions: {plan['from_version']} -> {plan['to_version']}",
        f"Reuse: {plan['reuse_count']} task(s)",
        f"Rerun: {plan['rerun_count']} task(s)",
        f"Removed: {plan['removed_count']} task(s)",
    ]
    reasons: dict[str, int] = {}
    for item in plan["rerun"]:
        reasons[item["reason"]] = reasons.get(item["reason"], 0) + 1
    for reason, count in sorted(reasons.items()):
        lines.append(f"- {reason}: {count}")
    for item in plan["rerun"][:20]:
        lines.append(f"  rerun {item['task_ref']} ({item['reason']})")
    if len(plan["rerun"]) > 20:
        lines.append(f"  ... {len(plan['rerun']) - 20} more")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--from", dest="from_path", type=Path, required=True)
    parser.add_argument("--to", dest="to_path", type=Path, required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--results-manifest", type=Path, required=True)
    parser.add_argument("--allow-env-compatible", action="store_true")
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args()

    plan = plan_rerun(
        load_json(args.from_path),
        load_json(args.to_path),
        model=args.model,
        results_manifest=load_json(args.results_manifest),
        allow_env_compatible=args.allow_env_compatible,
    )
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.format == "json":
        print(json.dumps(plan, indent=2, sort_keys=True))
    else:
        print(render_summary(plan))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
