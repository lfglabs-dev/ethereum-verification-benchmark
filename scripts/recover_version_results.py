#!/usr/bin/env python3
"""Recover version result rows from existing run artifacts.

This script does not execute providers or verifiers. It re-indexes already
materialized ``results/runs/*/run.json`` artifacts into a version results
manifest, which is useful when a published manifest was generated before all
local run artifacts had been copied into the release workspace.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from classify_failures import COMPLETED_HARNESS_STATUSES  # noqa: E402
from infra_failures import provider_failure_reason  # noqa: E402
from plan_rerun import result_key  # noqa: E402


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def usage_total(run: dict[str, Any]) -> int:
    usage = run.get("usage") if isinstance(run.get("usage"), dict) else {}
    if "total_tokens" in usage:
        return int(usage.get("total_tokens") or 0)
    return int(usage.get("prompt_tokens") or 0) + int(usage.get("completion_tokens") or 0)


def is_pass(run: dict[str, Any]) -> bool:
    score = ((run.get("verifier") or {}).get("score") or {})
    earned = score.get("points_earned")
    possible = score.get("points_possible")
    return isinstance(earned, (int, float)) and isinstance(possible, (int, float)) and possible > 0 and earned >= possible


def run_sort_key(run: dict[str, Any]) -> tuple[int, int, str]:
    status = str(run.get("harness_status") or "").strip().lower()
    completed = 1 if status in COMPLETED_HARNESS_STATUSES else 0
    nonzero = 1 if usage_total(run) > 0 else 0
    return completed, nonzero, str(run.get("started_at") or run.get("run_id") or "")


def iter_runs(runs_dirs: list[Path]) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []
    for runs_dir in runs_dirs:
        if not runs_dir.exists():
            print(f"warning: missing runs dir: {runs_dir}", file=sys.stderr)
            continue
        for run_path in sorted(runs_dir.glob("*/run.json")):
            try:
                run = load_json(run_path)
            except (OSError, json.JSONDecodeError) as exc:
                print(f"warning: skipping unreadable run: {run_path}: {exc}", file=sys.stderr)
                continue
            run["_artifact_dir"] = run_path.parent.name
            run["_artifact_path"] = str(run_path.parent)
            runs.append(run)
    return runs


def archive_by_model(manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        str(model.get("model_id")): model.get("archive")
        for model in manifest.get("models", [])
        if isinstance(model, dict) and isinstance(model.get("archive"), dict)
    }


def existing_model_defaults(manifest: dict[str, Any], model_id: str) -> dict[str, Any]:
    for model in manifest.get("models", []):
        if isinstance(model, dict) and model.get("model_id") == model_id:
            return {
                "archive": model.get("archive"),
                "display_name": model.get("display_name") or model_id,
                "temperature_policy": model.get("temperature_policy"),
            }
    return {"archive": None, "display_name": model_id, "temperature_policy": None}


def build_model_entry(
    *,
    model_id: str,
    version: dict[str, Any],
    previous_manifest: dict[str, Any],
    runs: list[dict[str, Any]],
) -> dict[str, Any]:
    tasks = {str(task["task_ref"]): task for task in version.get("tasks", [])}
    selected: dict[str, dict[str, Any]] = {}
    for run in runs:
        if run.get("model") != model_id:
            continue
        task_ref = str(run.get("task_ref") or "")
        if task_ref not in tasks:
            continue
        previous = selected.get(task_ref)
        if previous is None or run_sort_key(run) > run_sort_key(previous):
            selected[task_ref] = run

    defaults = existing_model_defaults(previous_manifest, model_id)
    caveats: list[str] = []
    if len(selected) != len(tasks):
        caveats.append(f"partial task coverage: {len(selected)}/{len(tasks)}")

    task_results: list[dict[str, Any]] = []
    token_totals = {"completion_tokens": 0, "prompt_tokens": 0, "requests": 0, "total_tokens": 0}
    passed = 0
    valid_count = 0
    invalid_count = 0
    temperature_policy = defaults["temperature_policy"]
    provider_caveats = caveats or None
    for task_ref in sorted(selected):
        run = selected[task_ref]
        task = tasks[task_ref]
        usage = run.get("usage") if isinstance(run.get("usage"), dict) else {}
        normalized_usage = {
            "completion_tokens": int(usage.get("completion_tokens") or 0),
            "prompt_tokens": int(usage.get("prompt_tokens") or 0),
            "requests": int(usage.get("requests") or 0),
            "total_tokens": usage_total(run),
        }
        for key in token_totals:
            token_totals[key] += normalized_usage[key]

        harness_status = str(run.get("harness_status") or "")
        artifact_status = "ok" if harness_status.strip().lower() in COMPLETED_HARNESS_STATUSES else "error-only"
        passed_task = is_pass(run)
        run_dir = Path(run["_artifact_path"]) if run.get("_artifact_path") else None
        # A passing verdict is always genuine; only scrutinize non-passing verdicts for
        # provider/transport contamination so infra outages are never scored as model failures.
        provider_reason = None if passed_task else provider_failure_reason(run, run_dir)
        provider_invalid = provider_reason is not None
        # "reusable" == the stored verdict can be trusted as a genuine pass/fail.
        reusable = (
            artifact_status == "ok"
            and normalized_usage["total_tokens"] > 0
            and bool(run.get("verifier"))
            and not provider_invalid
        )
        # A pass is inherently a genuine, valid verdict; a non-pass is valid only when
        # trustworthy (not contaminated by a provider/transport failure).
        if reusable or passed_task:
            valid_count += 1
        else:
            invalid_count += 1
        if passed_task:
            passed += 1
        entry_result = {
            "artifact_id": str(run.get("run_id") or run.get("_artifact_dir")),
            "artifact_status": artifact_status,
            "harness_status": harness_status,
            "passed": passed_task,
            "provider_invalid": provider_invalid,
            "result_key": result_key(
                model=model_id,
                benchmark_version=str(version["benchmark_version"]),
                task_ref=task_ref,
                task_fingerprint=str(task["task_fingerprint"]),
                task_interface_id=str(task["task_interface_id"]),
                harness_id=str(version["harness_id"]),
                environment_id=str(version["environment_id"]),
                mode=str(version["mode"]),
                budget=str(version["budget"]),
                temperature_policy=temperature_policy,
                provider_caveats=provider_caveats,
            ),
            "reusable": reusable,
            "run_id": str(run.get("run_id") or run.get("_artifact_dir")),
            "task_fingerprint": str(task["task_fingerprint"]),
            "task_interface_id": str(task["task_interface_id"]),
            "task_ref": task_ref,
            "usage": normalized_usage,
            "verifier_output_present": bool(run.get("verifier")),
        }
        if provider_reason:
            entry_result["provider_failure_reason"] = provider_reason
        task_results.append(entry_result)

    if invalid_count:
        caveats.append(f"provider/transport-invalid tasks excluded from failed count: {invalid_count}")
    status = "complete" if len(selected) == len(tasks) and valid_count == len(tasks) else "partial" if selected else "invalid"
    task_count = len(selected)
    return {
        "archive": defaults["archive"],
        "benchmark_version": str(version["benchmark_version"]),
        "caveats": caveats,
        "display_name": defaults["display_name"],
        # Genuine model failures only: infra-invalid tasks are neither passed nor failed.
        "failed": max(0, valid_count - passed),
        "invalid_count": invalid_count,
        "model_id": model_id,
        "passed": passed,
        "status": status,
        "task_count": task_count,
        "task_results": task_results,
        "temperature_policy": temperature_policy,
        "token_totals": token_totals,
        "valid_count": valid_count,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", type=Path, required=True)
    parser.add_argument("--results-manifest", type=Path, required=True)
    parser.add_argument("--runs-dir", type=Path, action="append", required=True)
    parser.add_argument("--model", action="append", required=True)
    args = parser.parse_args()

    version = load_json(args.version)
    manifest = load_json(args.results_manifest)
    runs = iter_runs(args.runs_dir)
    rebuilt = {
        model_id: build_model_entry(model_id=model_id, version=version, previous_manifest=manifest, runs=runs)
        for model_id in args.model
    }

    existing = [model for model in manifest.get("models", []) if model.get("model_id") not in rebuilt]
    manifest["models"] = sorted(existing + list(rebuilt.values()), key=lambda model: str(model.get("model_id")))
    write_json(args.results_manifest, manifest)

    for model_id, entry in rebuilt.items():
        print(
            f"{model_id}: {entry['passed']}/{entry['task_count']} "
            f"status={entry['status']} tokens={entry['token_totals']['total_tokens']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
