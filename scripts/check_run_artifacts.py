#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

REQUIRED_FILES = [
    "run.json",
    "workspace-manifest.json",
    "harness-request.json",
    "harness-response.json",
    "stdout.txt",
    "stderr.txt",
    "verifier/verifier.json",
    "report.md",
]


def _load_json(path: Path, errors: list[str]) -> object | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        errors.append(f"{path.parent}: {path.name} is not valid JSON: {exc}")
    except OSError as exc:
        errors.append(f"{path.parent}: cannot read {path.name}: {exc}")
    return None


def check_run(run_dir: Path) -> list[str]:
    errors: list[str] = []
    if run_dir.is_file() and run_dir.name == "run.json":
        run_dir = run_dir.parent
    for rel in REQUIRED_FILES:
        if not (run_dir / rel).is_file():
            errors.append(f"{run_dir}: missing {rel}")
    if errors:
        return errors
    run = _load_json(run_dir / "run.json", errors)
    manifest = _load_json(run_dir / "workspace-manifest.json", errors)
    request = _load_json(run_dir / "harness-request.json", errors)
    verifier = _load_json(run_dir / "verifier" / "verifier.json", errors)
    if errors:
        return errors
    if not isinstance(run, dict):
        errors.append(f"{run_dir}: run.json is not an object")
        run = {}
    if not isinstance(manifest, dict):
        errors.append(f"{run_dir}: workspace-manifest.json is not an object")
        manifest = {}
    if not isinstance(request, dict):
        errors.append(f"{run_dir}: harness-request.json is not an object")
        request = {}
    if not isinstance(verifier, dict):
        errors.append(f"{run_dir}: verifier/verifier.json is not an object")
        verifier = {}
    if run_dir.joinpath("grok-output.json").is_file():
        _load_json(run_dir / "grok-output.json", errors)
    for key in ("run_id", "harness_id", "track", "run_mode", "group_id", "verifier"):
        if key not in run:
            errors.append(f"{run_dir}: run.json missing {key}")
    if run.get("run_mode") in {"task", "group", "suite"} and "started_at" not in run:
        errors.append(f"{run_dir}: run.json missing started_at")
    if run.get("run_mode") not in {"task", "group", "suite"}:
        errors.append(f"{run_dir}: invalid run_mode {run.get('run_mode')!r}")
    if run.get("run_mode") in {"task", "group"}:
        if not (run_dir / "TASK_SUMMARY.md").is_file():
            errors.append(f"{run_dir}: missing TASK_SUMMARY.md")
        submitted = verifier.get("submitted_files")
        if not isinstance(submitted, list):
            errors.append(f"{run_dir}: verifier missing submitted_files")
        else:
            for item in submitted:
                if isinstance(item, dict) and isinstance(item.get("path"), str):
                    if not (run_dir / "submitted" / item["path"]).is_file():
                        errors.append(f"{run_dir}: missing submitted artifact {item['path']}")
    if not isinstance(manifest.get("files"), list) or not manifest["files"]:
        errors.append(f"{run_dir}: workspace manifest has no file entries")
    if run.get("harness_id") == "default" and run.get("mode") == "fair" and run.get("run_mode") in {"task", "group"}:
        tool_policy = manifest.get("tool_policy")
        if not isinstance(tool_policy, dict) or tool_policy.get("include_group_grindset") is not False:
            errors.append(f"{run_dir}: fair default run must record include_group_grindset=false")
        if "max_tool_calls" not in request:
            errors.append(f"{run_dir}: fair default request missing max_tool_calls")
    if run.get("harness_id") == "grok-build" and run.get("run_mode") in {"task", "group"}:
        for key in ("max_turns", "auth_mode", "timeout_seconds"):
            if key not in request:
                errors.append(f"{run_dir}: grok-build request missing {key}")
        if run.get("harness_status") == "timeout" and not (run_dir / "timeout.json").is_file():
            errors.append(f"{run_dir}: timeout grok-build run missing timeout.json")
        if not (run_dir / "workspace.diff").is_file():
            errors.append(f"{run_dir}: grok-build run missing workspace.diff")
    score = verifier.get("score")
    if not isinstance(score, dict):
        errors.append(f"{run_dir}: verifier missing score")
    else:
        for key in ("points_earned", "points_possible", "passed_targets", "total_targets"):
            if key not in score:
                errors.append(f"{run_dir}: verifier score missing {key}")
    if run.get("run_mode") == "suite":
        child_runs = run.get("child_runs")
        if not isinstance(child_runs, list) or not child_runs:
            errors.append(f"{run_dir}: suite run has no child_runs")
        else:
            totals = {"points_earned": 0, "points_possible": 0, "passed_targets": 0, "total_targets": 0}
            for child in child_runs:
                if not isinstance(child, dict):
                    errors.append(f"{run_dir}: child_runs entry is not an object")
                    continue
                artifact = child.get("artifact")
                if not isinstance(artifact, str) or not (Path(artifact) / "run.json").is_file():
                    errors.append(f"{run_dir}: missing child run artifact {artifact!r}")
                if run.get("harness_id") == "default" and child.get("mode") != run.get("mode"):
                    errors.append(f"{run_dir}: child run mode {child.get('mode')!r} does not match suite mode {run.get('mode')!r}")
                child_score = child.get("score")
                if not isinstance(child_score, dict):
                    errors.append(f"{run_dir}: child run entry missing score")
                    continue
                for key in totals:
                    totals[key] += int(child_score.get(key, 0))
            if isinstance(score, dict):
                for key, expected in totals.items():
                    if int(score.get(key, 0)) != expected:
                        errors.append(f"{run_dir}: suite score {key}={score.get(key)!r} does not match child total {expected}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate normalized benchmark run artifact directories")
    parser.add_argument("runs", nargs="+", type=Path)
    args = parser.parse_args()
    errors: list[str] = []
    for path in args.runs:
        errors.extend(check_run(path))
    if errors:
        print("\n".join(errors))
        return 1
    print(f"run artifact checks passed for {len(args.runs)} run(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
