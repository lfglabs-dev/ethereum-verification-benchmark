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


def check_run(run_dir: Path) -> list[str]:
    errors: list[str] = []
    if run_dir.is_file() and run_dir.name == "run.json":
        run_dir = run_dir.parent
    for rel in REQUIRED_FILES:
        if not (run_dir / rel).is_file():
            errors.append(f"{run_dir}: missing {rel}")
    if errors:
        return errors
    run = json.loads((run_dir / "run.json").read_text(encoding="utf-8"))
    manifest = json.loads((run_dir / "workspace-manifest.json").read_text(encoding="utf-8"))
    verifier = json.loads((run_dir / "verifier" / "verifier.json").read_text(encoding="utf-8"))
    for key in ("run_id", "harness_id", "track", "run_mode", "group_id", "verifier"):
        if key not in run:
            errors.append(f"{run_dir}: run.json missing {key}")
    if run.get("run_mode") not in {"task", "group", "suite"}:
        errors.append(f"{run_dir}: invalid run_mode {run.get('run_mode')!r}")
    if not isinstance(manifest.get("files"), list) or not manifest["files"]:
        errors.append(f"{run_dir}: workspace manifest has no file entries")
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
