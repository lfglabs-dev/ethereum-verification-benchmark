#!/usr/bin/env python3
from __future__ import annotations

import argparse
import glob
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.classification import classify_run


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _run_dirs(patterns: list[str]) -> list[Path]:
    paths: set[Path] = set()
    for pattern in patterns:
        for match in glob.glob(pattern):
            path = Path(match)
            if path.is_file() and path.name == "run.json":
                path = path.parent
            if (path / "run.json").is_file():
                paths.add(path)
    return sorted(paths)


def _run_dirs_from_aggregate(path: Path, *, include_preserved_passes: bool) -> list[Path]:
    payload = _load_json(path)
    paths: set[Path] = set()
    records = payload.get("records")
    if isinstance(records, list):
        for record in records:
            if not isinstance(record, dict):
                continue
            run_json = record.get("run_json")
            if isinstance(run_json, str):
                paths.add(Path(run_json).parent)
    if include_preserved_passes:
        passes = payload.get("preserved_pass_artifacts")
        if isinstance(passes, list):
            for record in passes:
                if not isinstance(record, dict):
                    continue
                run_json = record.get("run_json")
                if isinstance(run_json, str):
                    paths.add(Path(run_json).parent)
    return sorted(path for path in paths if (path / "run.json").is_file())


def classify_run_dir(run_dir: Path) -> dict[str, Any]:
    run = _load_json(run_dir / "run.json")
    response_path = run_dir / "harness-response.json"
    response = _load_json(response_path) if response_path.is_file() else {}
    tasks = response.get("tasks") if isinstance(response.get("tasks"), list) else []
    classification = classify_run(run.get("verifier", {}), tasks)
    return {"run_dir": str(run_dir), "run": run, "classification": classification}


def main() -> int:
    parser = argparse.ArgumentParser(description="Replay publication-safe classification over existing run artifacts")
    parser.add_argument("patterns", nargs="*", help="run directory or glob pattern")
    parser.add_argument("--aggregate-records", type=Path, help="read run_json paths from an aggregate JSON records array")
    parser.add_argument("--include-preserved-passes", action="store_true", help="also include aggregate preserved_pass_artifacts")
    parser.add_argument("--json", action="store_true", help="emit JSON instead of a text summary")
    args = parser.parse_args()

    run_dirs = _run_dirs(args.patterns)
    if args.aggregate_records:
        run_dirs.extend(_run_dirs_from_aggregate(args.aggregate_records, include_preserved_passes=args.include_preserved_passes))
    run_dirs = sorted(set(run_dirs))
    records = [classify_run_dir(path) for path in run_dirs]
    final_counts: Counter[str] = Counter()
    raw_by_final: dict[str, Counter[str]] = defaultdict(Counter)
    reasons: Counter[str] = Counter()
    for record in records:
        classification = record["classification"]
        for target in classification.get("targets", []):
            if not isinstance(target, dict):
                continue
            final_class = str(target.get("final_class"))
            raw_status = str(target.get("raw_verifier_status"))
            final_counts[final_class] += 1
            raw_by_final[final_class][raw_status] += 1
            reasons[str(target.get("final_reason"))] += 1

    payload = {
        "run_count": len(records),
        "target_count": sum(final_counts.values()),
        "final_class_counts": dict(sorted(final_counts.items())),
        "raw_verifier_by_final_class": {
            key: dict(sorted(value.items())) for key, value in sorted(raw_by_final.items())
        },
        "final_reason_counts": dict(sorted(reasons.items())),
    }
    if args.json:
        print(json.dumps(payload, indent=2))
        return 0

    print(f"runs: {payload['run_count']}")
    print(f"targets: {payload['target_count']}")
    print(f"final_class_counts: {payload['final_class_counts']}")
    print(f"raw_verifier_by_final_class: {payload['raw_verifier_by_final_class']}")
    print(f"final_reason_counts: {payload['final_reason_counts']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
