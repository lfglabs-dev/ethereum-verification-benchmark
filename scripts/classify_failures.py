#!/usr/bin/env python3
"""Classify Verity proof-attempt failures into a two-level taxonomy.

Level 1 is the *outcome* (passed / lean_check_failed / theorem_missing / timeout / ...),
derived from the verifier or harness status. Level 2 is the *Lean failure sub-mode*
(unsolved_goals / tactic_failed / syntax_error / ...), parsed from the verifier output
when a submitted proof fails to type-check.

The taxonomy itself lives in ``analysis/failure_modes.json`` so it can be extended
without touching code. This module is a thin, deterministic interpreter over that file.

It is intentionally independent of benchmark versioning: classification never feeds
``result_key`` and changing the taxonomy never invalidates a stored result.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TAXONOMY = ROOT / "analysis" / "failure_modes.json"

# Harness statuses that mean the run finished cleanly enough to trust its verdict.
# ``completed_with_failures`` is emitted (harness/cli.py) when the run completes but some
# targets fail -- those are genuine model failures we must keep, not infrastructure errors.
COMPLETED_HARNESS_STATUSES = frozenset({"", "completed", "completed_with_failures"})


@dataclass(frozen=True)
class Classification:
    outcome: str
    is_pass: bool
    lean_failure_mode: str | None
    detail: str | None

    def as_dict(self) -> dict[str, Any]:
        return {
            "outcome": self.outcome,
            "is_pass": self.is_pass,
            "lean_failure_mode": self.lean_failure_mode,
            "detail": self.detail,
        }


def load_taxonomy(path: Path = DEFAULT_TAXONOMY) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _build_status_index(taxonomy: dict[str, Any]) -> dict[str, dict[str, Any]]:
    index: dict[str, dict[str, Any]] = {}
    for status in taxonomy.get("outcome_statuses", []):
        for raw in status.get("verifier_status", []):
            index[str(raw).strip().lower()] = status
    return index


def map_outcome(
    status: str | None,
    *,
    taxonomy: dict[str, Any],
    harness_status: str | None = None,
) -> dict[str, Any]:
    """Resolve a raw verifier/harness status to an outcome status entry.

    A harness that did not complete is treated as a harness error regardless of the
    verifier status, since a partial run can leave a stale or empty verdict.
    """
    index = _build_status_index(taxonomy)
    if harness_status is not None and str(harness_status).strip().lower() not in COMPLETED_HARNESS_STATUSES:
        return index.get("harness_error", {"id": "harness_error", "is_pass": False})
    key = str(status or "").strip().lower()
    if key in index:
        return index[key]
    if not key:
        return index.get("no_submission", {"id": "no_submission", "is_pass": False})
    # Unknown non-empty status: not a pass, surface it as a harness error rather than
    # silently treating it as a Lean failure we can sub-classify.
    return {"id": "harness_error", "is_pass": False, "label": f"unmapped:{key}"}


def _capture_detail(capture: Any, output: str) -> str | None:
    """Run one or more capture regexes against the output, returning the first hit.

    ``capture`` may be a single regex string or a list of regexes tried in order. Each
    regex should expose a named ``detail`` group (falling back to the first group).
    """
    if not capture:
        return None
    patterns = capture if isinstance(capture, list) else [capture]
    for pattern in patterns:
        match = re.search(pattern, output, flags=re.IGNORECASE)
        if match:
            groups = match.groupdict()
            if groups.get("detail"):
                return groups["detail"]
            if match.groups():
                return match.group(1)
    return None


def classify_lean_output(output: str, *, taxonomy: dict[str, Any]) -> tuple[str, str | None]:
    """Return (lean_failure_mode_id, detail) for a failed Lean check output."""
    haystack = (output or "").lower()
    fallback = "other_lean_error"
    for mode in taxonomy.get("lean_failure_modes", []):
        if mode.get("is_fallback"):
            fallback = mode["id"]
            continue
        signatures = [str(s).lower() for s in mode.get("signatures", [])]
        if any(sig in haystack for sig in signatures):
            detail = _capture_detail(mode.get("capture"), output or "")
            return mode["id"], detail
    return fallback, None


def classify(
    status: str | None,
    output: str | None,
    *,
    taxonomy: dict[str, Any],
    harness_status: str | None = None,
) -> Classification:
    outcome = map_outcome(status, taxonomy=taxonomy, harness_status=harness_status)
    outcome_id = str(outcome.get("id"))
    is_pass = bool(outcome.get("is_pass"))
    lean_mode: str | None = None
    detail: str | None = None
    if outcome_id == "lean_check_failed":
        lean_mode, detail = classify_lean_output(output or "", taxonomy=taxonomy)
    return Classification(outcome=outcome_id, is_pass=is_pass, lean_failure_mode=lean_mode, detail=detail)


def iter_run_targets(artifact: dict[str, Any]) -> Iterator[dict[str, Any]]:
    """Yield {task_ref, status, output, harness_status} rows from a detailed run artifact.

    Handles the canonical run.json / verifier.json shape (verifier.targets[].output) as
    well as the legacy baseline_run shape (evaluation.failure_mode / evaluation.details).
    """
    harness_status = artifact.get("harness_status")
    verifier = artifact.get("verifier") if isinstance(artifact.get("verifier"), dict) else artifact
    targets = verifier.get("targets") if isinstance(verifier, dict) else None
    if isinstance(targets, list) and targets:
        for target in targets:
            if not isinstance(target, dict):
                continue
            yield {
                "task_ref": target.get("task_ref") or artifact.get("task_ref"),
                "status": target.get("status"),
                "output": target.get("output") or "",
                "harness_status": harness_status,
            }
        return
    evaluation = artifact.get("evaluation")
    if isinstance(evaluation, dict):
        passed = str(evaluation.get("status") or "").strip().lower() == "passed"
        status = "passed" if passed else evaluation.get("failure_mode")
        yield {
            "task_ref": artifact.get("task_ref"),
            "status": status or evaluation.get("status"),
            "output": evaluation.get("details") or "",
            "harness_status": harness_status,
        }


def _load_run(path: Path) -> dict[str, Any] | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def iter_run_files(runs_dir: Path) -> Iterator[Path]:
    """Yield one canonical artifact JSON per run directory (run.json preferred)."""
    if (runs_dir / "run.json").exists():
        yield runs_dir / "run.json"
        return
    for child in sorted(runs_dir.iterdir()):
        if child.is_dir():
            run_json = child / "run.json"
            verifier_json = child / "verifier" / "verifier.json"
            if run_json.exists():
                yield run_json
            elif verifier_json.exists():
                yield verifier_json
        elif child.suffix == ".json":
            yield child


def classify_runs_dir(runs_dir: Path, *, taxonomy: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for run_file in iter_run_files(runs_dir):
        artifact = _load_run(run_file)
        if artifact is None:
            continue
        for target in iter_run_targets(artifact):
            result = classify(
                target["status"],
                target["output"],
                taxonomy=taxonomy,
                harness_status=target.get("harness_status"),
            )
            rows.append({"task_ref": target["task_ref"], **result.as_dict()})
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("runs_dir", type=Path, help="Directory of detailed run artifacts to classify")
    parser.add_argument("--taxonomy", type=Path, default=DEFAULT_TAXONOMY)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args()

    taxonomy = load_taxonomy(args.taxonomy)
    rows = classify_runs_dir(args.runs_dir, taxonomy=taxonomy)

    if args.format == "json":
        print(json.dumps(rows, indent=2, sort_keys=True))
        return 0

    outcomes = Counter(r["outcome"] for r in rows)
    lean_modes = Counter(r["lean_failure_mode"] for r in rows if r["lean_failure_mode"])
    print(f"Classified {len(rows)} target(s) from {args.runs_dir}")
    print("Outcomes:")
    for name, count in outcomes.most_common():
        print(f"  {count:4d}  {name}")
    if lean_modes:
        print("Lean failure modes:")
        for name, count in lean_modes.most_common():
            print(f"  {count:4d}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
