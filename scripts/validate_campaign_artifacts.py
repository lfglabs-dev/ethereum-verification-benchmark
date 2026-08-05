#!/usr/bin/env python3
"""Validate a campaign artifact directory against the benchmark contract.

Usage:
  python3 scripts/validate_campaign_artifacts.py <run-dir> [<run-dir> ...]
  python3 scripts/validate_campaign_artifacts.py --self-test
  python3 scripts/validate_campaign_artifacts.py --summary runs/2026-08-05T03/full263

A "campaign artifact directory" is the per-run directory emitted by the harness
for a single benchmark task.  The script checks that:

  - every required file is present (the eight files listed in
    ``REQUIRED_FILES``);
  - ``run.json``, ``harness-request.json``, ``harness-response.json``,
    ``workspace-manifest.json`` and ``verifier/verifier.json`` parse as JSON;
  - the verifier outcome is classifiable against the taxonomy in
    ``analysis/failure_modes.json`` (handled by
    ``scripts/classify_failures.py`` so we stay in sync);
  - the four count buckets FULL-263 owners care about can be derived:
    ``solved`` (passed), ``genuine_fail`` (lean_check_failed / theorem_missing
    / theorem_statement_mismatch / forbidden_placeholder / hidden_import /
    syntax_error / unknown_identifier / sorry_used / no_submission / timeout),
    ``infra_invalid`` (infra_invalid / harness_error / verifier_infra_error /
    dependency_checkout_failed), and ``pending`` (anything else, including
    runs whose outcome cannot be classified).

Exit status is non-zero if at least one run is missing a required artifact,
if any required JSON file fails to parse, if at least one run falls in the
``pending`` bucket and ``--strict`` was requested, or if any run is a
``pending`` classification under ``--all-resolved``.

The script intentionally stays independent of the harness CLI: any producer
that lays out the eight files can be validated against this contract, which
is the prerequisite the FULL-263 nested campaign needs before it can run a
fair comparison across the model matrix.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from classify_failures import (  # noqa: E402  (sys.path manipulated above)
    Classification,
    map_outcome,
    load_taxonomy,
    provider_failure_reason,
)

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

PENDING_OUTCOMES = frozenset({"unknown_verifier_status"})
INFRA_INVALID_OUTCOMES = frozenset(
    {
        "infra_invalid",
        "harness_error",
        "verifier_infra_error",
        "dependency_checkout_failed",
    }
)
SOLVED_OUTCOMES = frozenset({"passed"})
GENUINE_FAIL_OUTCOMES = frozenset(
    {
        "lean_check_failed",
        "theorem_missing",
        "theorem_statement_mismatch",
        "forbidden_placeholder",
        "hidden_import",
        "timeout",
        "no_submission",
    }
)


@dataclass(frozen=True)
class RunReport:
    run_dir: Path
    missing: tuple[str, ...]
    parse_errors: tuple[str, ...]
    outcome: str
    is_pass: bool
    lean_failure_mode: str | None
    infra_reason: str | None

    @property
    def bucket(self) -> str:
        if self.outcome in SOLVED_OUTCOMES:
            return "solved"
        if self.outcome in GENUINE_FAIL_OUTCOMES:
            return "genuine_fail"
        if self.outcome in INFRA_INVALID_OUTCOMES:
            return "infra_invalid"
        return "pending"

    def as_dict(self) -> dict[str, Any]:
        return {
            "run_dir": str(self.run_dir),
            "missing": list(self.missing),
            "parse_errors": list(self.parse_errors),
            "outcome": self.outcome,
            "is_pass": self.is_pass,
            "lean_failure_mode": self.lean_failure_mode,
            "infra_reason": self.infra_reason,
            "bucket": self.bucket,
        }


def _load_json(path: Path, errors: list[str]) -> object | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        errors.append(f"{path.parent}/{path.name}: invalid JSON: {exc}")
    except OSError as exc:
        errors.append(f"{path.parent}/{path.name}: cannot read: {exc}")
    return None


def _has_tool_activity(value: object) -> bool:
    """Mirror scripts/check_run_artifacts.py's pre-MCP gate heuristic."""
    if isinstance(value, dict):
        for key, item in value.items():
            if key in {
                "requests",
                "tool_calls_executed",
                "tool_call_count",
                "initialization_count",
            } and isinstance(item, (int, float)) and item > 0:
                return True
            if key == "attempts" and isinstance(item, list) and item:
                return True
            if _has_tool_activity(item):
                return True
    elif isinstance(value, list):
        return any(_has_tool_activity(item) for item in value)
    return False


def validate_run(run_dir: Path, taxonomy: dict[str, Any]) -> RunReport:
    missing: list[str] = []
    parse_errors: list[str] = []
    for rel in REQUIRED_FILES:
        if not (run_dir / rel).is_file():
            missing.append(rel)

    run_obj = _load_json(run_dir / "run.json", parse_errors) if not missing else None
    request_obj = (
        _load_json(run_dir / "harness-request.json", parse_errors) if not missing else None
    )
    response_obj = (
        _load_json(run_dir / "harness-response.json", parse_errors) if not missing else None
    )
    workspace_obj = (
        _load_json(run_dir / "workspace-manifest.json", parse_errors)
        if not missing
        else None
    )
    verifier_obj = (
        _load_json(run_dir / "verifier" / "verifier.json", parse_errors)
        if not missing
        else None
    )

    outcome = "unknown_verifier_status"
    is_pass = False
    lean_failure_mode: str | None = None
    infra_reason: str | None = None

    if verifier_obj is not None and isinstance(verifier_obj, dict):
        verifier_status = str(verifier_obj.get("verifier_status", "")).strip()
        harness_status = None
        if isinstance(run_obj, dict):
            harness_status = run_obj.get("harness_status")
        classification = map_outcome(
            verifier_status or None,
            taxonomy=taxonomy,
            harness_status=harness_status,
        )
        outcome = classification.get("id") or "unknown_verifier_status"
        is_pass = bool(classification.get("is_pass", False))
        if outcome == "lean_check_failed":
            stderr_text = ""
            stdout_text = ""
            try:
                stderr_text = (run_dir / "stderr.txt").read_text(
                    encoding="utf-8", errors="replace"
                )
            except OSError:
                pass
            try:
                stdout_text = (run_dir / "stdout.txt").read_text(
                    encoding="utf-8", errors="replace"
                )
            except OSError:
                pass
            modes = taxonomy.get("lean_failure_modes", [])
            case_sensitive = bool(taxonomy.get("matching", {}).get("case_sensitive", False))
            haystack = f"{stdout_text}\n{stderr_text}"
            for mode in modes:
                signatures = mode.get("signatures", [])
                if not isinstance(signatures, list):
                    continue
                target = haystack if case_sensitive else haystack.lower()
                for sig in signatures:
                    if not isinstance(sig, str):
                        continue
                    needle = sig if case_sensitive else sig.lower()
                    if needle in target:
                        lean_failure_mode = mode.get("id")
                        break
                if lean_failure_mode is not None:
                    break

    if outcome in {"harness_error", "verifier_infra_error", "infra_invalid"}:
        if isinstance(response_obj, dict):
            infra_reason = provider_failure_reason(response_obj, run_dir)
        elif isinstance(request_obj, dict):
            infra_reason = provider_failure_reason(request_obj, run_dir)
    elif outcome == "harness_error" and isinstance(run_obj, dict):
        if not _has_tool_activity(run_obj):
            infra_reason = "no_durable_tool_activity"

    return RunReport(
        run_dir=run_dir,
        missing=tuple(missing),
        parse_errors=tuple(parse_errors),
        outcome=outcome,
        is_pass=is_pass,
        lean_failure_mode=lean_failure_mode,
        infra_reason=infra_reason,
    )


def summarise(reports: Iterable[RunReport]) -> dict[str, Any]:
    counts: Counter[str] = Counter()
    for report in reports:
        counts[report.bucket] += 1
    total = sum(counts.values())
    return {
        "total": total,
        "solved": counts["solved"],
        "genuine_fail": counts["genuine_fail"],
        "infra_invalid": counts["infra_invalid"],
        "pending": counts["pending"],
    }


def _self_test() -> int:
    """Cover the four buckets without writing a fake campaign on disk."""
    taxonomy = load_taxonomy()
    sample = {
        "passed": ("verifier_status", "passed"),
        "lean_check_failed": ("verifier_status", "lean_check_failed"),
        "infra_invalid": ("verifier_status", "request_timeout"),
        "unknown_verifier_status": ("verifier_status", "weird_new_value"),
    }
    for label, (key, value) in sample.items():
        result = map_outcome(value, taxonomy=taxonomy, harness_status="completed")
        expected = label
        if result.get("id") != expected:
            raise SystemExit(f"self-test: {value} -> {result.get('id')} != {expected}")
    tmp = ROOT / "runs" / "__validate_self_test"
    if tmp.exists():
        for child in tmp.iterdir():
            if child.is_file():
                child.unlink()
            else:
                for sub in child.rglob("*"):
                    if sub.is_file():
                        sub.unlink()
    else:
        tmp.mkdir(parents=True)
    for rel in REQUIRED_FILES:
        (tmp / rel).parent.mkdir(parents=True, exist_ok=True)
        if rel.endswith(".json"):
            (tmp / rel).write_text("{}", encoding="utf-8")
        else:
            (tmp / rel).write_text("", encoding="utf-8")
    report = validate_run(tmp, taxonomy)
    if report.missing:
        raise SystemExit(f"self-test: missing files reported: {report.missing}")
    print("self-test OK:", report.bucket)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "run_dirs",
        nargs="*",
        type=Path,
        help="One or more per-task run directories produced by the harness.",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Exercise the classifier without scanning a real campaign.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit non-zero as soon as a pending run is found.",
    )
    parser.add_argument(
        "--all-resolved",
        action="store_true",
        help="Require every run to land in solved/genuine_fail/infra_invalid.",
    )
    parser.add_argument(
        "--summary",
        action="store_true",
        help="Print only the four-bucket summary as JSON.",
    )
    args = parser.parse_args()

    if args.self_test:
        return _self_test()
    if not args.run_dirs:
        parser.error("at least one run directory is required (or pass --self-test)")

    taxonomy = load_taxonomy()
    reports = [validate_run(path, taxonomy) for path in args.run_dirs]
    counts = summarise(reports)

    if args.summary:
        print(json.dumps(counts, indent=2, sort_keys=True))
    else:
        print(json.dumps(
            {
                "summary": counts,
                "runs": [report.as_dict() for report in reports],
            },
            indent=2,
            sort_keys=True,
        ))

    problems = 0
    for report in reports:
        if report.missing or report.parse_errors:
            problems += 1
            continue
        if report.bucket == "pending" and (args.strict or args.all_resolved):
            problems += 1
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
