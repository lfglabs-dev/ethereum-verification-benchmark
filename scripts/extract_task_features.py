#!/usr/bin/env python3
"""Extract per-task and per-model features for the Verity task taxonomy layer.

Inputs (all keyed by ``task_ref``):
  * a benchmark version manifest (``benchmark-versions/<v>.json``) -- static task metadata
    (proof_family, property_class, category, difficulty, file lists, fingerprints);
  * a results manifest (``results/manifests/<v>.json``) -- the per-model pass/fail and
    token-usage matrix that is committed to the repo;
  * zero or more directories of *detailed* run artifacts (extracted release tarballs) --
    optional enrichment that adds the parsed Lean failure mode per task/model.

Outputs:
  * ``analysis/task_features.json`` -- per-task aggregate + per-model detail;
  * ``analysis/model_task_matrix.csv`` -- models x tasks pass/fail/usage matrix.

The features describe *what the models did*, not the benchmark definition. This layer is
decoupled from versioning: it records each task's fingerprint so downstream consumers can
detect drift, but it is never an input to ``result_key`` and never triggers reruns.
"""
from __future__ import annotations

import argparse
import csv
import json
import statistics
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from classify_failures import (  # noqa: E402
    COMPLETED_HARNESS_STATUSES,
    artifact_run_id,
    classify,
    iter_run_files,
    iter_run_targets,
    load_taxonomy,
)

DEFAULT_VERSION = ROOT / "benchmark-versions" / "v0.1.json"
DEFAULT_RESULTS = ROOT / "results" / "manifests" / "v0.1.json"
DEFAULT_FAILURE_MODES = ROOT / "analysis" / "failure_modes.json"
DEFAULT_OUT_FEATURES = ROOT / "analysis" / "task_features.json"
DEFAULT_OUT_MATRIX = ROOT / "analysis" / "model_task_matrix.csv"

STATIC_METADATA_FIELDS = (
    "family_id",
    "proof_family",
    "property_class",
    "category",
    "difficulty",
    "track",
    "theorem_name",
)


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def is_valid_attempt(result: dict[str, Any]) -> bool:
    """A task result counts as a real model attempt we can score.

    We require the harness to have completed and the verifier to have produced output.
    Errored/incomplete/zero-output rows are excluded from skill conclusions (they reflect
    transport or infrastructure problems, not model reasoning).
    """
    if str(result.get("harness_status") or "").strip().lower() not in COMPLETED_HARNESS_STATUSES:
        return False
    return bool(result.get("verifier_output_present", False))


def model_attempts(manifest: dict[str, Any]) -> dict[str, dict[str, dict[str, Any]]]:
    """model_id -> {task_ref -> task_result} restricted to valid attempts."""
    out: dict[str, dict[str, dict[str, Any]]] = {}
    for model in manifest.get("models", []):
        model_id = model.get("model_id")
        if not model_id:
            continue
        rows: dict[str, dict[str, Any]] = {}
        for result in model.get("task_results", []):
            task_ref = result.get("task_ref")
            if task_ref and is_valid_attempt(result):
                rows[str(task_ref)] = result
        out[str(model_id)] = rows
    return out


def select_cohort(
    attempts: dict[str, dict[str, dict[str, Any]]],
    task_refs: set[str],
    *,
    min_coverage: float,
) -> list[str]:
    """Models that attempted at least ``min_coverage`` of the version's tasks.

    The cohort is the apples-to-apples comparison set: every cohort model has a verdict on
    (almost) every task, so pass-rate and divisiveness are not skewed by partial coverage.
    """
    total = len(task_refs) or 1
    cohort = [
        model
        for model, rows in attempts.items()
        if len(task_refs & set(rows)) / total >= min_coverage
    ]
    return sorted(cohort)


def usage_total_tokens(result: dict[str, Any]) -> int:
    usage = result.get("usage") if isinstance(result.get("usage"), dict) else {}
    if "total_tokens" in usage:
        return int(usage.get("total_tokens") or 0)
    return int(usage.get("prompt_tokens") or 0) + int(usage.get("completion_tokens") or 0)


def load_enrichment(runs_dirs: list[Path], taxonomy: dict[str, Any]) -> dict[tuple[str, str, str], dict[str, Any]]:
    """(model_id, task_ref, run_id) -> classification dict from detailed artifacts.

    Run ids are part of the key because benchmark manifests select a specific reusable
    artifact. Backfills and retries can leave multiple artifacts for the same model/task,
    and attaching the wrong detailed artifact would mix pass/fail and failure-mode data.
    """
    enrichment: dict[tuple[str, str, str], dict[str, Any]] = {}
    for runs_dir in runs_dirs:
        if not runs_dir.exists():
            print(f"warning: runs dir not found, skipping: {runs_dir}", file=sys.stderr)
            continue
        for run_file in iter_run_files(runs_dir):
            try:
                artifact = json.loads(run_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            model_id = artifact.get("model")
            run_id = artifact_run_id(artifact, run_file)
            for target in iter_run_targets(artifact):
                task_ref = target.get("task_ref")
                if not (model_id and task_ref and run_id):
                    continue
                result = classify(
                    target.get("status"),
                    target.get("output"),
                    taxonomy=taxonomy,
                    harness_status=target.get("harness_status"),
                )
                enrichment[(str(model_id), str(task_ref), str(run_id))] = result.as_dict()
    return enrichment


def divisiveness(pass_rate: float) -> float:
    """0 when a cohort is unanimous (all pass or all fail), 1 when evenly split."""
    return round(1.0 - abs(2.0 * pass_rate - 1.0), 4)


def build_features(
    version: dict[str, Any],
    results: dict[str, Any],
    *,
    enrichment: dict[tuple[Any, ...], dict[str, Any]],
    min_coverage: float,
) -> dict[str, Any]:
    tasks = {str(t["task_ref"]): t for t in version.get("tasks", [])}
    task_refs = set(tasks)
    attempts = model_attempts(results)
    cohort = select_cohort(attempts, task_refs, min_coverage=min_coverage)
    all_models = sorted(attempts)

    task_features: list[dict[str, Any]] = []
    for task_ref in sorted(task_refs):
        meta = tasks[task_ref]
        per_model: dict[str, dict[str, Any]] = {}
        tokens: list[int] = []
        requests: list[int] = []
        attempt_count = 0
        pass_count = 0
        failure_modes: Counter[str] = Counter()

        for model in all_models:
            row = attempts[model].get(task_ref)
            if row is None:
                continue
            attempt_count += 1
            passed = bool(row.get("passed"))
            pass_count += int(passed)
            total_tokens = usage_total_tokens(row)
            req = int((row.get("usage") or {}).get("requests") or 0)
            tokens.append(total_tokens)
            requests.append(req)
            detail = {
                "passed": passed,
                "total_tokens": total_tokens,
                "requests": req,
                "harness_status": row.get("harness_status"),
            }
            run_id = row.get("run_id")
            enriched = None
            if run_id:
                enriched = enrichment.get((model, task_ref, str(run_id)))
            if enriched is None:
                # Backwards-compatible path for tests and hand-authored fixtures that
                # intentionally do not model concrete artifact selection.
                enriched = enrichment.get((model, task_ref))
            if enriched is not None:
                detail["outcome"] = enriched["outcome"]
                detail["lean_failure_mode"] = enriched["lean_failure_mode"]
                detail["detail"] = enriched["detail"]
                if not passed and enriched["lean_failure_mode"]:
                    failure_modes[enriched["lean_failure_mode"]] += 1
                elif (
                    not passed
                    and enriched["outcome"] not in {"lean_check_failed", "passed"}
                ):
                    failure_modes[enriched["outcome"]] += 1
            per_model[model] = detail

        cohort_rows = [(m, attempts[m].get(task_ref)) for m in cohort]
        cohort_attempts = [r for _, r in cohort_rows if r is not None]
        cohort_passes = sum(1 for r in cohort_attempts if r.get("passed"))
        cohort_size = len(cohort_attempts)
        cohort_pass_rate = round(cohort_passes / cohort_size, 4) if cohort_size else None

        feature = {
            "task_ref": task_ref,
            "task_fingerprint": meta.get("task_fingerprint"),
            "task_interface_id": meta.get("task_interface_id"),
            **{field: meta.get(field) for field in STATIC_METADATA_FIELDS},
            "static": {
                "n_implementation_files": len(meta.get("implementation_files") or []),
                "n_specification_files": len(meta.get("specification_files") or []),
                "n_editable_files": len(meta.get("editable_files") or []),
            },
            "attempts": attempt_count,
            "passes": pass_count,
            "pass_rate": round(pass_count / attempt_count, 4) if attempt_count else None,
            "cohort_size": cohort_size,
            "cohort_passes": cohort_passes,
            "cohort_pass_rate": cohort_pass_rate,
            "divisiveness": divisiveness(cohort_pass_rate) if cohort_pass_rate is not None else None,
            "mean_total_tokens": round(statistics.mean(tokens), 1) if tokens else None,
            "median_total_tokens": int(statistics.median(tokens)) if tokens else None,
            "mean_requests": round(statistics.mean(requests), 1) if requests else None,
            "failure_modes": dict(sorted(failure_modes.items())),
            "per_model": per_model,
        }
        task_features.append(feature)

    return {
        "schema_version": 1,
        "benchmark_version": version.get("benchmark_version"),
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "task_count": len(task_features),
        "models": all_models,
        "cohort": cohort,
        "cohort_min_coverage": min_coverage,
        "enrichment_present": bool(enrichment),
        "enriched_pairs": len(enrichment),
        "tasks": task_features,
    }


def write_matrix(features: dict[str, Any], path: Path) -> None:
    models = features["models"]
    fieldnames = [
        "task_ref",
        "family_id",
        "proof_family",
        "property_class",
        "difficulty",
        *models,
        "attempts",
        "passes",
        "pass_rate",
        "cohort_pass_rate",
        "divisiveness",
        "mean_total_tokens",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for task in features["tasks"]:
            row = {
                "task_ref": task["task_ref"],
                "family_id": task.get("family_id"),
                "proof_family": task.get("proof_family"),
                "property_class": task.get("property_class"),
                "difficulty": task.get("difficulty"),
                "attempts": task["attempts"],
                "passes": task["passes"],
                "pass_rate": task["pass_rate"],
                "cohort_pass_rate": task["cohort_pass_rate"],
                "divisiveness": task["divisiveness"],
                "mean_total_tokens": task["mean_total_tokens"],
            }
            for model in models:
                detail = task["per_model"].get(model)
                if detail is None:
                    row[model] = ""
                else:
                    row[model] = "pass" if detail["passed"] else "fail"
            writer.writerow(row)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", type=Path, default=DEFAULT_VERSION)
    parser.add_argument("--results", type=Path, default=DEFAULT_RESULTS)
    parser.add_argument("--failure-modes", type=Path, default=DEFAULT_FAILURE_MODES)
    parser.add_argument(
        "--runs-dir",
        type=Path,
        action="append",
        default=None,
        help="Directory of detailed run artifacts for failure-mode enrichment (repeatable).",
    )
    parser.add_argument(
        "--min-coverage",
        type=float,
        default=1.0,
        help="Fraction of tasks a model must have attempted to join the comparison cohort.",
    )
    parser.add_argument("--out-features", type=Path, default=DEFAULT_OUT_FEATURES)
    parser.add_argument("--out-matrix", type=Path, default=DEFAULT_OUT_MATRIX)
    args = parser.parse_args()

    taxonomy = load_taxonomy(args.failure_modes)
    enrichment = load_enrichment(args.runs_dir or [], taxonomy)
    features = build_features(
        load_json(args.version),
        load_json(args.results),
        enrichment=enrichment,
        min_coverage=args.min_coverage,
    )

    args.out_features.parent.mkdir(parents=True, exist_ok=True)
    args.out_features.write_text(json.dumps(features, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_matrix(features, args.out_matrix)

    print(f"tasks: {features['task_count']}  models: {len(features['models'])}  cohort: {len(features['cohort'])}")
    print(f"enriched (model,task) pairs: {features['enriched_pairs']}")
    print(f"wrote {args.out_features}")
    print(f"wrote {args.out_matrix}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
