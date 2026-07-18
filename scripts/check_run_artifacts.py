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
BUILTIN_FAIR_HARNESSES = {"default", "builtin-lean-lsp"}  # legacy artifacts remain readable
DEFAULT_MCP_EXECUTION_CONTRACT = "default-mcp-v1"
LEGACY_DEFAULT_IDENTITY = (1, "group/lean_tools", "builtin")
LEGACY_BUILTIN_MCP_IDENTITY = (1, "group/lean_tools_mcp", "lean-lsp-mcp")
PRE_MCP_REASONS = frozenset(
    {"dry_run", "missing_credentials", "dependency_warm_failed", "target_warm_failed"}
)
MCP_LIFECYCLE_STATUSES = frozenset({"not_attempted", "started", "completed", "impossible", "fallback"})


def _load_json(path: Path, errors: list[str]) -> object | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        errors.append(f"{path.parent}: {path.name} is not valid JSON: {exc}")
    except OSError as exc:
        errors.append(f"{path.parent}: cannot read {path.name}: {exc}")
    return None


def _has_model_or_tool_activity(value: object) -> bool:
    """Return true for durable evidence that execution passed the pre-MCP gate."""
    if isinstance(value, dict):
        for key, item in value.items():
            if key in {"requests", "tool_calls_executed", "tool_call_count", "initialization_count"}:
                if isinstance(item, (int, float)) and item > 0:
                    return True
            if key == "attempts" and isinstance(item, list) and item:
                return True
            if _has_model_or_tool_activity(item):
                return True
    elif isinstance(value, list):
        return any(_has_model_or_tool_activity(item) for item in value)
    return False


def _default_execution_identity(run: dict[str, object]) -> str:
    """Classify a default artifact from its recorded, not inferred, identity.

    The old bespoke default is readable only under its complete v1 identity.
    A current schema/contract, or any MCP identity, is always MCP-backed.  This
    intentionally leaves partial and contradictory identities untrusted.
    """
    if run.get("harness_id") != "default":
        return "not_default"
    identity = (run.get("schema_version"), run.get("track"), run.get("tool_backend"))
    if identity == LEGACY_DEFAULT_IDENTITY and "execution_contract" not in run:
        return "legacy_bespoke"
    if (
        "execution_contract" in run
        or run.get("schema_version") != 1
        or run.get("track") == "group/lean_tools_mcp"
        or run.get("tool_backend") == "lean-lsp-mcp"
    ):
        return "mcp"
    return "ambiguous"


def _is_legacy_pre_mcp_builtin_artifact(run: dict[str, object]) -> bool:
    """Recognize only the complete recorded identity of pre-lifecycle runs.

    This narrow historical form predates the canonical default execution
    contract.  It is intentionally unavailable to default artifacts and to
    records with a current schema/contract or any partial identity.
    """
    return (
        run.get("harness_id") == "builtin-lean-lsp"
        and (run.get("schema_version"), run.get("track"), run.get("tool_backend"))
        == LEGACY_BUILTIN_MCP_IDENTITY
        and "execution_contract" not in run
    )


def _has_valid_legacy_pre_mcp_exit(run: dict[str, object], response: dict[str, object]) -> bool:
    """Recognize the only historical lifecycle which predates MCP fields.

    Old builtin artifacts that deliberately stopped before MCP startup recorded
    the terminal run/response status, but not the later lifecycle fields.  Do
    not extend this exception to records which claim to have started MCP: any
    setup metadata or preflight record must still be complete and valid.
    """
    status = run.get("harness_status")
    return (
        _is_legacy_pre_mcp_builtin_artifact(run)
        and status in {"dry_run", "missing_credentials"}
        and response.get("status") == status
        and run.get("mcp_lifecycle") is None
        and response.get("mcp_lifecycle") is None
        and run.get("lean_lsp_mcp") is None
        and run.get("mcp_preflight") is None
        and run.get("provider_preflight") is None
        and not _has_model_or_tool_activity([run, response])
    )


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
    response = _load_json(run_dir / "harness-response.json", errors)
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
    if not isinstance(response, dict):
        errors.append(f"{run_dir}: harness-response.json is not an object")
        response = {}
    if not isinstance(verifier, dict):
        errors.append(f"{run_dir}: verifier/verifier.json is not an object")
        verifier = {}
    if run_dir.joinpath("grok-output.json").is_file():
        _load_json(run_dir / "grok-output.json", errors)
    for key in ("run_id", "harness_id", "track", "run_mode", "group_id", "verifier"):
        if key not in run:
            errors.append(f"{run_dir}: run.json missing {key}")
    for key in ("benchmark_budget", "operational_budget"):
        if key not in run:
            errors.append(f"{run_dir}: run.json missing {key}")
    if "benchmark_budget" not in request:
        errors.append(f"{run_dir}: harness-request.json missing benchmark_budget")
    if "operational_budget" not in request:
        errors.append(f"{run_dir}: harness-request.json missing operational_budget")
    classification = run.get("classification")
    if run.get("harness_id") in BUILTIN_FAIR_HARNESSES:
        if not isinstance(classification, dict):
            errors.append(f"{run_dir}: builtin fair run missing publication-safe classification")
        else:
            if "run_class" not in classification:
                errors.append(f"{run_dir}: classification missing run_class")
            counts = classification.get("final_class_counts")
            if not isinstance(counts, dict):
                errors.append(f"{run_dir}: classification missing final_class_counts")
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
    if run.get("harness_id") in BUILTIN_FAIR_HARNESSES and run.get("mode") == "fair" and run.get("run_mode") in {"task", "group"}:
        tool_policy = manifest.get("tool_policy")
        if not isinstance(tool_policy, dict) or tool_policy.get("generic_grindset_only") is not True:
            errors.append(f"{run_dir}: builtin fair run must record generic_grindset_only=true")
        if "max_tool_calls" not in request:
            errors.append(f"{run_dir}: builtin fair request missing max_tool_calls")
        if isinstance(response, dict) and response.get("status") == "completed":
            if "failure_counts" not in response:
                errors.append(f"{run_dir}: builtin fair response missing failure_counts")
            tasks = response.get("tasks")
            if isinstance(tasks, list):
                for task in tasks:
                    if isinstance(task, dict) and "validity" not in task:
                        errors.append(f"{run_dir}: builtin fair task missing validity metadata")
    default_identity = _default_execution_identity(run)
    if default_identity == "ambiguous":
        errors.append(f"{run_dir}: default artifact has no recognized recorded execution identity")
    if (
        default_identity == "mcp"
        and run.get("run_mode") in {"task", "group"}
        and run.get("execution_contract") != DEFAULT_MCP_EXECUTION_CONTRACT
    ):
        errors.append(f"{run_dir}: current default MCP artifact missing execution_contract {DEFAULT_MCP_EXECUTION_CONTRACT!r}")
    is_mcp_backed = (
        run.get("track") == "group/lean_tools_mcp"
        or run.get("tool_backend") == "lean-lsp-mcp"
        or default_identity in {"mcp", "ambiguous"}
    )
    if (
        is_mcp_backed
        and run.get("run_mode") in {"task", "group"}
    ):
        legacy_pre_mcp_builtin = _is_legacy_pre_mcp_builtin_artifact(run)
        if run.get("tool_backend") != "lean-lsp-mcp":
            errors.append(f"{run_dir}: canonical MCP run used non-MCP backend {run.get('tool_backend')!r}")
        valid_pre_mcp_exit = False
        if legacy_pre_mcp_builtin:
            valid_pre_mcp_exit = _has_valid_legacy_pre_mcp_exit(run, response)
        else:
            lifecycle = run.get("mcp_lifecycle")
            if not isinstance(lifecycle, dict):
                errors.append(f"{run_dir}: MCP-backed fair run missing MCP lifecycle state")
            else:
                lifecycle_status = lifecycle.get("status")
                if lifecycle_status not in MCP_LIFECYCLE_STATUSES:
                    errors.append(f"{run_dir}: invalid MCP lifecycle status {lifecycle_status!r}")
                elif lifecycle_status == "not_attempted":
                    reason = lifecycle.get("reason")
                    if reason not in PRE_MCP_REASONS:
                        errors.append(f"{run_dir}: invalid pre-MCP reason {reason!r}")
                    elif (
                        run.get("lean_lsp_mcp") is not None
                        or run.get("mcp_preflight") is not None
                        or run.get("provider_preflight") is not None
                        or _has_model_or_tool_activity([run, response])
                    ):
                        errors.append(f"{run_dir}: pre-MCP lifecycle claim has model or tool activity")
                    else:
                        valid_pre_mcp_exit = True
                elif lifecycle_status in {"impossible", "fallback"}:
                    errors.append(f"{run_dir}: MCP {lifecycle_status} lifecycle state is not valid for canonical runs")
        if not valid_pre_mcp_exit:
            # An MCP launch was attempted (or the artifact cannot prove a
            # legitimate pre-launch exit), so require full lifecycle evidence.
            metadata = run.get("lean_lsp_mcp")
            if not isinstance(metadata, dict):
                errors.append(f"{run_dir}: MCP-backed fair run missing MCP lifecycle metadata")
            else:
                for key in (
                    "package_version",
                    "minimum_lean_version",
                    "workspace_lean_version",
                    "initialization_count",
                    "tool_call_count",
                    "tool_call_counts",
                    "tool_call_duration_seconds",
                    "clean_shutdown",
                ):
                    if key not in metadata:
                        errors.append(f"{run_dir}: MCP lifecycle metadata missing {key}")
            if not isinstance(run.get("mcp_preflight"), dict):
                errors.append(f"{run_dir}: MCP-backed fair run missing MCP preflight result")
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
                if run.get("harness_id") in BUILTIN_FAIR_HARNESSES and child.get("mode") != run.get("mode"):
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


def self_test() -> list[str]:
    """Validator sanity check: a malformed run.json must be reported cleanly."""
    import shutil
    import tempfile

    errors: list[str] = []
    temp_root = Path(tempfile.mkdtemp(prefix="verity-artifact-helper-"))
    try:
        run_dir = temp_root / "run"
        (run_dir / "verifier").mkdir(parents=True)
        for rel in (
            "workspace-manifest.json",
            "harness-request.json",
            "harness-response.json",
            "stdout.txt",
            "stderr.txt",
            "report.md",
            "verifier/verifier.json",
        ):
            path = run_dir / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("{}\n", encoding="utf-8")
        (run_dir / "run.json").write_text("{bad-json\n", encoding="utf-8")
        artifact_errors = check_run(run_dir)
        if not artifact_errors or "run.json is not valid JSON" not in artifact_errors[0]:
            errors.append("artifact validator did not report malformed run.json cleanly")
    finally:
        shutil.rmtree(temp_root, ignore_errors=True)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate normalized benchmark run artifact directories")
    parser.add_argument("runs", nargs="*", type=Path)
    parser.add_argument("--self-test", action="store_true", help="run the validator sanity check instead of validating run dirs")
    args = parser.parse_args()
    if args.self_test:
        failures = self_test()
        if failures:
            print("\n".join(failures))
            return 1
        print("artifact validator self-test passed")
        return 0
    if not args.runs:
        parser.error("provide run directories or --self-test")
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
