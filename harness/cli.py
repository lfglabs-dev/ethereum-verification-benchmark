from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


def _load_dotenv() -> None:
    env_path = Path(__file__).resolve().parent.parent / ".env"
    if not env_path.is_file():
        return
    for raw_line in env_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip()
        if not key or key in os.environ:
            continue
        if (value.startswith('"') and value.endswith('"')) or (value.startswith("'") and value.endswith("'")):
            value = value[1:-1]
        os.environ[key] = value


_load_dotenv()

try:
    from .classification import classify_run
    from .budgets import (
        BUDGET_PROFILES,
        budget_artifact,
        budget_profile,
        dependency_warm_timeout_seconds,
    )
    from .manifests import (
        filter_group_to_task,
        group_id_from_task_ref,
        group_to_json,
        list_groups,
        load_group,
    )
    from .paths import RESULTS_DIR
    from .reports import compare_runs, write_run_report
    from .runners.lean_tools import _role_config as default_role_config
    from .runners.lean_tools_mcp import run_group as run_lean_tools_mcp_group
    from .workspace_builder import warm_public_dependencies, warm_result_failed
except ImportError:
    from classification import classify_run
    from budgets import (
        BUDGET_PROFILES,
        budget_artifact,
        budget_profile,
        dependency_warm_timeout_seconds,
    )
    from manifests import (
        filter_group_to_task,
        group_id_from_task_ref,
        group_to_json,
        list_groups,
        load_group,
    )
    from paths import RESULTS_DIR
    from reports import compare_runs, write_run_report
    from runners.lean_tools import _role_config as default_role_config
    from runners.lean_tools_mcp import run_group as run_lean_tools_mcp_group
    from workspace_builder import warm_public_dependencies, warm_result_failed


def warm_task_dependencies(task_ref: str, *, suite: str, timeout_seconds: int) -> tuple[int, Path]:
    """Explicit setup phase, intentionally separate from per-task model time."""
    group = filter_group_to_task(load_group(group_id_from_task_ref(task_ref), suite), task_ref)
    started_at = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    artifact_dir = RESULTS_DIR / "setup" / f"{started_at}-dependency-warm-{task_ref.replace('/', '__')}"
    artifact_dir.mkdir(parents=True, exist_ok=True)
    results = warm_public_dependencies(
        group,
        timeout_seconds=timeout_seconds,
        log_path=artifact_dir / "dependency-warm.log",
    )
    payload = {
        "schema_version": 1,
        "task_ref": task_ref,
        "timeout_seconds_per_module": timeout_seconds,
        "results": results,
        "passed": bool(results) and not any(warm_result_failed(item) for item in results),
    }
    (artifact_dir / "result.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return (0 if payload["passed"] else 1), artifact_dir


def run_group(
    group_id: str,
    harness: str,
    suite: str,
    keep_workspace: bool,
    dry_run: bool,
    max_attempts: int,
    max_turns: int,
    shell_timeout_seconds: int,
    max_tool_calls: int,
    task_ref: str | None = None,
    preflight_verified: bool = False,
) -> tuple[int, Path]:
    if suite == "v0.2" and not preflight_verified:
        # This is intentionally before workspace creation, runner dispatch, or
        # provider setup.  The validator is structural-only and process-cache
        # free so direct API callers cannot bypass the release preflight.
        from scripts.validate_v02_reference_contract import ensure_structural_contract

        ensure_structural_contract()
    if harness == "default":
        return run_lean_tools_mcp_group(
            group_id,
            suite=suite,
            keep_workspace=keep_workspace,
            dry_run=dry_run,
            max_attempts=max_attempts,
            max_turns=max_turns,
            max_tool_calls=max_tool_calls,
            task_ref=task_ref,
        )
    raise ValueError("only the canonical MCP-backed default harness is supported")
    

def _load_child_run(run_dir: Path) -> dict:
    return json.loads((run_dir / "run.json").read_text(encoding="utf-8"))


def _suite_group_status(child: dict) -> str:
    score = child.get("score", {})
    passed = int(score.get("passed_targets", 0))
    total = int(score.get("total_targets", 0))
    if total > 0 and passed == total and child.get("harness_status") in {"completed", "dry_run"}:
        return "passed"
    if child.get("harness_status") == "harness_error":
        return "harness_error"
    if passed > 0:
        return "partial"
    return "lean_check_failed"


def run_suite(
    *,
    suite: str,
    harness: str,
    keep_workspace: bool,
    dry_run: bool,
    max_attempts: int,
    max_turns: int,
    shell_timeout_seconds: int,
    max_tool_calls: int,
) -> tuple[int, Path]:
    if suite == "v0.2":
        from scripts.validate_v02_reference_contract import ensure_structural_contract

        ensure_structural_contract()
    start = time.time()
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    builtin_harness = harness == "default"
    mode_slug = "-fair" if builtin_harness else ""
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{harness}{mode_slug}-suite-{suite}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "verifier").mkdir(exist_ok=True)

    groups = list_groups(suite)
    child_runs: list[dict] = []
    exit_code = 0
    total_groups = len(groups)
    for index, group in enumerate(groups, start=1):
        print(f"[{index}/{total_groups}] start {group.group_id}", flush=True)
        code, child_dir = run_group(
            group.group_id, harness, suite, keep_workspace, dry_run,
            max_attempts, max_turns, shell_timeout_seconds, max_tool_calls,
            preflight_verified=(suite == "v0.2"),
        )
        child_run = _load_child_run(child_dir)
        score = child_run.get("verifier", {}).get("score", {})
        passed = score.get("passed_targets", 0)
        total = score.get("total_targets", 0)
        print(f"[{index}/{total_groups}] done {group.group_id} {passed}/{total} {child_dir}", flush=True)
        if code != 0:
            exit_code = 1
        child_runs.append(
            {
                "group_id": child_run.get("group_id"),
                "run_id": child_run.get("run_id"),
                "artifact": str(child_dir),
                "track": child_run.get("track"),
                "model": child_run.get("model"),
                "mode": child_run.get("mode"),
                "harness_status": child_run.get("harness_status"),
                "score": child_run.get("verifier", {}).get("score", {}),
                "classification": child_run.get("classification"),
            }
        )

    points_earned = sum(int(item.get("score", {}).get("points_earned", 0)) for item in child_runs)
    points_possible = sum(int(item.get("score", {}).get("points_possible", 0)) for item in child_runs)
    passed_targets = sum(int(item.get("score", {}).get("passed_targets", 0)) for item in child_runs)
    total_targets = sum(int(item.get("score", {}).get("total_targets", 0)) for item in child_runs)
    verifier = {
        "score": {
            "points_earned": points_earned,
            "points_possible": points_possible,
            "passed_targets": passed_targets,
            "total_targets": total_targets,
        },
        "targets": [
            {
                "task_ref": item.get("group_id"),
                "status": _suite_group_status(item),
                "points_earned": item.get("score", {}).get("points_earned", 0),
                "points_possible": item.get("score", {}).get("points_possible", 0),
                "artifact": item.get("artifact"),
            }
            for item in child_runs
        ],
        "groups": child_runs,
    }
    final_counts: Counter[str] = Counter()
    reusable_target_count = 0
    non_reusable_target_count = 0
    child_classifications = []
    for child in child_runs:
        child_classification = child.get("classification")
        if not isinstance(child_classification, dict):
            continue
        child_classifications.append(child_classification)
        counts = child_classification.get("final_class_counts")
        if isinstance(counts, dict):
            for key, value in counts.items():
                final_counts[str(key)] += int(value)
        reusable_target_count += int(child_classification.get("reusable_target_count") or 0)
        non_reusable_target_count += int(child_classification.get("non_reusable_target_count") or 0)
    if final_counts and final_counts.get("INFRA_INVALID", 0) == sum(final_counts.values()):
        run_class = "INFRA_INVALID"
    elif final_counts.get("INFRA_INVALID", 0):
        run_class = "MIXED_INFRA_INVALID"
    elif final_counts.get("SOLVED", 0) == sum(final_counts.values()) and final_counts:
        run_class = "SOLVED"
    else:
        run_class = "GENUINE_FAIL"
    classification = {
        "schema_version": 1,
        "policy": classify_run(verifier, []).get("policy"),
        "run_class": run_class,
        "reusable": bool(final_counts) and non_reusable_target_count == 0,
        "final_class_counts": dict(sorted(final_counts.items())),
        "reusable_target_count": reusable_target_count,
        "non_reusable_target_count": non_reusable_target_count,
        "children": child_classifications,
    }
    harness_status = "completed" if exit_code == 0 else "completed_with_failures"
    child_tracks = sorted({str(item.get("track")) for item in child_runs if item.get("track")})
    child_models = sorted({str(item.get("model")) for item in child_runs if item.get("model")})
    role_config = default_role_config() if builtin_harness else None
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": harness,
        "model": child_models[0] if len(child_models) == 1 else "suite-aggregate",
        "track": child_tracks[0] if len(child_tracks) == 1 else "mixed",
        "mode": "fair" if builtin_harness else None,
        "run_mode": "suite",
        "group_id": None,
        "task_ref": None,
        "suite": suite,
        "started_at": started_at,
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": harness_status,
        "harness_exit_code": exit_code,
        "child_runs": child_runs,
        "role_config": role_config,
        "benchmark_budget": {
            "max_attempts": max_attempts,
            "max_tool_calls": max_tool_calls,
            "max_turns": max_turns,
            "completion_token_budget": int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0")),
        },
        "operational_budget": budget_artifact(
            budget_profile("quick"),
            token_budget=int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0")),
        )["operational_budget"],
        "classification": classification,
        "verifier": verifier,
    }
    (run_dir / "run.json").write_text(json.dumps(run, indent=2) + "\n", encoding="utf-8")
    (run_dir / "verifier" / "verifier.json").write_text(json.dumps(verifier, indent=2) + "\n", encoding="utf-8")
    (run_dir / "harness-request.json").write_text(
        json.dumps(
            {
                "suite": suite,
                "harness": harness,
                "dry_run": dry_run,
                "max_attempts": max_attempts,
                "max_turns": max_turns,
                "shell_timeout_seconds": shell_timeout_seconds,
                "mode": "fair" if builtin_harness else None,
                "max_tool_calls": max_tool_calls if builtin_harness else None,
                "role_config": role_config,
                "benchmark_budget": {
                    "max_attempts": max_attempts,
                    "max_tool_calls": max_tool_calls,
                    "max_turns": max_turns,
                    "completion_token_budget": int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0")),
                },
                "operational_budget": budget_artifact(
                    budget_profile("quick"),
                    token_budget=int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0")),
                )["operational_budget"],
                "groups": [group_to_json(group) for group in groups],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (run_dir / "harness-response.json").write_text(
        json.dumps({"status": harness_status, "child_runs": child_runs}, indent=2) + "\n",
        encoding="utf-8",
    )
    (run_dir / "workspace-manifest.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "kind": "suite-aggregate",
                "files": [{"path": str(Path(item["artifact"]) / "run.json")} for item in child_runs],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (run_dir / "stdout.txt").write_text("\n".join(str(item["artifact"]) for item in child_runs) + "\n", encoding="utf-8")
    (run_dir / "stderr.txt").write_text("", encoding="utf-8")
    write_run_report(run_dir, run)
    return exit_code, run_dir


def _apply_budget(args: argparse.Namespace) -> None:
    profile = budget_profile(args.budget)
    if args.max_attempts is None:
        args.max_attempts = profile.max_attempts
    if args.max_tool_calls is None:
        args.max_tool_calls = profile.max_tool_calls
    if args.max_turns is None:
        args.max_turns = profile.max_turns
    if args.shell_timeout_seconds is None:
        args.shell_timeout_seconds = profile.shell_timeout_seconds


def main() -> int:
    parser = argparse.ArgumentParser(description="Ethereum verification benchmark group CLI")
    sub = parser.add_subparsers(dest="command", required=True)

    list_parser = sub.add_parser("list")
    list_parser.add_argument("--suite", choices=["active", "backlog", "all", "v0.2"], default="active")
    list_parser.add_argument("--unit", choices=["group", "task"], default="group")
    list_parser.add_argument("--json", action="store_true")

    group_parser = sub.add_parser("run-group")
    group_parser.add_argument("group_id")
    group_parser.add_argument("--suite", choices=["active", "backlog", "all", "v0.2"], default="active")
    group_parser.add_argument("--harness", default="default", choices=["default"], help="canonical MCP-backed harness")
    group_parser.add_argument("--keep-workspace", action="store_true")
    group_parser.add_argument("--dry-run", action="store_true")
    group_parser.add_argument("--budget", choices=sorted(BUDGET_PROFILES), default="quick")
    group_parser.add_argument("--max-attempts", type=int)
    group_parser.add_argument("--max-turns", type=int)
    group_parser.add_argument("--shell-timeout-seconds", type=int)
    group_parser.add_argument("--max-tool-calls", type=int)

    task_parser = sub.add_parser("run-task")
    task_parser.add_argument("task_ref")
    task_parser.add_argument("--suite", choices=["active", "backlog", "all", "v0.2"], default="active")
    task_parser.add_argument("--harness", default="default", choices=["default"], help="canonical MCP-backed harness")
    task_parser.add_argument("--keep-workspace", action="store_true")
    task_parser.add_argument("--dry-run", action="store_true")
    task_parser.add_argument("--budget", choices=sorted(BUDGET_PROFILES), default="quick")
    task_parser.add_argument("--max-attempts", type=int)
    task_parser.add_argument("--max-turns", type=int)
    task_parser.add_argument("--shell-timeout-seconds", type=int)
    task_parser.add_argument("--max-tool-calls", type=int)

    warm_parser = sub.add_parser(
        "warm-task",
        help="warm public Lean dependencies outside the per-task model budget",
    )
    warm_parser.add_argument("task_ref")
    warm_parser.add_argument("--suite", choices=["active", "backlog", "all", "v0.2"], default="active")
    warm_parser.add_argument(
        "--timeout-seconds", type=int, default=dependency_warm_timeout_seconds()
    )

    suite_parser = sub.add_parser("run-suite")
    suite_parser.add_argument("--suite", choices=["active", "backlog", "all", "v0.2"], default="active")
    suite_parser.add_argument("--harness", default="default", choices=["default"], help="canonical MCP-backed harness")
    suite_parser.add_argument("--keep-workspace", action="store_true")
    suite_parser.add_argument("--dry-run", action="store_true")
    suite_parser.add_argument("--budget", choices=sorted(BUDGET_PROFILES), default="quick")
    suite_parser.add_argument("--max-attempts", type=int)
    suite_parser.add_argument("--max-turns", type=int)
    suite_parser.add_argument("--shell-timeout-seconds", type=int)
    suite_parser.add_argument("--max-tool-calls", type=int)

    compare_parser = sub.add_parser("compare")
    compare_parser.add_argument("--runs", nargs="+", required=True)

    args = parser.parse_args()
    if (
        args.command != "list"
        and getattr(args, "suite", None) == "v0.2"
        and os.environ.get("VERITY_V02_PINNED_CHECKOUT") != "1"
    ):
        return subprocess.run(
            [sys.executable, "scripts/run_in_v02_environment.py", "--", sys.executable, "-m", "harness.cli", *sys.argv[1:]],
            cwd=Path(__file__).resolve().parent.parent,
            check=False,
        ).returncode
    if args.command == "list":
        groups = list_groups(args.suite)
        if args.json:
            print(json.dumps([group_to_json(group) for group in groups], indent=2))
        elif args.unit == "group":
            for group in groups:
                print(group.group_id)
        else:
            for group in groups:
                for task in group.tasks:
                    print(task.task_ref)
        return 0
    if args.command == "run-group":
        _apply_budget(args)
        code, run_dir = run_group(
            args.group_id,
            args.harness,
            args.suite,
            args.keep_workspace,
            args.dry_run,
            args.max_attempts,
            args.max_turns,
            args.shell_timeout_seconds,
            args.max_tool_calls,
        )
        print(run_dir)
        return code
    if args.command == "run-task":
        _apply_budget(args)
        group_id = group_id_from_task_ref(args.task_ref)
        code, run_dir = run_group(
            group_id,
            args.harness,
            args.suite,
            args.keep_workspace,
            args.dry_run,
            args.max_attempts,
            args.max_turns,
            args.shell_timeout_seconds,
            args.max_tool_calls,
            task_ref=args.task_ref,
        )
        print(run_dir)
        return code
    if args.command == "warm-task":
        if args.suite == "v0.2":
            from scripts.validate_v02_reference_contract import ensure_structural_contract
            ensure_structural_contract()
        code, artifact_dir = warm_task_dependencies(
            args.task_ref,
            suite=args.suite,
            timeout_seconds=args.timeout_seconds,
        )
        print(artifact_dir)
        return code
    if args.command == "run-suite":
        _apply_budget(args)
        exit_code, run_dir = run_suite(
            suite=args.suite,
            harness=args.harness,
            keep_workspace=args.keep_workspace,
            dry_run=args.dry_run,
            max_attempts=args.max_attempts,
            max_turns=args.max_turns,
            shell_timeout_seconds=args.shell_timeout_seconds,
            max_tool_calls=args.max_tool_calls,
        )
        print(run_dir)
        return exit_code
    print(json.dumps(compare_runs([Path(item) for item in args.runs]), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
