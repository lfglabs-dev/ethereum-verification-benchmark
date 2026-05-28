from __future__ import annotations

import argparse
import json
import os
import time
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

DEFAULT_MAX_TOOL_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_TOOL_CALLS", "24"))

try:
    from .manifests import group_id_from_task_ref, group_to_json, list_groups
    from .paths import RESULTS_DIR
    from .reports import compare_runs, write_run_report
    from .runners.grok_build import run_group as run_grok_group
    from .runners.lean_tools import run_group as run_lean_tools_group
except ImportError:
    from manifests import group_id_from_task_ref, group_to_json, list_groups
    from paths import RESULTS_DIR
    from reports import compare_runs, write_run_report
    from runners.grok_build import run_group as run_grok_group
    from runners.lean_tools import run_group as run_lean_tools_group


def run_group(
    group_id: str,
    harness: str,
    suite: str,
    keep_workspace: bool,
    dry_run: bool,
    max_attempts: int,
    max_turns: int,
    mode: str,
    max_tool_calls: int,
    task_ref: str | None = None,
) -> tuple[int, Path]:
    if harness == "grok-build":
        return run_grok_group(
            group_id,
            suite=suite,
            keep_workspace=keep_workspace,
            dry_run=dry_run,
            max_turns=max_turns,
            task_ref=task_ref,
        )
    if harness == "default":
        return run_lean_tools_group(
            group_id,
            suite=suite,
            keep_workspace=keep_workspace,
            dry_run=dry_run,
            max_attempts=max_attempts,
            max_tool_calls=max_tool_calls,
            mode=mode,
            task_ref=task_ref,
        )
    raise SystemExit(f"unknown harness: {harness} (expected: default, grok-build)")


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
    mode: str,
    max_tool_calls: int,
) -> tuple[int, Path]:
    start = time.time()
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    mode_slug = f"-{mode}" if harness == "default" else ""
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
        code, child_dir = run_group(group.group_id, harness, suite, keep_workspace, dry_run, max_attempts, max_turns, mode, max_tool_calls)
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
    harness_status = "completed" if exit_code == 0 else "completed_with_failures"
    child_tracks = sorted({str(item.get("track")) for item in child_runs if item.get("track")})
    child_models = sorted({str(item.get("model")) for item in child_runs if item.get("model")})
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": harness,
        "model": child_models[0] if len(child_models) == 1 else "suite-aggregate",
        "track": child_tracks[0] if len(child_tracks) == 1 else "mixed",
        "mode": mode if harness == "default" else None,
        "run_mode": "suite",
        "group_id": None,
        "task_ref": None,
        "suite": suite,
        "started_at": started_at,
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": harness_status,
        "harness_exit_code": exit_code,
        "child_runs": child_runs,
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
                "mode": mode if harness == "default" else None,
                "max_tool_calls": max_tool_calls if harness == "default" else None,
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


def main() -> int:
    parser = argparse.ArgumentParser(description="Verity benchmark group CLI")
    sub = parser.add_subparsers(dest="command", required=True)

    list_parser = sub.add_parser("list")
    list_parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    list_parser.add_argument("--unit", choices=["group", "task"], default="group")
    list_parser.add_argument("--json", action="store_true")

    group_parser = sub.add_parser("run-group")
    group_parser.add_argument("group_id")
    group_parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    group_parser.add_argument("--harness", choices=["default", "grok-build"], default="default")
    group_parser.add_argument("--keep-workspace", action="store_true")
    group_parser.add_argument("--dry-run", action="store_true")
    group_parser.add_argument("--max-attempts", type=int, default=1)
    group_parser.add_argument("--max-turns", type=int, default=20)
    group_parser.add_argument("--mode", choices=["fair", "tuned", "legacy"], default="fair")
    group_parser.add_argument("--max-tool-calls", type=int, default=DEFAULT_MAX_TOOL_CALLS)

    task_parser = sub.add_parser("run-task")
    task_parser.add_argument("task_ref")
    task_parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    task_parser.add_argument("--harness", choices=["default", "grok-build"], default="default")
    task_parser.add_argument("--keep-workspace", action="store_true")
    task_parser.add_argument("--dry-run", action="store_true")
    task_parser.add_argument("--max-attempts", type=int, default=1)
    task_parser.add_argument("--max-turns", type=int, default=20)
    task_parser.add_argument("--mode", choices=["fair", "tuned", "legacy"], default="fair")
    task_parser.add_argument("--max-tool-calls", type=int, default=DEFAULT_MAX_TOOL_CALLS)

    suite_parser = sub.add_parser("run-suite")
    suite_parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    suite_parser.add_argument("--harness", choices=["default", "grok-build"], default="default")
    suite_parser.add_argument("--keep-workspace", action="store_true")
    suite_parser.add_argument("--dry-run", action="store_true")
    suite_parser.add_argument("--max-attempts", type=int, default=1)
    suite_parser.add_argument("--max-turns", type=int, default=20)
    suite_parser.add_argument("--mode", choices=["fair", "tuned", "legacy"], default="fair")
    suite_parser.add_argument("--max-tool-calls", type=int, default=DEFAULT_MAX_TOOL_CALLS)

    compare_parser = sub.add_parser("compare")
    compare_parser.add_argument("--runs", nargs="+", required=True)

    args = parser.parse_args()
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
        code, run_dir = run_group(
            args.group_id,
            args.harness,
            args.suite,
            args.keep_workspace,
            args.dry_run,
            args.max_attempts,
            args.max_turns,
            args.mode,
            args.max_tool_calls,
        )
        print(run_dir)
        return code
    if args.command == "run-task":
        group_id = group_id_from_task_ref(args.task_ref)
        code, run_dir = run_group(
            group_id,
            args.harness,
            args.suite,
            args.keep_workspace,
            args.dry_run,
            args.max_attempts,
            args.max_turns,
            args.mode,
            args.max_tool_calls,
            task_ref=args.task_ref,
        )
        print(run_dir)
        return code
    if args.command == "run-suite":
        exit_code, run_dir = run_suite(
            suite=args.suite,
            harness=args.harness,
            keep_workspace=args.keep_workspace,
            dry_run=args.dry_run,
            max_attempts=args.max_attempts,
            max_turns=args.max_turns,
            mode=args.mode,
            max_tool_calls=args.max_tool_calls,
        )
        print(run_dir)
        return exit_code
    print(json.dumps(compare_runs([Path(item) for item in args.runs]), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
