from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from . import lean_tools
    from ..transport import DEFAULT_BASE_URL, endpoint_smoke
except ImportError:
    import lean_tools
    from transport import DEFAULT_BASE_URL, endpoint_smoke


HARNESS_ID = "builtin-lean-lsp"
RUN_SLUG = "builtin-lean-lsp"
TRACK = "group/lean_tools_mcp"


def run_group(
    group_id: str,
    *,
    suite: str = "active",
    keep_workspace: bool = False,
    dry_run: bool = False,
    max_attempts: int = 1,
    max_tool_calls: int = lean_tools.DEFAULT_MAX_TOOL_CALLS,
    task_ref: str | None = None,
) -> tuple[int, Path]:
    """Run the builtin fair loop with lean-lsp-mcp as its Lean IDE backend."""
    return lean_tools.run_group(
        group_id,
        suite=suite,
        keep_workspace=keep_workspace,
        dry_run=dry_run,
        max_attempts=max_attempts,
        max_tool_calls=max_tool_calls,
        task_ref=task_ref,
        harness_id=HARNESS_ID,
        run_slug=RUN_SLUG,
        track=TRACK,
        tool_backend="lean-lsp-mcp",
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Builtin fair harness backed by lean-lsp-mcp"
    )
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("smoke")
    run = sub.add_parser("run-group")
    run.add_argument("group_id")
    run.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    run.add_argument("--keep-workspace", action="store_true")
    run.add_argument("--dry-run", action="store_true")
    run.add_argument("--max-attempts", type=int, default=1)
    run.add_argument("--max-tool-calls", type=int, default=lean_tools.DEFAULT_MAX_TOOL_CALLS)
    run.add_argument("--task-ref")
    args = parser.parse_args()
    if args.command == "smoke":
        print(json.dumps(endpoint_smoke(DEFAULT_BASE_URL, lean_tools.DEFAULT_DRIVER_MODEL), indent=2))
        return 0
    code, run_dir = run_group(
        args.group_id,
        suite=args.suite,
        keep_workspace=args.keep_workspace,
        dry_run=args.dry_run,
        max_attempts=args.max_attempts,
        max_tool_calls=args.max_tool_calls,
        task_ref=args.task_ref,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
