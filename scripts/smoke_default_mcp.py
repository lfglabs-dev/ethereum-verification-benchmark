#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.lean_lsp_mcp_client import (
    LeanLspMcpCompatibilityError,
    LeanLspMcpSession,
)
from harness.manifests import filter_group_to_task, group_id_from_task_ref, load_group
from harness.workspace_builder import build_group_workspace


DEFAULT_TASK = "ethereum/deposit_contract_minimal/deposit_count"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Initialize the pinned default MCP backend and execute one real MCP tool"
    )
    parser.add_argument("--task", default=DEFAULT_TASK)
    parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    parser.add_argument("--keep-workspace", action="store_true")
    args = parser.parse_args()

    group_id = group_id_from_task_ref(args.task)
    group = filter_group_to_task(load_group(group_id, args.suite), args.task)
    built = build_group_workspace(group, run_id="default-mcp-smoke")
    task = group.tasks[0]
    query = task.theorem_name.rsplit(".", 1)[-1]
    try:
        try:
            with LeanLspMcpSession(built.path) as session:
                result = session.call_tool(
                    "lean_local_search",
                    {"query": query, "limit": 10},
                )
                if not result.get("ok"):
                    raise RuntimeError(f"lean_local_search failed: {result}")
                print(
                    json.dumps(
                        {
                            "status": "passed",
                            "workspace": str(built.path),
                            "task_ref": args.task,
                            "mcp": session.metadata(),
                            "tool_call": {
                                "name": "lean_local_search",
                                "arguments": {"query": query, "limit": 10},
                                "result": result,
                            },
                        },
                        indent=2,
                    )
                )
        except LeanLspMcpCompatibilityError as exc:
            print(
                json.dumps(
                    {
                        "status": "blocked_incompatible_lean_toolchain",
                        "task_ref": args.task,
                        "error": str(exc),
                        "required_action": (
                            "Re-run this smoke on the audited benchmark/Verity Lean 4.24 migration."
                        ),
                    },
                    indent=2,
                )
            )
            return 2
    finally:
        if not args.keep_workspace:
            shutil.rmtree(built.path, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
