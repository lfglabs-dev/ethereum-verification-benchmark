#!/usr/bin/env python3
"""Grindset ablation harness.

Measures, per benchmark task, whether a fixed generic tactic battery closes
the task's proof obligation inside a fair workspace (the same workspace an
agent sees: generic Grindset modules only), and how long the Lean check
takes. This is the empirical loop for curating the shipped Grindset: a
lemma/attribute change is good if it raises the battery close-rate or cuts
check time without case-specific knowledge.

Usage:
  python3 scripts/grindset_ablation.py --tasks slice --jobs 4 --out /tmp/ablation.json
  python3 scripts/grindset_ablation.py --tasks ethereum/deposit_contract_minimal/deposit_count
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import shutil
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.manifests import filter_group_to_task, list_groups, load_group
from harness.workspace_builder import build_group_workspace
from harness.runners import lean_tools
from harness.symbols import harvest_task_symbols, spec_names

SLICE_TASKS = [
    "ethereum/deposit_contract_minimal/deposit_count",
    "kleros/sortition_trees/node_id_bijection",
    "damn_vulnerable_defi/side_entrance/deposit_sets_pool_balance",
    "nexus_mutual/ramm_price_band/sync_sets_book_value",
    "paladin_votes/stream_recovery_claim_usdc/claim_marks_user",
]


def battery(skeleton: str, symbols: list[str]) -> list[tuple[str, str]]:
    specs = spec_names(skeleton)
    unfolds = "".join(f"try unfold {name}\n" for name in specs + symbols)
    args = ", ".join(["grind_norm"] + symbols + ["*"])
    all_args = ", ".join(["grind_norm"] + specs + symbols)
    entries = [
        # Agent-validated generic template: normalize, unfold public names,
        # simp with everything, then branch discharge.
        ("norm_unfold_simp_split", (
            "try simp only [grind_norm] at *\n"
            + unfolds
            + f"simp [{args}]\n"
            + "all_goals try (split_ifs <;> simp_all [grind_norm])\n"
            + "all_goals try (repeat' (split <;> simp_all [grind_norm]))\n"
            + "all_goals try omega\n"
        )),
        # simp_all variant: unfolds spec defs inside hypotheses too.
        ("simp_all_everything", f"simp_all [{all_args}]\n"),
        # Reach-style chain goals (Safe family shape) have a dedicated shipped
        # tactic; harmless elsewhere (fails fast).
        ("reach_grind", unfolds + "verity_reach_grind\n"),
        ("grind", "grind\n"),
    ]
    seen: set[str] = set()
    unique = []
    for name, body in entries:
        if body not in seen:
            seen.add(body)
            unique.append((name, body))
    return unique


def run_task(task_ref: str, suite: str) -> dict[str, object]:
    group_id = "/".join(task_ref.split("/")[:2])
    group = filter_group_to_task(load_group(group_id, suite), task_ref)
    built = build_group_workspace(group, run_id=f"ablation-{task_ref.replace('/', '__')}")
    task = group.tasks[0]
    results: list[dict[str, object]] = []
    try:
        editable = str(task.editable_files[0])
        target_module = str(task.target_module)
        proof_path = built.path / editable
        skeleton = proof_path.read_text(encoding="utf-8")
        # Warm the workspace build graph so battery timings measure proof
        # elaboration, not dependency compilation (skeleton has sorry, so a
        # non-zero exit here is expected).
        lean_tools._run_lean_module(built.path, target_module, timeout_seconds=1800)
        symbols = harvest_task_symbols(built.path, task)
        for name, body in battery(skeleton, symbols):
            candidate = lean_tools._patch_proof_body(skeleton, body)
            started = time.time()
            code, output = lean_tools._run_lean_module_with_proof_content(
                proof_path=proof_path,
                workspace=built.path,
                target_module=target_module,
                content=candidate,
            )
            diagnostics = lean_tools._goal_diagnostics(output) if code != 0 else {}
            results.append(
                {
                    "task_ref": task_ref,
                    "tactic": name,
                    "passed": code == 0,
                    "seconds": round(time.time() - started, 2),
                    "failure_kind": diagnostics.get("failure_kind"),
                    "first_error": (diagnostics.get("first_error") or "")[:200],
                }
            )
            if code == 0:
                break
    finally:
        shutil.rmtree(built.path, ignore_errors=True)
    return {"task_ref": task_ref, "results": results}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tasks", nargs="+", default=["slice"])
    parser.add_argument("--suite", default="active")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    if args.tasks == ["slice"]:
        task_refs = SLICE_TASKS
    elif args.tasks == ["all"]:
        task_refs = sorted(
            f"{group.group_id}/{task.task_id}"
            for group in list_groups(args.suite)
            for task in group.tasks
        )
    else:
        task_refs = args.tasks

    rows: list[dict[str, object]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(run_task, ref, args.suite): ref for ref in task_refs}
        for future in concurrent.futures.as_completed(futures):
            ref = futures[future]
            try:
                outcome = future.result()
            except Exception as exc:  # noqa: BLE001 - report and continue
                outcome = {"task_ref": ref, "error": str(exc), "results": []}
            rows.append(outcome)
            closed = [r["tactic"] for r in outcome["results"] if r["passed"]]
            status = f"closed by {closed[0]}" if closed else "open"
            if outcome.get("error"):
                status = f"error: {outcome['error'][:120]}"
            print(f"{ref}: {status}", flush=True)

    rows.sort(key=lambda row: str(row["task_ref"]))
    closed_count = sum(1 for row in rows if any(r["passed"] for r in row["results"]))
    summary = {
        "tasks": len(rows),
        "closed": closed_count,
        "close_rate": round(closed_count / len(rows), 3) if rows else 0.0,
        "rows": rows,
    }
    print(f"\nclosed {closed_count}/{len(rows)} tasks")
    if args.out:
        Path(args.out).write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
