#!/usr/bin/env python3
"""Generate a deterministic case-stratified benchmark panel from a version manifest."""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path
from typing import Any


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def stable_rank(seed: int, task_ref: str) -> str:
    return sha256_bytes(f"stratified-panel-v1\0{seed}\0{task_ref}".encode())


def allocate_case_slots(case_sizes: dict[str, int], panel_size: int, seed: int) -> dict[str, int]:
    """Give every case one slot, then allocate extras by largest remainder."""
    if panel_size < len(case_sizes):
        raise ValueError(
            f"panel size {panel_size} cannot cover all {len(case_sizes)} cases"
        )
    total_tasks = sum(case_sizes.values())
    if panel_size > total_tasks:
        raise ValueError(f"panel size {panel_size} exceeds task count {total_tasks}")

    allocation = {case_id: 1 for case_id in case_sizes}
    extras = panel_size - len(case_sizes)
    remaining = {case_id: size - 1 for case_id, size in case_sizes.items()}
    remaining_total = sum(remaining.values())
    if extras == 0:
        return allocation
    if remaining_total < extras:
        raise ValueError("not enough remaining tasks for requested panel")

    exact = {
        case_id: extras * available / remaining_total
        for case_id, available in remaining.items()
    }
    for case_id, quota in exact.items():
        allocation[case_id] += min(remaining[case_id], int(quota))

    unallocated = panel_size - sum(allocation.values())
    candidates = sorted(
        case_sizes,
        key=lambda case_id: (
            -(exact[case_id] - int(exact[case_id])),
            stable_rank(seed, f"case-allocation\0{case_id}"),
            case_id,
        ),
    )
    while unallocated:
        progressed = False
        for case_id in candidates:
            if allocation[case_id] >= case_sizes[case_id]:
                continue
            allocation[case_id] += 1
            unallocated -= 1
            progressed = True
            if not unallocated:
                break
        if not progressed:
            raise ValueError("could not allocate every panel slot")
    return allocation


def generate_panel(
    manifest: dict[str, Any], panel_size: int = 50, seed: int = 42
) -> tuple[list[str], dict[str, Any]]:
    tasks = manifest.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        raise ValueError("manifest must contain a non-empty tasks array")
    refs = [task.get("task_ref") for task in tasks]
    if any(not isinstance(ref, str) or not ref for ref in refs):
        raise ValueError("every task must have a non-empty task_ref")
    if len(refs) != len(set(refs)):
        raise ValueError("manifest contains duplicate task_ref values")

    by_case: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for task in tasks:
        case_id = task.get("case_id")
        if not isinstance(case_id, str) or not case_id:
            raise ValueError(f"task {task['task_ref']} has no case_id")
        by_case[case_id].append(task)

    allocation = allocate_case_slots(
        {case_id: len(case_tasks) for case_id, case_tasks in by_case.items()},
        panel_size,
        seed,
    )
    selected: list[dict[str, Any]] = []
    for case_id in sorted(by_case):
        ranked = sorted(
            by_case[case_id],
            key=lambda task: (stable_rank(seed, task["task_ref"]), task["task_ref"]),
        )
        selected.extend(ranked[: allocation[case_id]])

    selected.sort(key=lambda task: task["task_ref"])
    panel = [task["task_ref"] for task in selected]
    if len(panel) != panel_size or len(set(panel)) != panel_size:
        raise AssertionError("generator produced an invalid panel")

    dimensions = {}
    for key in ("difficulty", "category", "proof_family", "property_class"):
        counts: dict[str, int] = defaultdict(int)
        for task in selected:
            counts[str(task.get(key))] += 1
        dimensions[key] = dict(sorted(counts.items()))

    metadata = {
        "schema_version": 1,
        "panel_id": f"STRAT-{panel_size}",
        "benchmark_version": manifest.get("benchmark_version"),
        "benchmark_git_sha": manifest.get("git_sha"),
        "manifest_task_count": len(tasks),
        "task_set_id": manifest.get("task_set_id"),
        "environment_id": manifest.get("environment_id"),
        "harness_id": manifest.get("harness_id"),
        "selection": {
            "algorithm": "case-stratified-largest-remainder-sha256-v1",
            "seed": seed,
            "panel_size": panel_size,
            "case_count": len(by_case),
            "case_coverage": len({task["case_id"] for task in selected}),
            "allocation": dict(sorted(allocation.items())),
            "rank_domain": "stratified-panel-v1",
        },
        "dimensions": dimensions,
        "tasks": panel,
    }
    return panel, metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--panel", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--size", type=int, default=50)
    parser.add_argument("--seed", type=int, default=42)
    return parser.parse_args()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=False) + "\n")


def main() -> int:
    args = parse_args()
    manifest_bytes = args.manifest.read_bytes()
    manifest = json.loads(manifest_bytes)
    panel, metadata = generate_panel(manifest, args.size, args.seed)
    write_json(args.panel, panel)
    panel_bytes = args.panel.read_bytes()
    metadata["manifest_sha256"] = f"sha256:{sha256_bytes(manifest_bytes)}"
    metadata["panel_sha256"] = f"sha256:{sha256_bytes(panel_bytes)}"
    write_json(args.metadata, metadata)
    print(
        json.dumps(
            {
                "panel": str(args.panel),
                "metadata": str(args.metadata),
                "tasks": len(panel),
                "cases": metadata["selection"]["case_coverage"],
                "panel_sha256": metadata["panel_sha256"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
