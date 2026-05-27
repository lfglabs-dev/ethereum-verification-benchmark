#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.manifests import list_groups, load_group
from harness.workspace_builder import assert_workspace_isolated, build_group_workspace, sha256_file


def check_group(group_id: str) -> list[str]:
    errors: list[str] = []
    workspace = Path(tempfile.mkdtemp(prefix=f"verity-workspace-check-{group_id.replace('/', '__')}-"))
    try:
        built = build_group_workspace(load_group(group_id), workspace_dir=workspace, run_id="workspace-check")
        try:
            assert_workspace_isolated(built.path)
        except AssertionError as exc:
            errors.append(str(exc))
        manifest = json.loads(built.manifest_path.read_text(encoding="utf-8"))
        manifest_hashes = {item["path"]: item["sha256"] for item in manifest["files"]}
        if not (built.path / "Benchmark" / "Grindset.lean").is_file():
            errors.append(f"{group_id}: missing Benchmark/Grindset.lean umbrella import")
        dependency_cache = manifest.get("dependency_cache")
        if dependency_cache is not None:
            if dependency_cache.get("path") != ".lake":
                errors.append(f"{group_id}: unexpected dependency cache path {dependency_cache.get('path')!r}")
            cache_link = built.path / ".lake"
            if not cache_link.is_symlink():
                errors.append(f"{group_id}: dependency cache .lake is not a symlink")
            else:
                resolved_cache = cache_link.resolve()
                if resolved_cache == ROOT:
                    errors.append(f"{group_id}: dependency cache resolves to repo root")
                if not str(resolved_cache).endswith("/.lake"):
                    errors.append(f"{group_id}: dependency cache target is not a .lake directory: {resolved_cache}")
        for task in manifest["group"]["tasks"]:
            for key in ("implementation_files", "specification_files", "editable_files"):
                for rel in task[key]:
                    if not (built.path / rel).is_file():
                        errors.append(f"{group_id}: missing declared {key} file {rel}")
        for rel, expected in manifest_hashes.items():
            path = built.path / rel
            if not path.is_file():
                errors.append(f"{group_id}: manifest file missing {rel}")
            elif sha256_file(path) != expected:
                errors.append(f"{group_id}: hash mismatch for {rel}")
    finally:
        shutil.rmtree(workspace, ignore_errors=True)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Check generated group workspace isolation and manifests")
    parser.add_argument("groups", nargs="*")
    parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    args = parser.parse_args()
    group_ids = args.groups or [group.group_id for group in list_groups(args.suite)]
    errors: list[str] = []
    for group_id in group_ids:
        errors.extend(check_group(group_id))
    if errors:
        for error in errors:
            print(error)
        return 1
    print(f"workspace checks passed for {len(group_ids)} group(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
