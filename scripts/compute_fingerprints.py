#!/usr/bin/env python3
"""Compute benchmark version fingerprints and manifests."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from datetime import date
from pathlib import Path

from typing import Any

import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "harness"))
sys.path.insert(0, str(ROOT / "scripts"))

from release_config import BENCHMARK_ID  # noqa: E402
from manifests import list_groups  # noqa: E402
from manifest_utils import load_manifest_data  # noqa: E402

HASH_PREFIX = "sha256:"
TASK_METADATA_FIELDS = (
    "proof_family",
    "property_class",
    "difficulty",
    "category",
    "track",
    "task_interface_version",
    "translation_status",
    "proof_status",
)
EXECUTION_METADATA_FIELDS = (
    "task_id",
    "case_id",
    "theorem_name",
    "implementation_files",
    "specification_files",
    "editable_files",
    "reference_solution_declaration",
    "task_interface_version",
    "translation_status",
    "proof_status",
    "evaluation_engine",
)
INTERFACE_FIELDS = (
    "task_id",
    "case_id",
    "theorem_name",
    "implementation_files",
    "specification_files",
    "editable_files",
    "reference_solution_declaration",
    "task_interface_version",
    "track",
)


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def digest_bytes(value: bytes) -> str:
    return HASH_PREFIX + hashlib.sha256(value).hexdigest()


def digest_json(value: Any) -> str:
    return digest_bytes(canonical_json(value))


def read_file_entry(path: Path) -> dict[str, object]:
    rel = path.relative_to(ROOT).as_posix()
    if not path.is_file():
        return {"path": rel, "missing": True}
    return {"path": rel, "sha256": digest_bytes(path.read_bytes()), "bytes": path.stat().st_size}


def existing_paths(paths: list[str]) -> list[Path]:
    result: list[Path] = []
    for raw in paths:
        path = ROOT / raw
        if path.exists():
            result.append(path)
    return result


def load_case_manifest(task_manifest: Path) -> dict[str, object]:
    return load_manifest_data(task_manifest.parent.parent / "case.yaml")


def load_task_manifest(task_manifest: Path) -> dict[str, object]:
    return load_manifest_data(task_manifest)


def task_ref_parts(task_ref: str) -> tuple[str, str, str]:
    family_id, case_name, task_id = task_ref.split("/", 2)
    return family_id, f"{family_id}/{case_name}", task_id


def _list_field(value: object) -> list[str]:
    return [str(item) for item in value] if isinstance(value, list) else []


def task_entry(task) -> dict[str, object]:
    manifest_path = ROOT / task.manifest_path
    raw_task = load_task_manifest(manifest_path)
    raw_case = load_case_manifest(manifest_path)
    family_id, case_id, task_id = task_ref_parts(task.task_ref)
    implementation_id = str(raw_task.get("implementation_id") or raw_case.get("implementation_id") or "")
    family_manifest = ROOT / "families" / family_id / "family.yaml"
    implementation_manifest = ROOT / "families" / family_id / "implementations" / implementation_id / "implementation.yaml"

    implementation_files = _list_field(raw_task.get("implementation_files"))
    specification_files = _list_field(raw_task.get("specification_files"))
    editable_files = _list_field(raw_task.get("editable_files"))
    execution_metadata = {field: raw_task.get(field) for field in EXECUTION_METADATA_FIELDS if field in raw_task}
    interface_metadata = {field: raw_task.get(field) for field in INTERFACE_FIELDS if field in raw_task}

    fingerprint_files = [
        manifest_path,
        manifest_path.parent.parent / "case.yaml",
        family_manifest,
        implementation_manifest,
        *existing_paths(implementation_files),
        *existing_paths(specification_files),
        *existing_paths(editable_files),
    ]
    fingerprint_payload = {
        "task_ref": task.task_ref,
        "metadata": execution_metadata,
        "files": [read_file_entry(path) for path in sorted(set(fingerprint_files), key=lambda item: item.as_posix())],
    }
    interface_payload = {
        "task_ref": task.task_ref,
        "metadata": interface_metadata,
        "public_files": [read_file_entry(path) for path in existing_paths(implementation_files + specification_files)],
        "editable_files": [read_file_entry(path) for path in existing_paths(editable_files)],
    }

    entry = {
        "task_ref": task.task_ref,
        "family_id": family_id,
        "case_id": case_id,
        "task_id": task_id,
        "manifest_path": task.manifest_path,
        "task_fingerprint": digest_json(fingerprint_payload),
        "task_interface_id": digest_json(interface_payload),
        "theorem_name": raw_task.get("theorem_name"),
        "implementation_files": implementation_files,
        "specification_files": specification_files,
        "editable_files": editable_files,
    }
    for field in TASK_METADATA_FIELDS:
        if field in raw_task:
            entry[field] = raw_task[field]
    return entry


def ordered_tasks(suite: str = "active") -> list[dict[str, object]]:
    tasks = []
    for group in list_groups(suite=suite, runnable_only=True):
        tasks.extend(group.tasks)
    return [task_entry(task) for task in sorted(tasks, key=lambda item: item.task_ref)]


def task_entries(suite: str = "all") -> dict[str, dict[str, object]]:
    """Return canonical task entries keyed by ref from the production derivation."""
    entries = ordered_tasks(suite)
    result = {str(entry["task_ref"]): entry for entry in entries}
    if len(result) != len(entries):
        raise ValueError("cannot recompute task entries with duplicate refs")
    return result


def task_metadata(suite: str = "all") -> dict[str, tuple[str, str]]:
    """Return production fingerprints keyed by task reference.

    Keep consumers of frozen contracts on the same ``task_entry`` derivation as
    version-manifest generation; this is deliberately not a parallel hash
    implementation.
    """
    metadata: dict[str, tuple[str, str]] = {}
    for task in task_entries(suite).values():
        ref = task.get("task_ref")
        fingerprint = task.get("task_fingerprint")
        interface_id = task.get("task_interface_id")
        if not isinstance(ref, str) or not isinstance(fingerprint, str) or not isinstance(interface_id, str):
            raise ValueError("cannot recompute task metadata")
        metadata[ref] = (fingerprint, interface_id)
    return metadata


def baseline_contract_entries(
    commit: str,
) -> tuple[dict[str, dict[str, object]], dict[str, dict[str, str]]]:
    """Recompute canonical task and reference entries in ``commit`` only."""
    program = """
import hashlib, json, sys
from pathlib import Path
from scripts.compute_fingerprints import ordered_tasks
from harness.task_runner import load_task_record, resolve_task_manifest
sys.path.insert(0, __CLOSURE_SCRIPT_PATH__)
from v02_reference_closure import collect_reference_closure
tasks = ordered_tasks('all')
references = {}
for task in tasks:
    task_path = resolve_task_manifest(task['task_ref'])
    reference = load_task_record(task_path)['reference_solution']
    module = reference['module']
    module_path = Path.cwd().joinpath(*module.split('.')).with_suffix('.lean')
    references[task['task_ref']] = {
        'reference_module': module,
        'reference_declaration': reference['declaration'],
        'reference_module_path': str(module_path.relative_to(Path.cwd())),
        'reference_module_sha256': hashlib.sha256(module_path.read_bytes()).hexdigest(),
        'reference_import_closure': collect_reference_closure(Path.cwd(), module),
    }
print(json.dumps({'tasks': tasks, 'references': references}, sort_keys=True))
"""
    with tempfile.TemporaryDirectory(prefix="benchmark-baseline-metadata-") as directory:
        worktree = Path(directory) / "source"
        added = subprocess.run(
            ["git", "worktree", "add", "--detach", str(worktree), commit],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        if added.returncode:
            raise ValueError(f"pinned source unavailable (infra): {commit}")
        try:
            program = program.replace("__CLOSURE_SCRIPT_PATH__", repr(str(ROOT / "scripts")))
            result = subprocess.run(
                [sys.executable, "-c", program], cwd=worktree, text=True, capture_output=True, check=False
            )
            if result.returncode:
                raise ValueError(f"pinned source canonical recomputation unavailable (infra): {commit}")
            data = json.loads(result.stdout)
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", str(worktree)], cwd=ROOT, check=False)
    tasks = data.get("tasks") if isinstance(data, dict) else None
    references = data.get("references") if isinstance(data, dict) else None
    if not isinstance(tasks, list) or not isinstance(references, dict):
        raise ValueError("pinned source canonical entries malformed")
    entries = {entry.get("task_ref"): entry for entry in tasks if isinstance(entry, dict)}
    if len(entries) != len(tasks) or not all(isinstance(ref, str) for ref in entries):
        raise ValueError("pinned source canonical task entries malformed")
    if set(references) != set(entries) or not all(
        isinstance(ref, str) and isinstance(entry, dict) for ref, entry in references.items()
    ):
        raise ValueError("pinned source reference entries malformed")
    return entries, references


def baseline_version_metadata(
    commit: str,
    *,
    version: str,
    created_at: str,
    suite: str = "all",
    mode: str = "fair",
    budget: str = "normal",
) -> dict[str, object]:
    """Derive version-level metadata in the immutable pinned source tree.

    This deliberately calls the same ``build_version_manifest`` implementation
    used for ordinary releases, rather than reimplementing its identity hashes.
    """
    program = f"""
import json
from scripts.compute_fingerprints import build_version_manifest
manifest = build_version_manifest(
    {version!r}, created_at={created_at!r}, suite={suite!r}, mode={mode!r}, budget={budget!r}
)
print(json.dumps({{key: value for key, value in manifest.items() if key != 'tasks'}}, sort_keys=True))
"""
    with tempfile.TemporaryDirectory(prefix="benchmark-baseline-version-") as directory:
        worktree = Path(directory) / "source"
        added = subprocess.run(
            ["git", "worktree", "add", "--detach", str(worktree), commit],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        if added.returncode:
            raise ValueError(f"pinned source unavailable (infra): {commit}")
        try:
            result = subprocess.run(
                [sys.executable, "-c", program], cwd=worktree, text=True, capture_output=True, check=False
            )
            if result.returncode:
                raise ValueError(f"pinned source version metadata recomputation unavailable (infra): {commit}")
            metadata = json.loads(result.stdout)
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", str(worktree)], cwd=ROOT, check=False)
    if not isinstance(metadata, dict) or not all(isinstance(key, str) for key in metadata):
        raise ValueError("pinned source version metadata malformed")
    return metadata


def baseline_task_entries(commit: str) -> dict[str, dict[str, object]]:
    """Return full canonical entries from the pinned source revision."""
    return baseline_contract_entries(commit)[0]


def baseline_reference_entries(commit: str) -> dict[str, dict[str, str]]:
    """Return reference declarations and module hashes from the pinned revision."""
    return baseline_contract_entries(commit)[1]


def baseline_task_metadata(commit: str) -> dict[str, tuple[str, str]]:
    """Compatibility view of the pinned canonical task entries."""
    return {
        ref: (str(entry["task_fingerprint"]), str(entry["task_interface_id"]))
        for ref, entry in baseline_task_entries(commit).items()
    }


def task_set_id(tasks: list[dict[str, object]]) -> str:
    return digest_json([task["task_ref"] for task in tasks])


def hash_tree(paths: list[Path]) -> str:
    files: list[dict[str, object]] = []
    for root in paths:
        if root.is_file():
            files.append(read_file_entry(root))
        elif root.is_dir():
            for path in sorted(p for p in root.rglob("*") if p.is_file()):
                if "__pycache__" in path.parts:
                    continue
                files.append(read_file_entry(path))
    return digest_json(files)


def harness_id() -> str:
    roots = [
        ROOT / "harness",
        ROOT / "scripts" / "run_default_harness_group.sh",
        ROOT / "scripts" / "run_default_harness_suite.sh",
        ROOT / "scripts" / "run_local_default_benchmark.py",
        ROOT / "scripts" / "run_task.sh",
        ROOT / "scripts" / "run_case.sh",
    ]
    return hash_tree(roots)


def environment_id() -> str:
    roots = [
        ROOT / "lean-toolchain",
        ROOT / "lakefile.lean",
        ROOT / "lake-manifest.json",
        ROOT / "benchmark.toml",
        ROOT / ".github" / "actions" / "setup-lean",
    ]
    return hash_tree(roots)


def git_sha() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unknown"


def build_version_manifest(
    version: str,
    *,
    created_at: str | None = None,
    mode: str = "fair",
    budget: str = "normal",
    suite: str = "active",
) -> dict[str, object]:
    tasks = ordered_tasks(suite)
    return {
        "benchmark": BENCHMARK_ID,
        "benchmark_version": version,
        "created_at": created_at or date.today().isoformat(),
        "git_sha": git_sha(),
        "manifest_schema_version": 1,
        "task_count": len(tasks),
        "task_set_id": task_set_id(tasks),
        "harness_id": harness_id(),
        "environment_id": environment_id(),
        "mode": mode,
        "budget": budget,
        "tasks": tasks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", required=True, help="Benchmark version, for example 0.1")
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--created-at", default=None)
    parser.add_argument("--mode", default="fair")
    parser.add_argument("--budget", default="normal")
    parser.add_argument("--suite", default="active")
    args = parser.parse_args()

    manifest = build_version_manifest(
        args.version,
        created_at=args.created_at,
        mode=args.mode,
        budget=args.budget,
        suite=args.suite,
    )
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
