#!/usr/bin/env python3
"""Generate the v0.2 contract from the baseline production all-suite selector."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "harness"))

BASELINE = "c5a2344b121040445ccd745a3f839548ca8f9158"
MANIFEST = ROOT / "benchmark-versions" / "v0.2.json"
REFERENCES = ROOT / "benchmark-versions" / "v0.2-references.json"


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest_file(path: Path) -> str:
    return digest_bytes(path.read_bytes())


@contextmanager
def baseline_worktree() -> Path:
    """Expose the pinned source tree without ever consulting the caller's checkout."""
    with tempfile.TemporaryDirectory(prefix="v02-contract-baseline-") as directory:
        path = Path(directory) / "source"
        subprocess.run(
            ["git", "worktree", "add", "--detach", str(path), BASELINE],
            cwd=ROOT,
            check=True,
        )
        try:
            yield path
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", str(path)], cwd=ROOT, check=False)


def read_baseline_contract_inputs(worktree: Path) -> dict[str, object]:
    """Load selector, version-manifest metadata and references from the pinned tree."""
    program = """
import hashlib, json
from pathlib import Path
from scripts.compute_fingerprints import build_version_manifest
from harness.task_runner import discover_task_refs, load_task_record, resolve_task_manifest
root = Path.cwd()
refs = discover_task_refs('all')
version_manifest = build_version_manifest('0.2', created_at='2026-07-18', suite='all')
if [task['task_ref'] for task in version_manifest['tasks']] != refs:
    raise SystemExit('version-manifest all-suite task order differs from production selector')
entries = []
for ref in refs:
    task_path = resolve_task_manifest(ref)
    task = load_task_record(task_path)
    reference = task['reference_solution']
    module = reference['module']
    declaration = reference['declaration']
    if not isinstance(module, str) or not isinstance(declaration, str):
        raise SystemExit(f'{ref}: source task has no reference module/declaration')
    module_path = root.joinpath(*module.split('.')).with_suffix('.lean')
    if not module_path.is_file():
        raise SystemExit(f'{ref}: reference module does not exist: {module}')
    entries.append({
        'task_ref': ref,
        'task_fingerprint': next(task['task_fingerprint'] for task in version_manifest['tasks'] if task['task_ref'] == ref),
        'task_interface_id': next(task['task_interface_id'] for task in version_manifest['tasks'] if task['task_ref'] == ref),
        'task_manifest_path': str(task_path.relative_to(root)),
        'task_manifest_sha256': hashlib.sha256(task_path.read_bytes()).hexdigest(),
        'reference_module': module,
        'reference_declaration': declaration,
        'reference_module_path': str(module_path.relative_to(root)),
        'reference_module_sha256': hashlib.sha256(module_path.read_bytes()).hexdigest(),
    })
print(json.dumps({'refs': refs, 'tasks': version_manifest['tasks'], 'version_metadata': {
    key: value for key, value in version_manifest.items() if key != 'tasks'
}, 'entries': entries}))
"""
    completed = subprocess.run(
        [sys.executable, "-c", program], cwd=worktree, text=True, capture_output=True, check=True
    )
    return json.loads(completed.stdout)


def dump(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    # The release contract is deliberately derived from the real production all
    # selector in the pinned source revision, never from a potentially changed
    # generator checkout.
    with baseline_worktree() as worktree:
        baseline = read_baseline_contract_inputs(worktree)
        refs = baseline["refs"]
        tasks = baseline["tasks"]
        version_metadata = baseline["version_metadata"]
        reference_entries = baseline["entries"]
        selector_files_sha256 = {
            path: digest_file(worktree / path)
            for path in ("harness/task_runner.py", "scripts/run_all.sh")
        }
    if not isinstance(refs, list) or not all(isinstance(ref, str) for ref in refs):
        raise SystemExit("baseline all-suite selector returned malformed task refs")
    if not isinstance(tasks, list) or not all(isinstance(task, dict) for task in tasks):
        raise SystemExit("baseline version manifest returned malformed task objects")
    if [task.get("task_ref") for task in tasks] != refs:
        raise SystemExit("baseline version manifest task objects differ from all-suite selector")
    if not isinstance(version_metadata, dict):
        raise SystemExit("baseline version manifest returned malformed metadata")
    if not isinstance(reference_entries, list) or not all(isinstance(entry, dict) for entry in reference_entries):
        raise SystemExit("baseline all-suite selector returned malformed reference entries")
    if len(refs) != len(set(refs)):
        raise SystemExit("baseline all-suite selector returned duplicate task refs")
    source = {
        "commit": BASELINE,
        "entrypoint": "scripts/run_all.sh",
        "selector_command": "python3 harness/task_runner.py list --suite all",
        "selector_files_sha256": selector_files_sha256,
    }
    task_hashes = {entry["task_ref"]: entry["task_manifest_sha256"] for entry in reference_entries}
    task_set_hash = digest_bytes(("\n".join(refs) + "\n").encode())
    manifest = {
        **version_metadata,
        "benchmark": "ethereum-verification-benchmark",
        "benchmark_version": "0.2",
        "contract_kind": "canonical_full_suite_selection",
        "schema_version": 2,
        "source": source,
        "task_count": len(tasks),
        "task_set_sha256": task_set_hash,
        "tasks": tasks,
        "task_manifest_sha256": task_hashes,
    }
    dump(MANIFEST, manifest)
    references = {
        "benchmark": "ethereum-verification-benchmark",
        "benchmark_version": "0.2",
        "contract_kind": "canonical_reference_declarations",
        "schema_version": 1,
        "source_commit": BASELINE,
        "canonical_manifest_path": str(MANIFEST.relative_to(ROOT)),
        "canonical_manifest_sha256": digest_file(MANIFEST),
        "task_count": len(refs),
        "task_set_sha256": task_set_hash,
        "tasks": reference_entries,
    }
    dump(REFERENCES, references)
    print(MANIFEST.relative_to(ROOT))
    print(REFERENCES.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
