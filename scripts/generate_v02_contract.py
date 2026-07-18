#!/usr/bin/env python3
"""Generate the v0.2 contract from the baseline production all-suite selector."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "harness"))

from harness.task_runner import discover_task_refs, load_task_record, resolve_task_manifest

BASELINE = "c5a2344b121040445ccd745a3f839548ca8f9158"
MANIFEST = ROOT / "benchmark-versions" / "v0.2.json"
REFERENCES = ROOT / "benchmark-versions" / "v0.2-references.json"


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest_file(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def git_file_sha(revision: str, path: str) -> str:
    raw = subprocess.check_output(["git", "show", f"{revision}:{path}"], cwd=ROOT)
    return digest_bytes(raw)


def dump(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    # This is deliberately the real production selector, not a fixture.
    refs = discover_task_refs("all")
    if len(refs) != len(set(refs)):
        raise SystemExit("baseline all-suite selector returned duplicate task refs")
    source = {
        "commit": BASELINE,
        "entrypoint": "scripts/run_all.sh",
        "selector_command": "python3 harness/task_runner.py list --suite all",
        "selector_files_sha256": {
            "harness/task_runner.py": git_file_sha(BASELINE, "harness/task_runner.py"),
            "scripts/run_all.sh": git_file_sha(BASELINE, "scripts/run_all.sh"),
        },
    }
    task_hashes: dict[str, str] = {}
    reference_entries: list[dict[str, str]] = []
    for ref in refs:
        task_path = resolve_task_manifest(ref)
        task = load_task_record(task_path)
        reference = task["reference_solution"]
        module = reference["module"]
        declaration = reference["declaration"]
        if not isinstance(module, str) or not isinstance(declaration, str):
            raise SystemExit(f"{ref}: source task has no reference module/declaration")
        module_path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if not module_path.is_file():
            raise SystemExit(f"{ref}: reference module does not exist: {module}")
        rel_task = str(task_path.relative_to(ROOT))
        task_hashes[ref] = digest_file(task_path)
        reference_entries.append({
            "task_ref": ref,
            "task_manifest_path": rel_task,
            "task_manifest_sha256": task_hashes[ref],
            "reference_module": module,
            "reference_declaration": declaration,
            "reference_module_path": str(module_path.relative_to(ROOT)),
            "reference_module_sha256": digest_file(module_path),
        })
    task_set_hash = digest_bytes(("\n".join(refs) + "\n").encode())
    manifest = {
        "benchmark": "ethereum-verification-benchmark",
        "benchmark_version": "0.2",
        "contract_kind": "canonical_full_suite_selection",
        "schema_version": 2,
        "source": source,
        "task_count": len(refs),
        "task_set_sha256": task_set_hash,
        "tasks": refs,
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
