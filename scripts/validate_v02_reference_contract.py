#!/usr/bin/env python3
"""Validate the frozen v0.2 reference declarations with the Lean verifier."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "harness"))
from harness.task_runner import discover_task_refs, load_task_record, resolve_task_manifest

MANIFEST = ROOT / "benchmark-versions" / "v0.2.json"
REFERENCES = ROOT / "benchmark-versions" / "v0.2-references.json"
DEFAULT_AUDIT = ROOT / "artifacts" / "audits" / "p2-v02-reference-validation.json"
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
ESCAPE = re.compile(r"\b(?:sorry|admit|axiom)\b")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def fail(message: str) -> None:
    raise ValueError(message)


def load_json(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        fail(f"{path}: expected object")
    return data


def run_lean(module: str, declaration: str) -> tuple[bool, str]:
    # Compilation plus #check verifies the actual Lean declaration; source scanning is only
    # an additional escape-hatch guard and never the verifier decision.
    build = subprocess.run(["lake", "build", module], cwd=ROOT, text=True, capture_output=True, check=False)
    if build.returncode:
        return False, "module_compile_failed"
    with tempfile.TemporaryDirectory(prefix="v02-reference-check-") as directory:
        check = Path(directory) / "Check.lean"
        check.write_text(f"import {module}\n#check {declaration}\n", encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(check)], cwd=ROOT, text=True, capture_output=True, check=False)
    return (result.returncode == 0, "verifier_valid" if result.returncode == 0 else "declaration_check_failed")


def baseline_file_sha(commit: str, path: str) -> str:
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"], cwd=ROOT, capture_output=True, check=False
    )
    if result.returncode:
        fail(f"baseline source unavailable: {commit}:{path}")
    return hashlib.sha256(result.stdout).hexdigest()


def validate(*, verify_lean: bool, audit_path: Path) -> int:
    started = time.monotonic()
    manifest = load_json(MANIFEST)
    contract = load_json(REFERENCES)
    errors: list[str] = []
    statuses: list[dict[str, str]] = []
    try:
        if manifest.get("schema_version") != 2 or manifest.get("benchmark_version") != "0.2":
            fail("manifest schema/version mismatch")
        source = manifest.get("source")
        if not isinstance(source, dict) or not isinstance(source.get("commit"), str):
            fail("manifest source provenance malformed")
        selector_hashes = source.get("selector_files_sha256")
        if not isinstance(selector_hashes, dict) or not selector_hashes:
            fail("manifest selector source hashes missing")
        for path, expected in selector_hashes.items():
            if not isinstance(path, str) or not isinstance(expected, str) or baseline_file_sha(source["commit"], path) != expected:
                fail(f"baseline selector source hash drift: {path}")
        task_objects = manifest.get("tasks")
        mappings = manifest.get("task_manifest_sha256")
        if not isinstance(task_objects, list) or not all(isinstance(task, dict) for task in task_objects):
            fail("manifest task list malformed")
        refs = [task.get("task_ref") for task in task_objects]
        if not all(isinstance(ref, str) for ref in refs):
            fail("manifest task list malformed")
        if manifest.get("manifest_schema_version") != 1:
            fail("version manifest schema drift")
        for task in task_objects:
            if not isinstance(task.get("task_fingerprint"), str) or not isinstance(task.get("task_interface_id"), str):
                fail(f"{task.get('task_ref')}: version task metadata malformed")
        if len(refs) != len(set(refs)) or manifest.get("task_count") != len(refs):
            fail("manifest task list duplicate/count drift")
        if discover_task_refs("v0.2") != refs:
            fail("frozen v0.2-suite selector drift")
        expected_task_hash = hashlib.sha256(("\n".join(refs) + "\n").encode()).hexdigest()
        if manifest.get("task_set_sha256") != expected_task_hash:
            fail("manifest task ordering/hash drift")
        if not isinstance(mappings, dict) or set(mappings) != set(refs):
            fail("manifest task mapping missing/duplicate drift")
        if contract.get("canonical_manifest_sha256") != sha(MANIFEST):
            fail("reference contract manifest hash drift")
        entries = contract.get("tasks")
        if not isinstance(entries, list) or len(entries) != len(refs):
            fail("reference contract task count drift")
        entry_refs = [entry.get("task_ref") if isinstance(entry, dict) else None for entry in entries]
        if entry_refs != refs or len(set(entry_refs)) != len(entry_refs):
            fail("reference contract mapping order/duplicate/missing drift")
        if contract.get("task_set_sha256") != expected_task_hash:
            fail("reference contract task ordering/hash drift")
        for index, (ref, entry) in enumerate(zip(refs, entries, strict=True), start=1):
            if not isinstance(entry, dict):
                fail(f"{ref}: malformed reference entry")
            if (
                entry.get("task_fingerprint") != task_objects[index - 1].get("task_fingerprint")
                or entry.get("task_interface_id") != task_objects[index - 1].get("task_interface_id")
            ):
                fail(f"{ref}: pinned task metadata drift")
            task_path = resolve_task_manifest(ref)
            task = load_task_record(task_path)
            module = entry.get("reference_module")
            declaration = entry.get("reference_declaration")
            if not isinstance(module, str) or not IDENT.fullmatch(module) or not isinstance(declaration, str) or not IDENT.fullmatch(declaration):
                fail(f"{ref}: malformed reference module/declaration")
            if entry.get("task_manifest_path") != str(task_path.relative_to(ROOT)):
                fail(f"{ref}: task manifest path drift")
            current_task_sha = sha(task_path)
            if mappings[ref] != current_task_sha or entry.get("task_manifest_sha256") != current_task_sha:
                fail(f"{ref}: task manifest hash drift")
            actual = task["reference_solution"]
            if actual["module"] != module or actual["declaration"] != declaration:
                fail(f"{ref}: reference declaration mapping drift")
            module_path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
            if entry.get("reference_module_path") != str(module_path.relative_to(ROOT)) or not module_path.is_file():
                fail(f"{ref}: reference module missing/path drift")
            if entry.get("reference_module_sha256") != sha(module_path):
                fail(f"{ref}: reference module hash drift")
            if ESCAPE.search(module_path.read_text(encoding="utf-8")):
                fail(f"{ref}: forbidden reference escape hatch")
            if verify_lean and (index == 1 or index % 10 == 0 or index == len(refs)):
                print(f"[v0.2-reference-validation] checking={index}/{len(refs)}", flush=True)
            valid, status = run_lean(module, declaration) if verify_lean else (True, "structural_valid")
            statuses.append({"task_ref": ref, "status": status})
            if verify_lean and (index == 1 or index % 10 == 0 or index == len(refs)):
                print(f"[v0.2-reference-validation] verified={index}/{len(refs)}", flush=True)
            if not valid:
                fail(f"{ref}: {status}")
    except (OSError, json.JSONDecodeError, ValueError, subprocess.SubprocessError) as exc:
        errors.append(str(exc))
    counts = {"verifier_valid": sum(item["status"] == "verifier_valid" for item in statuses), "failed": len(errors), "total": len(statuses)}
    audit = {
        "schema_version": 1,
        "kind": "p2_v02_reference_validation",
        "classification": "no_provider",
        "source_commit": manifest.get("source", {}).get("commit") if isinstance(manifest.get("source"), dict) else None,
        "manifest_path": display_path(MANIFEST),
        "manifest_sha256": sha(MANIFEST),
        "reference_contract_path": display_path(REFERENCES),
        "reference_contract_sha256": sha(REFERENCES),
        "task_count": manifest.get("task_count"),
        "task_set_sha256": manifest.get("task_set_sha256"),
        "per_task_verifier_status": statuses,
        "totals": counts,
        "errors": errors,
        "duration_seconds": round(time.monotonic() - started, 3),
    }
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(display_path(audit_path))
    return 0 if not errors and (not verify_lean or counts["verifier_valid"] == manifest.get("task_count")) else 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-lean", action="store_true", help="structural regression-test mode only")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT)
    args = parser.parse_args()
    return validate(verify_lean=not args.no_lean, audit_path=args.audit)


if __name__ == "__main__":
    raise SystemExit(main())
