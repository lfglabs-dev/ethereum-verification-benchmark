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
from harness.verify_lease import verify_lease
from harness.v02_release import BASELINE_COMMIT, RELEASE_METADATA, RELEASE_SOURCE
from scripts.compute_fingerprints import (
    baseline_version_metadata,
    trusted_closure_helper_namespace,
)

MANIFEST = ROOT / "benchmark-versions" / "v0.2.json"
REFERENCES = ROOT / "benchmark-versions" / "v0.2-references.json"
DEFAULT_AUDIT = ROOT / "artifacts" / "audits" / "p2-v02-reference-validation.json"
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
ESCAPE = re.compile(r"\b(?:sorry|admit|axiom)\b")

# ``environment_id`` is release metadata, not an ambient validation value: v0.2
# pins its baseline environment (including the Verity dependency revision).  A
# later dependency update receives a new ID only when generating a new version.
VERSION_METADATA_FIELDS = (
    "benchmark",
    "benchmark_version",
    "created_at",
    "git_sha",
    "manifest_schema_version",
    "task_count",
    "task_set_id",
    "harness_id",
    "environment_id",
    "mode",
    "budget",
)
MANIFEST_FIELDS = frozenset((*VERSION_METADATA_FIELDS, "contract_kind", "schema_version", "source", "task_set_sha256", "tasks", "task_manifest_sha256"))
REFERENCE_FIELDS = frozenset(("benchmark", "benchmark_version", "contract_kind", "schema_version", "source_commit", "canonical_manifest_path", "canonical_manifest_sha256", "task_count", "task_set_sha256", "tasks"))


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


def lean_code(text: str) -> str:
    """Remove Lean comments before looking for proof escape declarations."""
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and text.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            index = len(text) if newline == -1 else newline + 1
            result.append("\n")
        else:
            result.append(text[index])
            index += 1
    return "".join(result)


def run_lean(module: str, declaration: str) -> tuple[bool, str]:
    # Compilation plus #check verifies the actual Lean declaration; source scanning is only
    # an additional escape-hatch guard and never the verifier decision.
    with verify_lease(label="v02_reference_validation"):
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
        fail(f"pinned source unavailable (infra): {commit}:{path}")
    return hashlib.sha256(result.stdout).hexdigest()


def validate(*, verify_lean: bool, audit_path: Path) -> int:
    started = time.monotonic()
    manifest = load_json(MANIFEST)
    contract = load_json(REFERENCES)
    errors: list[str] = []
    statuses: list[dict[str, str]] = []
    try:
        source = manifest.get("source")
        if not isinstance(source, dict) or not isinstance(source.get("commit"), str):
            fail("manifest source provenance malformed")
        if set(manifest) != MANIFEST_FIELDS:
            fail("manifest canonical field set drift")
        if set(contract) != REFERENCE_FIELDS:
            fail("reference contract canonical field set drift")
        # Check the reviewed literals before any candidate-provided source
        # identity is used to read Git objects or execute the closure helper.
        if source != RELEASE_SOURCE:
            fail("release trust-root source provenance drift")
        if {field: manifest.get(field) for field in VERSION_METADATA_FIELDS} != RELEASE_METADATA:
            fail("release trust-root version metadata drift")
        try:
            baseline_metadata = baseline_version_metadata(BASELINE_COMMIT, version="0.2", created_at=RELEASE_METADATA["created_at"])
        except ValueError as exc:
            fail(f"pinned source unavailable (infra): {exc}")
        if {field: manifest.get(field) for field in VERSION_METADATA_FIELDS} != baseline_metadata:
            fail("pinned baseline version metadata drift")
        # Verify before executing its closure algorithm; it is never imported
        # from the mutable candidate checkout.
        closure_namespace = trusted_closure_helper_namespace()
        collect_reference_closure = closure_namespace.get("collect_reference_closure")
        if not callable(collect_reference_closure):
            fail("trusted closure helper missing collect_reference_closure")
        expected_source = RELEASE_SOURCE
        if source != expected_source:
            fail("pinned baseline source provenance drift")
        if manifest.get("schema_version") != 2 or manifest.get("benchmark_version") != "0.2":
            fail("manifest schema/version mismatch")
        selector_hashes = source.get("selector_files_sha256")
        if not isinstance(selector_hashes, dict) or not selector_hashes:
            fail("manifest selector source hashes missing")
        for path, expected in selector_hashes.items():
            if not isinstance(path, str) or not isinstance(expected, str) or baseline_file_sha(source["commit"], path) != expected:
                fail(f"baseline selector source hash drift: {path}")
        from scripts.compute_fingerprints import baseline_contract_entries, task_entries

        try:
            baseline_entries, baseline_references = baseline_contract_entries(BASELINE_COMMIT)
        except ValueError as exc:
            fail(f"pinned source unavailable (infra): {exc}")
        current_entries = task_entries("all")
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
        if set(baseline_entries) != set(refs):
            fail("pinned baseline task set drift")
        if not set(refs).issubset(current_entries):
            fail("current frozen task missing")
        for task in task_objects:
            ref = task["task_ref"]
            if baseline_entries[ref] != task:
                fail(f"{ref}: pinned baseline canonical task entry drift")
            if current_entries[ref] != baseline_entries[ref]:
                fail(f"{ref}: current task source canonical entry drift")
        if discover_task_refs("v0.2") != refs:
            fail("frozen v0.2-suite selector drift")
        expected_task_hash = hashlib.sha256(("\n".join(refs) + "\n").encode()).hexdigest()
        if manifest.get("task_set_sha256") != expected_task_hash:
            fail("manifest task ordering/hash drift")
        if not isinstance(mappings, dict) or set(mappings) != set(refs):
            fail("manifest task mapping missing/duplicate drift")
        if contract.get("canonical_manifest_sha256") != sha(MANIFEST):
            fail("reference contract manifest hash drift")
        expected_reference_metadata = {
            "benchmark": "ethereum-verification-benchmark",
            "benchmark_version": "0.2",
            "contract_kind": "canonical_reference_declarations",
            "schema_version": 2,
            "source_commit": BASELINE_COMMIT,
            "canonical_manifest_path": str(MANIFEST.relative_to(ROOT)),
            "canonical_manifest_sha256": sha(MANIFEST),
            "task_count": manifest["task_count"],
            "task_set_sha256": manifest["task_set_sha256"],
        }
        if {field: contract.get(field) for field in expected_reference_metadata} != expected_reference_metadata:
            fail("pinned baseline reference metadata drift")
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
            pinned_reference = baseline_references.get(ref)
            if not isinstance(pinned_reference, dict):
                fail(f"{ref}: pinned reference entry missing")
            for field in (
                "reference_module",
                "reference_declaration",
                "reference_module_path",
                "reference_module_sha256",
                "reference_import_closure",
            ):
                if entry.get(field) != pinned_reference.get(field):
                    fail(f"{ref}: pinned reference {field} drift")
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
            closure = entry.get("reference_import_closure")
            if not isinstance(closure, list) or not closure:
                fail(f"{ref}: malformed reference import closure")
            for member in closure:
                if not isinstance(member, dict) or set(member) != {"module", "path", "sha256"}:
                    fail(f"{ref}: malformed reference import closure")
                path = ROOT / member["path"] if isinstance(member.get("path"), str) else None
                if path is None or not path.is_file():
                    fail(f"{ref}: reference helper missing/hash drift")
                if ESCAPE.search(lean_code(path.read_text(encoding="utf-8"))):
                    fail(f"{ref}: forbidden reference escape hatch")
                if member.get("sha256") != sha(path):
                    fail(f"{ref}: reference helper missing/hash drift")
            if closure != collect_reference_closure(ROOT, module):
                fail(f"{ref}: reference import closure drift")
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
        "classification": "infra_unavailable" if any("(infra)" in error for error in errors) else "no_provider",
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


def ensure_structural_contract() -> None:
    """Fail closed before a frozen run can execute a task or contact a provider.

    This deliberately performs only the structural/hash/closure checks.  Full
    Lean proof validation remains the release-validation job, not per-task
    harness startup work.
    """
    with tempfile.TemporaryDirectory(prefix="v02-reference-preflight-") as directory:
        audit = Path(directory) / "audit.json"
        if validate(verify_lean=False, audit_path=audit) != 0:
            errors = json.loads(audit.read_text(encoding="utf-8")).get("errors", [])
            raise ValueError("v0.2 reference preflight failed: " + (str(errors[0]) if errors else "unknown error"))


if __name__ == "__main__":
    raise SystemExit(main())
