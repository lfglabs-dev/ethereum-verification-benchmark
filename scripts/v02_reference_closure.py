"""Collect the case-local proof/helper closure for frozen v0.2 references.

The boundary is deliberately the directory containing a declared reference
module, and only modules whose filename contains ``Proof`` participate. We
include that module and recursively include only repo-local, case-local proof
imports (for example ``Slot0Proof.lean``). This pins proof helpers without
pulling implementation/specification modules or shared library dependencies
into the reference-proof contract.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path


IMPORT = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b", re.MULTILINE)
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


def module_path(root: Path, module: str) -> Path:
    """Return a normalized, repository-contained path for a Lean module."""
    if not MODULE.fullmatch(module):
        raise ValueError(f"malformed Lean import module: {module!r}")
    root = root.resolve()
    path = root.joinpath(*module.split(".")).with_suffix(".lean").resolve()
    if not path.is_relative_to(root):
        raise ValueError(f"Lean import path escapes repository: {module!r}")
    return path


def collect_reference_closure(root: Path, module: str) -> list[dict[str, str]]:
    """Return sorted path/hash records for a bounded, cycle-safe helper closure."""
    root = root.resolve()
    entry = module_path(root, module)
    if not entry.is_file():
        raise ValueError(f"reference module missing: {module}")
    boundary = entry.parent.resolve()
    pending = [module]
    visited: set[str] = set()
    records: list[dict[str, str]] = []
    # The bound makes malformed/generated import graphs fail closed instead of
    # consuming unbounded resources. v0.2's case-local proof closures are tiny.
    while pending:
        if len(visited) >= 128:
            raise ValueError(f"reference import closure exceeds bound: {module}")
        current = pending.pop()
        if current in visited:
            continue
        path = module_path(root, current)
        if not path.is_file():
            raise ValueError(f"repo-local reference helper missing: {current}")
        if not path.is_relative_to(boundary) or "Proof" not in path.stem:
            # This is a real repo-local import, but outside the documented
            # proof/helper boundary, so it is intentionally not contract input.
            continue
        visited.add(current)
        text = path.read_text(encoding="utf-8")
        records.append({
            "module": current,
            "path": str(path.relative_to(root)),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        })
        for imported in IMPORT.findall(text):
            imported_path = module_path(root, imported)
            if imported_path.is_relative_to(boundary) and "Proof" in imported_path.stem:
                pending.append(imported)
    return sorted(records, key=lambda record: record["path"])
