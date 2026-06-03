#!/usr/bin/env python3
"""Audit reference solution Lean files for placeholder tokens and declarations.

Scans every reference solution module referenced by task manifests and
fails if any contains `sorry` or `admit` placeholders, or if a referenced
declaration is not declared in the referenced source module.

Usage:
    python3 scripts/check_reference_solutions.py
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from manifest_utils import load_manifest_data

ROOT = Path(__file__).resolve().parent.parent

TASK_DIRS = [ROOT / "cases", ROOT / "backlog"]
PROOF_READY_STATUSES = {"partial", "complete"}

# Tokens that indicate an incomplete proof.
PLACEHOLDER_TOKENS = ("sorry", "admit")

# Matches standalone sorry/admit (not inside comments or strings).
# This is a best-effort heuristic — it catches the common cases.
_PLACEHOLDER_RE = re.compile(
    r"(?:^|\s)(?:" + "|".join(PLACEHOLDER_TOKENS) + r")(?:\s|$)", re.MULTILINE
)

# Matches Lean single-line comments
_LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
_DECL_RE = re.compile(
    r"^\s*(?:private\s+)?(?:theorem|lemma|def|abbrev|opaque|axiom)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)*)\b")
_END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)*))?\s*$")


def lean_module_path(module_name: str) -> Path:
    return ROOT.joinpath(*module_name.split(".")).with_suffix(".lean")


def strip_comments(text: str) -> str:
    """Strip single-line comments. Block comments are rare in proof files."""
    return _LINE_COMMENT_RE.sub("", text)


def check_file(path: Path) -> list[tuple[int, str]]:
    """Return list of (line_number, line) containing placeholder tokens."""
    text = path.read_text(encoding="utf-8")
    hits: list[tuple[int, str]] = []
    for i, line in enumerate(text.splitlines(), start=1):
        cleaned = _LINE_COMMENT_RE.sub("", line)
        for token in PLACEHOLDER_TOKENS:
            # Match as a whole word
            if re.search(rf"\b{token}\b", cleaned):
                hits.append((i, line.rstrip()))
                break
    return hits


def declared_names(path: Path) -> set[str]:
    """Return top-level declaration names, including active namespace prefixes."""
    names: set[str] = set()
    namespaces: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        cleaned = _LINE_COMMENT_RE.sub("", line).strip()
        namespace_match = _NAMESPACE_RE.match(cleaned)
        if namespace_match:
            namespaces.append(namespace_match.group(1))
            continue
        end_match = _END_RE.match(cleaned)
        if end_match:
            if namespaces and end_match.group(1):
                namespaces.pop()
            continue
        decl_match = _DECL_RE.match(cleaned)
        if decl_match:
            name = decl_match.group(1)
            names.add(name)
            if namespaces:
                names.add(".".join([*namespaces, name]))
    return names


def discover_task_manifests() -> list[Path]:
    """Find all task manifest YAML files under cases/ and backlog/."""
    manifests: list[Path] = []
    for task_dir in TASK_DIRS:
        if task_dir.is_dir():
            manifests.extend(sorted(task_dir.rglob("tasks/*.yaml")))
    return manifests


def main() -> None:
    manifests = discover_task_manifests()

    checked = 0
    failures: dict[Path, dict[str, object]] = {}
    missing: list[tuple[str, str]] = []
    missing_declarations: list[tuple[str, str, str]] = []
    checked_cache: dict[Path, list[tuple[int, str]]] = {}
    declaration_cache: dict[Path, set[str]] = {}

    for manifest_path in manifests:
        task = load_manifest_data(manifest_path)
        if task.get("proof_status") not in PROOF_READY_STATUSES:
            continue
        ref_module = task.get("reference_solution_module")
        if not ref_module:
            continue

        path = lean_module_path(str(ref_module))
        if not path.is_file():
            missing.append((str(task.get("task_id", "?")), str(ref_module)))
            continue
        ref_decl = task.get("reference_solution_declaration")
        if isinstance(ref_decl, str) and ref_decl:
            names = declaration_cache.get(path)
            if names is None:
                names = declared_names(path)
                declaration_cache[path] = names
            if ref_decl not in names:
                missing_declarations.append(
                    (str(task.get("task_id", "?")), str(ref_module), ref_decl)
                )

        hits = checked_cache.get(path)
        if hits is None:
            checked += 1
            hits = check_file(path)
            checked_cache[path] = hits
        if hits:
            task_ids = failures.setdefault(path, {"task_ids": [], "hits": hits})["task_ids"]
            assert isinstance(task_ids, list)
            task_ids.append(str(task.get("task_id", "?")))

    print(f"Reference solution audit: {checked} files checked.")

    if missing:
        print(f"\nERROR: {len(missing)} reference solution module(s) not found:", file=sys.stderr)
        for task_id, module in missing:
            print(f"  {task_id}: {module}", file=sys.stderr)

    if missing_declarations:
        print(
            f"\nERROR: {len(missing_declarations)} referenced declaration(s) not found in source:",
            file=sys.stderr,
        )
        for task_id, module, declaration in missing_declarations:
            print(f"  {task_id}: {module}::{declaration}", file=sys.stderr)

    if failures:
        print(
            f"\nERROR: {len(failures)} reference solution file(s) contain placeholder tokens:",
            file=sys.stderr,
        )
        for path, failure in failures.items():
            rel = path.relative_to(ROOT)
            task_ids = ", ".join(sorted(set(failure["task_ids"])))
            print(f"\n  {rel} (tasks: {task_ids}):", file=sys.stderr)
            hits = failure["hits"]
            assert isinstance(hits, list)
            for lineno, line in hits:
                print(f"    line {lineno}: {line}", file=sys.stderr)
    if missing or missing_declarations or failures:
        sys.exit(1)
    else:
        print(
            f"OK: reference solution declarations found for checked task manifests."
        )
        print("OK: no placeholder tokens (sorry/admit) found in reference solutions.")


if __name__ == "__main__":
    main()
