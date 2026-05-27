#!/usr/bin/env python3
"""Enforce the trusted boundary axiom ledger."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "trusted-axioms.json"
SCAN_ROOTS = [ROOT / "Benchmark", ROOT / "cases", ROOT / "backlog"]

AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
LINE_COMMENT_RE = re.compile(r"--.*$")


def load_ledger() -> set[tuple[str, str]]:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    entries = data.get("axioms")
    if not isinstance(entries, list):
        raise SystemExit("trusted-axioms.json: expected top-level 'axioms' list")

    allowed: set[tuple[str, str]] = set()
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise SystemExit(f"trusted-axioms.json: axiom entry {index} must be an object")
        path = entry.get("path")
        name = entry.get("name")
        boundary = entry.get("boundary")
        justification = entry.get("justification")
        if not all(isinstance(value, str) and value.strip() for value in (path, name, boundary, justification)):
            raise SystemExit(
                f"trusted-axioms.json: axiom entry {index} needs non-empty path/name/boundary/justification"
            )
        resolved = (ROOT / path).resolve()
        try:
            resolved.relative_to(ROOT.resolve())
        except ValueError:
            raise SystemExit(f"trusted-axioms.json: path escapes repository: {path}")
        if not resolved.is_file():
            raise SystemExit(f"trusted-axioms.json: listed axiom path does not exist: {path}")
        allowed.add((path, name))
    return allowed


def discover_axioms() -> list[tuple[str, int, str]]:
    hits: list[tuple[str, int, str]] = []
    for root in SCAN_ROOTS:
        if not root.is_dir():
            continue
        for path in sorted(root.rglob("*.lean")):
            rel = str(path.relative_to(ROOT))
            for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
                cleaned = LINE_COMMENT_RE.sub("", line)
                match = AXIOM_RE.match(cleaned)
                if match:
                    hits.append((rel, lineno, match.group(1)))
    return hits


def main() -> int:
    allowed = load_ledger()
    discovered = discover_axioms()
    discovered_keys = {(path, name) for path, _lineno, name in discovered}

    errors: list[str] = []
    for path, lineno, name in discovered:
        if (path, name) not in allowed:
            errors.append(f"unlisted axiom {name} at {path}:{lineno}")

    for path, name in sorted(allowed - discovered_keys):
        errors.append(f"ledger entry not found in Lean sources: {path}::{name}")

    if errors:
        print("trusted axiom ledger check failed", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(f"trusted axiom ledger OK: {len(discovered)} axiom declaration(s) accounted for")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
