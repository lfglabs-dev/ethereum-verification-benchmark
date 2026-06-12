#!/usr/bin/env python3
"""Lint: agent-visible Grindset modules must stay contract-agnostic.

The modules shipped into every agent workspace (see
harness/workspace_builder.py `grindset_modules`) may not reference any
`Benchmark.Cases.*` name in code. Doc comments may mention cases for
context; identifiers and imports may not. This is the structural guard
against benchmark answers leaking into the agent-visible lemma library.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Must match the always-shipped set in harness/workspace_builder.py.
SHIPPED_MODULES = [
    "Benchmark/Grindset/Attr.lean",
    "Benchmark/Grindset/Monad.lean",
    "Benchmark/Grindset/Core.lean",
    "Benchmark/Grindset/Reach.lean",
    "Benchmark/Grindset/ArithCore.lean",
]

CASE_REF = re.compile(r"Benchmark\.Cases\.")


def strip_comments(text: str) -> str:
    # Remove block comments (handles nesting poorly but Lean comments here
    # are simple) and line comments.
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def main() -> int:
    errors: list[str] = []

    builder = (ROOT / "harness" / "workspace_builder.py").read_text(encoding="utf-8")
    match = re.search(r"grindset_modules = \{([^}]*)\}", builder)
    if not match:
        errors.append("could not locate grindset_modules in harness/workspace_builder.py")
    else:
        shipped = {name.strip().strip('"') for name in match.group(1).split(",") if name.strip()}
        expected = {Path(rel).name for rel in SHIPPED_MODULES}
        if shipped != expected:
            errors.append(
                "SHIPPED_MODULES out of sync with workspace_builder grindset_modules: "
                f"lint={sorted(expected)} builder={sorted(shipped)}"
            )

    for rel in SHIPPED_MODULES:
        path = ROOT / rel
        if not path.is_file():
            errors.append(f"missing shipped Grindset module: {rel}")
            continue
        code = strip_comments(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), start=1):
            if CASE_REF.search(line):
                errors.append(f"{rel}:{lineno}: references Benchmark.Cases.* in code: {line.strip()}")
            if re.search(r"^\s*import\s+Benchmark\.Cases", line):
                errors.append(f"{rel}:{lineno}: imports a Benchmark.Cases module")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("grindset generic checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
