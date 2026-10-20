#!/usr/bin/env python3
"""Check that editable task files under Benchmark/Generated ship no proof.

Task files are hand-authored (see scripts/generate_task_skeletons.py and
CONTRIBUTING.md); nothing regenerates them from the reference proofs, so this
check is the guard that keeps a reference proof from leaking into the file an
agent starts from.

A task file is accepted when:

* it declares no top-level theorem/lemma/def/... other than the task theorem
  (helper lemmas with proofs would hand the agent part of the solution), and
* the task theorem body, ignoring comments, is a placeholder: ``exact ?_``,
  ``sorry``, or the grind-first skeleton emitted by
  ``generate_task_skeletons.py`` (``unfold <spec>`` followed by a bare
  ``grind`` / ``grind [hints]``), which is a hint, not a proof.

Usage: python3 scripts/task_file_policy.py [FILE ...]   (default: all task files)
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TASK_GLOB = "Benchmark/Generated/*/*/Tasks/*.lean"

PLACEHOLDER_BODIES = ({"exact ?_"}, {"sorry"})
_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|axiom|opaque)\b\s*([^\s:({\[]*)"
)
_SKELETON_UNFOLD_RE = re.compile(r"^unfold\s+\S+$")
_SKELETON_GRIND_RE = re.compile(r"^grind(\s*\[[^\]]*\])?$")


def _strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def _is_placeholder(body_lines: list[str]) -> bool:
    if set(body_lines) in PLACEHOLDER_BODIES and len(body_lines) == 1:
        return True
    return (
        len(body_lines) == 2
        and bool(_SKELETON_UNFOLD_RE.match(body_lines[0]))
        and bool(_SKELETON_GRIND_RE.match(body_lines[1]))
    )


def task_file_errors(path: Path) -> list[str]:
    """Return policy violations for one editable task file."""
    lines = _strip_comments(path.read_text(encoding="utf-8")).splitlines()
    decls = [(index, match) for index, line in enumerate(lines) if (match := _DECL_RE.match(line))]
    rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
    if not decls:
        return [f"{rel}: no task theorem found"]
    errors: list[str] = []
    if len(decls) > 1:
        names = ", ".join(f"{m.group(1)} {m.group(2)}" for _, m in decls)
        errors.append(f"{rel}: task files must declare only the task theorem, found: {names}")
    start, _ = decls[-1]
    body_start = None
    for index in range(start, len(lines)):
        if ":= by" in lines[index]:
            body_start = index
            tail = lines[index].split(":= by", 1)[1].strip()
            break
    if body_start is None:
        return errors + [f"{rel}: task theorem has no `:= by` tactic body"]
    body = [tail] if tail else []
    for line in lines[body_start + 1:]:
        if line.startswith("end ") or line.strip() == "end":
            break
        if line.strip():
            body.append(line.strip())
    if not _is_placeholder(body):
        preview = " ".join(body)[:120]
        errors.append(f"{rel}: task theorem body must be a placeholder (`exact ?_`), found: {preview!r}")
    return errors


def all_task_files() -> list[Path]:
    return sorted(ROOT.glob(TASK_GLOB))


def main(argv: list[str]) -> int:
    paths = [Path(arg).resolve() for arg in argv] or all_task_files()
    errors = [error for path in paths for error in task_file_errors(path)]
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    print(f"task file policy OK: {len(paths)} file(s) contain no proof")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
