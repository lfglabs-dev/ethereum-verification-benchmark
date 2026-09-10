#!/usr/bin/env python3
"""Select the active benchmark cases that a Git diff can affect.

The PR workflow uses this as a deliberately conservative routing layer:

* files below an active ``cases/<project>/<case>`` directory select that case;
* Lean source files are mapped through the current task manifests; and
* shared runtime, CI, and unrecognised source changes request full validation.

It is not a replacement for the scheduled frozen-release validation.  Its
only job is to keep ordinary case PRs small while failing closed when the
changed surface cannot be attributed safely.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parent.parent
if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from manifest_utils import load_manifest_data


@dataclass(frozen=True)
class ChangedFile:
    """One path from ``git diff --name-status``."""

    status: str
    path: str


@dataclass(frozen=True)
class CaseInfo:
    case_id: str
    family_id: str | None
    implementation_id: str | None
    source_paths: frozenset[str]


@dataclass(frozen=True)
class Selection:
    cases: tuple[str, ...]
    full: bool
    reasons: tuple[str, ...]

    def as_dict(self) -> dict[str, object]:
        return {
            "cases": list(self.cases),
            "full": self.full,
            "reasons": list(self.reasons),
        }


GLOBAL_PREFIXES = (
    ".github/",
    "harness/",
    "schemas/",
    "scripts/",
    "benchmark-versions/",
)
GLOBAL_FILES = {
    "Benchmark.lean",
    "benchmark.toml",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
    "trusted-axioms.json",
}
SAFE_PREFIXES = ("analysis/", "docs/", "results/", "tests/")
SAFE_FILES = {
    ".env.example",
    ".gitignore",
    "CONTRIBUTING.md",
    "README.md",
    "REPORT.md",
    "benchmark-inventory.json",
    "leaderboard.md",
    "plan.md",
    "results.json",
}


def _module_path(module: object) -> str | None:
    if not isinstance(module, str) or not module:
        return None
    if "/" in module or "\\" in module:
        return None
    return module.replace(".", "/") + ".lean"


def _string(value: object) -> str | None:
    return value.strip() if isinstance(value, str) and value.strip() else None


def _path_list(value: object) -> list[str]:
    if not isinstance(value, list):
        return []
    return [item for item in value if isinstance(item, str) and item]


def _relative(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def load_active_cases(root: Path = ROOT) -> tuple[CaseInfo, ...]:
    """Build a manifest-derived index of active case source paths."""
    cases: list[CaseInfo] = []
    for case_manifest in sorted((root / "cases").glob("*/*/case.yaml")):
        case_data = load_manifest_data(case_manifest)
        project = case_manifest.parent.parent.name
        case_name = case_manifest.parent.name
        case_id = f"{project}/{case_name}"
        paths = {_relative(case_manifest, root)}

        for key in ("lean_target", "spec_target", "proof_target"):
            module_path = _module_path(case_data.get(key))
            if module_path:
                paths.add(module_path)

        for task_manifest in sorted(case_manifest.parent.glob("tasks/*.yaml")):
            task_data = load_manifest_data(task_manifest)
            paths.add(_relative(task_manifest, root))
            for key in ("implementation_files", "specification_files", "editable_files"):
                paths.update(_path_list(task_data.get(key)))
            module_path = _module_path(task_data.get("reference_solution_module"))
            if module_path:
                paths.add(module_path)

        cases.append(
            CaseInfo(
                case_id=case_id,
                family_id=_string(case_data.get("family_id")),
                implementation_id=_string(case_data.get("implementation_id")),
                source_paths=frozenset(paths),
            )
        )
    return tuple(cases)


def _normalise_path(path: str) -> str | None:
    path = path.replace("\\", "/")
    while path.startswith("./"):
        path = path[2:]
    parts = path.split("/")
    if not path or path.startswith("/") or any(part in {"", ".", ".."} for part in parts):
        return None
    return path


def _case_from_case_path(path: str) -> str | None:
    parts = path.split("/")
    if len(parts) < 3 or parts[0] != "cases":
        return None
    return f"{parts[1]}/{parts[2]}"


def select_changes(changes: Iterable[ChangedFile], *, root: Path = ROOT) -> Selection:
    """Return affected active cases and whether the full check is required."""
    change_list = tuple(changes)
    try:
        case_infos = load_active_cases(root)
    except (OSError, ValueError) as exc:
        return Selection((), True, (f"could not load active manifests: {exc}",))

    source_to_cases: dict[str, set[str]] = {}
    for case in case_infos:
        for source_path in case.source_paths:
            source_to_cases.setdefault(source_path, set()).add(case.case_id)

    selected: set[str] = set()
    reasons: list[str] = []
    full = False

    def require_full(reason: str) -> None:
        nonlocal full
        full = True
        if reason not in reasons:
            reasons.append(reason)

    for change in change_list:
        path = _normalise_path(change.path)
        if path is None:
            require_full(f"invalid changed path: {change.path!r}")
            continue

        status = change.status[:1]
        # Deleted or renamed source can no longer be resolved from the current
        # manifest index.  Let the full validator make the definitive call.
        if status == "D" and path.startswith(("cases/", "backlog/", "Benchmark/", "families/")):
            require_full(f"removed benchmark source: {path}")
            continue

        if path.startswith(GLOBAL_PREFIXES) or path in GLOBAL_FILES:
            require_full(f"shared CI/runtime surface changed: {path}")
            continue

        direct_case = _case_from_case_path(path)
        if direct_case:
            selected.add(direct_case)
            continue

        if path.startswith("backlog/"):
            require_full(f"backlog benchmark source changed: {path}")
            continue

        if path.startswith("families/"):
            parts = path.split("/")
            if len(parts) < 3:
                require_full(f"unrecognised family path: {path}")
                continue
            family_id = parts[1]
            implementation_id = None
            if len(parts) >= 5 and parts[2] == "implementations":
                implementation_id = parts[3]
            matches = [
                case.case_id
                for case in case_infos
                if case.family_id == family_id
                and (implementation_id is None or case.implementation_id == implementation_id)
            ]
            selected.update(matches)
            continue

        if path.startswith("Benchmark/"):
            matches = source_to_cases.get(path)
            if matches:
                selected.update(matches)
            else:
                require_full(f"unmapped Lean source changed: {path}")
            continue

        if path.startswith(SAFE_PREFIXES) or path in SAFE_FILES:
            continue

        require_full(f"unrecognised repository source changed: {path}")

    return Selection(tuple(sorted(selected)), full, tuple(reasons))


def git_changes(*, base: str, head: str, root: Path = ROOT) -> tuple[ChangedFile, ...]:
    """Read a rename-aware diff and make destructive paths fail closed."""
    result = subprocess.run(
        ["git", "diff", "--name-status", "--find-renames", "--find-copies", "-z", base, head],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        error = result.stderr.decode("utf-8", errors="replace").strip()
        raise ValueError(error or f"could not diff {base}..{head}")

    fields = result.stdout.decode("utf-8", errors="surrogateescape").split("\0")
    changes: list[ChangedFile] = []
    index = 0
    while index < len(fields) - 1:
        status = fields[index]
        index += 1
        if not status:
            continue
        kind = status[:1]
        if kind in {"R", "C"}:
            if index + 1 >= len(fields):
                raise ValueError(f"malformed {status} diff entry")
            old_path, new_path = fields[index], fields[index + 1]
            index += 2
            # Treat renames/copies conservatively.  The old source may have
            # been an import that the new manifest no longer records.
            changes.append(ChangedFile("D", old_path))
            changes.append(ChangedFile("A", new_path))
            continue
        if index >= len(fields):
            raise ValueError(f"malformed {status} diff entry")
        changes.append(ChangedFile(kind, fields[index]))
        index += 1
    return tuple(changes)


def _write_github_output(path: Path, selection: Selection) -> None:
    reason = "; ".join(selection.reasons).replace("\r", " ").replace("\n", " ")
    with path.open("a", encoding="utf-8") as output:
        output.write(f"cases={json.dumps(list(selection.cases), separators=(',', ':'))}\n")
        output.write(f"full={'true' if selection.full else 'false'}\n")
        output.write(f"reason={reason}\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="base commit for the diff")
    parser.add_argument("--head", default="HEAD", help="head commit for the diff")
    parser.add_argument("--force-full", action="store_true", help="skip diff resolution and request full validation")
    parser.add_argument("--github-output", type=Path, help="write cases/full/reason to a GitHub Actions output file")
    args = parser.parse_args()

    if args.force_full:
        selection = Selection((), True, ("event has no trustworthy diff base",))
    elif not args.base:
        parser.error("--base is required unless --force-full is used")
    else:
        try:
            selection = select_changes(git_changes(base=args.base, head=args.head))
        except ValueError as exc:
            selection = Selection((), True, (f"could not resolve changed files: {exc}",))

    print(json.dumps(selection.as_dict(), sort_keys=True))
    if args.github_output:
        _write_github_output(args.github_output, selection)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
