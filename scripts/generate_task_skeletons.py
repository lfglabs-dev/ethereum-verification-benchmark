#!/usr/bin/env python3
"""Grind-first task skeleton generator for Benchmark/Generated/**/Tasks/*.lean.

This script rewrites (or previews) the editable proof template for every task
manifest under ``cases/``. The rewriter keeps everything an agent relies on to
understand the goal — imports of the case's ``Specs``, namespace, ``open``
declarations, the theorem docstring, and the theorem signature — but swaps the
proof body for a grind-first skeleton that also imports ``Benchmark.Grindset``.

Default skeleton body:

    import Benchmark.Grindset
    ...
    theorem foo ... := by
      -- Grindset-first: unfold the spec, then try grind with case-local hints.
      -- If grind fails, see harness/PROOF_PATTERNS.md for simp / by_cases
      -- fallbacks and for the `grind?` lemma-discovery loop.
      unfold foo_spec
      grind [ContractName.fn, ContractName.fieldA, ContractName.fieldB]

When we cannot confidently determine the contract symbols to hint (no call of
the form ``ContractName.fn`` appears in the theorem body, or no companion
``Contract.lean`` is found), the body falls back to a bare ``grind`` followed
by a ``sorry`` line that is commented out — the agent still sees a grind-first
template without the script fabricating a hint list.

Usage
-----

Dry-run a preview of every regenerated template into
``Benchmark/GeneratedPreview/`` without touching live files::

    python3 scripts/generate_task_skeletons.py --preview

Rewrite live ``Benchmark/Generated/...`` files in place (only do this when
you are sure no live benchmark run is reading them)::

    python3 scripts/generate_task_skeletons.py --in-place

Operate on a single task file::

    python3 scripts/generate_task_skeletons.py --preview \\
        Benchmark/Generated/Lido/VaulthubLocked/Tasks/CeildivSandwich.lean

Emit a single unified patch instead of writing files::

    python3 scripts/generate_task_skeletons.py --patch > grindset/s3-skeletons.patch

Assumptions
-----------

* The live generator for Verity benchmark tasks is the human author following
  ``CONTRIBUTING.md``; there is no pre-existing Python scaffolding tool. This
  script stands in as the canonical rewriter so future task skeletons inherit
  the grind-first shape automatically.
* ``Benchmark.Grindset`` is either the real bundle of ``@[grind]`` lemmas from
  branch ``grindset/s1-verity-grindset`` or the empty stub shipped alongside
  this script on ``grindset/s3-skeleton-gen``. Either way, ``import
  Benchmark.Grindset`` resolves and is safe.
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
GENERATED_ROOT = ROOT / "Benchmark" / "Generated"
PREVIEW_ROOT = ROOT / "Benchmark" / "GeneratedPreview"
CASES_ROOT = ROOT / "Benchmark" / "Cases"
GRINDSET_IMPORT = "import Benchmark.Grindset"
PLACEHOLDER_LINE_RE = re.compile(
    r"^\s*--\s*Replace this placeholder with a complete Lean proof\.\s*$"
)


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------


@dataclass
class TemplateFile:
    path: Path
    imports: list[str]
    namespace: str | None
    opens: list[str]
    docstring: list[str] | None
    theorem_prelude: list[str]
    theorem_body_keep: list[str]
    theorem_name: str
    trailing: list[str]
    raw: str


_THEOREM_RE = re.compile(r"^\s*theorem\s+([A-Za-z_][A-Za-z0-9_']*)\b")


def parse_template(path: Path) -> TemplateFile | None:
    """Parse an existing ``Tasks/<Name>.lean`` skeleton into its structural
    parts. Returns ``None`` for files that do not look like a task template
    (missing a ``theorem`` or a ``:= by`` body)."""

    text = path.read_text()
    lines = text.splitlines()

    imports: list[str] = []
    namespace: str | None = None
    opens: list[str] = []
    docstring: list[str] | None = None
    theorem_prelude: list[str] = []
    theorem_name = ""
    theorem_body_keep: list[str] = []
    trailing: list[str] = []

    i = 0
    n = len(lines)

    # imports / namespace / opens / blanks, until we hit `/--` or `theorem`
    while i < n:
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(line)
            i += 1
            continue
        if stripped.startswith("namespace "):
            namespace = stripped[len("namespace "):].strip()
            i += 1
            continue
        if stripped.startswith("open "):
            opens.append(line)
            i += 1
            continue
        if stripped == "" or stripped.startswith("--"):
            # allow blanks / line comments in the preamble
            i += 1
            continue
        if stripped.startswith("/--") or _THEOREM_RE.match(line):
            break
        # Anything else in the preamble (e.g. a `private def`) is unexpected
        # for a skeleton; fall through and let the parser bail out.
        break

    # optional docstring
    if i < n and lines[i].strip().startswith("/--"):
        doc_start = i
        while i < n and "-/" not in lines[i]:
            i += 1
        if i >= n:
            return None
        docstring = lines[doc_start:i + 1]
        i += 1

    # theorem signature up to ":= by"
    if i >= n or not _THEOREM_RE.match(lines[i]):
        return None
    m = _THEOREM_RE.match(lines[i])
    theorem_name = m.group(1)
    sig_start = i
    while i < n and ":= by" not in lines[i]:
        i += 1
    if i >= n:
        return None
    theorem_prelude = lines[sig_start:i + 1]
    i += 1

    # body lines until `end <namespace>` (or EOF)
    body_start = i
    end_marker_idx = n
    for j in range(i, n):
        if lines[j].strip().startswith("end ") and namespace is not None \
                and lines[j].strip() == f"end {namespace}":
            end_marker_idx = j
            break
    body_lines = lines[body_start:end_marker_idx]
    trailing = lines[end_marker_idx:]

    # Keep any existing body lines that are NOT the placeholder; the rewriter
    # does not use them, but we record them for dry-run diagnostics.
    for line in body_lines:
        if PLACEHOLDER_LINE_RE.match(line):
            continue
        if line.strip() in {"exact ?_", "sorry"}:
            continue
        theorem_body_keep.append(line)

    return TemplateFile(
        path=path,
        imports=imports,
        namespace=namespace,
        opens=opens,
        docstring=docstring,
        theorem_prelude=theorem_prelude,
        theorem_body_keep=theorem_body_keep,
        theorem_name=theorem_name,
        trailing=trailing,
        raw=text,
    )


# ---------------------------------------------------------------------------
# Contract-symbol extraction
# ---------------------------------------------------------------------------


_CONTRACT_CALL_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\.([a-z][A-Za-z0-9_]*)\b")
_VERITY_CONTRACT_RE = re.compile(r"^\s*verity_contract\s+([A-Z][A-Za-z0-9_]*)")
_STORAGE_FIELD_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*.+:=\s*slot\s+\d+\s*$"
)


def locate_contract_file(namespace: str | None) -> Path | None:
    """Given a namespace like ``Benchmark.Cases.Kleros.SortitionTrees``, return
    the path to the companion ``Contract.lean`` if present."""
    if not namespace:
        return None
    if not namespace.startswith("Benchmark.Cases."):
        return None
    rel = namespace.split(".")
    # rel == ["Benchmark", "Cases", "Kleros", "SortitionTrees"]
    contract = ROOT.joinpath(*rel, "Contract.lean")
    if contract.is_file():
        return contract
    return None


def parse_contract_storage(contract_path: Path) -> tuple[str | None, list[str]]:
    """Return ``(contract_name, storage_field_names)`` by scanning a
    ``verity_contract <Name> where ... storage <f> : T := slot N`` block."""
    text = contract_path.read_text()
    lines = text.splitlines()
    contract_name: str | None = None
    fields: list[str] = []
    in_storage = False
    storage_indent = None

    for line in lines:
        if contract_name is None:
            m = _VERITY_CONTRACT_RE.match(line)
            if m:
                contract_name = m.group(1)
            continue
        stripped_no_trailing = line.rstrip()
        if not in_storage:
            if stripped_no_trailing.strip() == "storage":
                in_storage = True
                storage_indent = len(line) - len(line.lstrip())
            continue
        # in storage block
        if not stripped_no_trailing.strip():
            continue
        line_indent = len(line) - len(line.lstrip())
        # Leaving the storage block when we dedent back to/below the
        # `storage` keyword.
        if line_indent <= (storage_indent or 0):
            in_storage = False
            continue
        m = _STORAGE_FIELD_RE.match(line)
        if m:
            fields.append(m.group(1))
    return contract_name, fields


def extract_contract_symbols(
    template: TemplateFile,
) -> tuple[str | None, list[str]]:
    """Return ``(ContractName, hint_symbols)`` where ``hint_symbols`` is the
    list passed inside the ``grind [...]`` brackets. ``None`` for the contract
    name means we could not confidently pick hints."""
    body_text = "\n".join(template.theorem_prelude)
    calls = _CONTRACT_CALL_RE.findall(body_text)
    if not calls:
        return None, []

    # Score candidates: the contract name used most often in the signature is
    # almost certainly the one whose storage fields we want to load.
    counts: dict[str, int] = {}
    fn_names: dict[str, list[str]] = {}
    for ctor, fn in calls:
        counts[ctor] = counts.get(ctor, 0) + 1
        fn_names.setdefault(ctor, []).append(fn)

    # Prefer the contract whose companion Contract.lean actually exists.
    contract_path = locate_contract_file(template.namespace)
    picked = None
    declared_name: str | None = None
    fields: list[str] = []
    if contract_path is not None:
        declared_name, fields = parse_contract_storage(contract_path)
        if declared_name and declared_name in counts:
            picked = declared_name

    if picked is None:
        # Fall back to the most-used Contract-like identifier.
        picked = max(counts, key=lambda k: counts[k])

    hints: list[str] = []
    # first: the contract.fn (deduped, preserving signature order)
    seen: set[str] = set()
    for fn in fn_names.get(picked, []):
        sym = f"{picked}.{fn}"
        if sym not in seen:
            hints.append(sym)
            seen.add(sym)
    # then: every declared storage field, if we found any
    for f in fields:
        sym = f"{picked}.{f}"
        if sym not in seen:
            hints.append(sym)
            seen.add(sym)
    return picked, hints


def infer_spec_name(theorem_prelude: list[str]) -> str | None:
    """Return the ``_spec`` name referenced inside the theorem signature, if
    any. We look for the first ``foo_spec`` token in the signature."""
    for line in theorem_prelude:
        m = re.search(r"\b([A-Za-z_][A-Za-z0-9_']*_spec)\b", line)
        if m:
            return m.group(1)
    return None


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def render_skeleton(template: TemplateFile) -> str:
    contract_name, hints = extract_contract_symbols(template)
    spec_name = infer_spec_name(template.theorem_prelude)

    imports = list(template.imports)
    if GRINDSET_IMPORT not in imports:
        imports.append(GRINDSET_IMPORT)

    out: list[str] = []
    out.extend(imports)
    out.append("")
    if template.namespace:
        out.append(f"namespace {template.namespace}")
        out.append("")
    out.extend(template.opens)
    if template.opens:
        out.append("")
    if template.docstring:
        out.extend(template.docstring)
    out.extend(template.theorem_prelude)

    # Proof body: grind-first
    body: list[str] = []
    body.append(
        "  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md."
    )
    body.append(
        "  -- Try `grind` with contract symbol hints; fall back to `simp` /"
    )
    body.append("  -- `by_cases` if grind leaves goals. Use `grind?` for hints.")
    if spec_name:
        body.append(f"  unfold {spec_name}")
    if hints:
        hint_list = ", ".join(hints)
        body.append(f"  grind [{hint_list}]")
    elif contract_name:
        body.append(f"  grind [{contract_name}]")
    else:
        # No confidently pickable hint list: emit a bare grind. If grind does
        # not close, the agent will replace this with a `sorry`-free proof.
        body.append("  grind")

    out.extend(body)
    if template.namespace:
        out.append("")
        out.append(f"end {template.namespace}")
    return "\n".join(out).rstrip() + "\n"


# ---------------------------------------------------------------------------
# CLI / driver
# ---------------------------------------------------------------------------


def iter_templates(paths: Iterable[Path]) -> Iterable[Path]:
    for p in paths:
        p = p.resolve()
        if p.is_file() and p.suffix == ".lean":
            yield p
        elif p.is_dir():
            yield from sorted(p.rglob("*.lean"))


def _default_targets() -> list[Path]:
    if not GENERATED_ROOT.is_dir():
        return []
    return sorted(
        p for p in GENERATED_ROOT.rglob("*.lean")
        if "/Tasks/" in str(p)
    )


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument(
        "--preview",
        action="store_true",
        help=(
            "Write rewritten templates under Benchmark/GeneratedPreview/ "
            "instead of Benchmark/Generated/."
        ),
    )
    mode.add_argument(
        "--in-place",
        action="store_true",
        help="Overwrite Benchmark/Generated/**/Tasks/*.lean in place.",
    )
    mode.add_argument(
        "--patch",
        action="store_true",
        help="Emit a unified diff on stdout; do not write any files.",
    )
    ap.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help=(
            "Optional explicit files/dirs. Defaults to all Benchmark/Generated"
            "/**/Tasks/*.lean files."
        ),
    )
    args = ap.parse_args(argv)

    if not any([args.preview, args.in_place, args.patch]):
        args.preview = True  # safer default

    targets = list(iter_templates(args.paths)) if args.paths else _default_targets()
    if not targets:
        print("no task skeleton templates found", file=sys.stderr)
        return 1

    changed = 0
    for path in targets:
        template = parse_template(path)
        if template is None:
            print(f"skip (unparsed): {path.relative_to(ROOT)}", file=sys.stderr)
            continue
        new_text = render_skeleton(template)
        if new_text == template.raw:
            continue
        changed += 1
        rel = path.relative_to(ROOT)
        if args.patch:
            diff = difflib.unified_diff(
                template.raw.splitlines(keepends=True),
                new_text.splitlines(keepends=True),
                fromfile=f"a/{rel}",
                tofile=f"b/{rel}",
            )
            sys.stdout.writelines(diff)
            continue
        if args.preview:
            try:
                rel_to_gen = path.relative_to(GENERATED_ROOT)
            except ValueError:
                rel_to_gen = Path(path.name)
            out_path = PREVIEW_ROOT / rel_to_gen
        else:  # in-place
            out_path = path
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(new_text)
        print(f"wrote {out_path.relative_to(ROOT)}")
    if args.patch:
        return 0
    print(f"done: {changed} file(s) regenerated")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
