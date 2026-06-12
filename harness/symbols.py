"""Public-symbol extraction from Verity case files.

Single home for the parsing that turns a task's public implementation and
specification files into names a proof can mechanically use: contract
functions, storage-slot declarations, and spec helper defs. Used by the
fair harness's `show_task` summary and by scripts/grindset_ablation.py.
Nothing case-specific lives here — everything is derived from the files at
runtime.
"""

from __future__ import annotations

import re
from pathlib import Path

_NS_RE = re.compile(r"namespace\s+([A-Za-z0-9_.]+)")
_CONTRACT_RE = re.compile(r"verity_contract\s+([A-Za-z_][A-Za-z0-9_']*)")
_DEF_RE = re.compile(r"def\s+([A-Za-z_][A-Za-z0-9_']*)")
_FUNCTION_RE = re.compile(r"function\s+(?:internal\s+)?([A-Za-z_][A-Za-z0-9_']*)\s*(?:\(|$)")
_SLOT_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_']*)\s*:\s*.+:=\s*slot\s+\d+")
_FUNCTION_KEYWORDS = {"on", "nonreentrant", "internal"}
SPEC_NAME_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_'.]*_spec)\b")


def _code_lines(text: str):
    """Yield stripped non-comment lines (block and line comments removed)."""
    in_block = False
    for raw in text.splitlines():
        line = raw.strip()
        if in_block:
            if "-/" in line:
                in_block = False
                line = line.split("-/", 1)[1].strip()
            else:
                continue
        if line.startswith(("/-", "/--")):
            if "-/" not in line:
                in_block = True
            continue
        if line.startswith("--"):
            continue
        yield line


def spec_names(text: str) -> list[str]:
    """All `*_spec` identifiers mentioned in a Lean file."""
    return sorted(set(SPEC_NAME_RE.findall(text)))


def harvest_task_symbols(workspace: Path, task) -> list[str]:
    """Contract functions, storage-slot decls, and spec helper defs from the
    task's public files, spelled the way the task skeleton's namespace
    resolves them: contract members prefixed with the contract name,
    file-level defs bare."""
    names: list[str] = []
    for rel in list(task.implementation_files) + list(task.specification_files):
        path = workspace / rel
        if not path.is_file():
            continue
        contract = None
        for line in _code_lines(path.read_text(encoding="utf-8")):
            ns_match = _NS_RE.match(line)
            if ns_match:
                contract = ns_match.group(1).split(".")[-1]
            contract_match = _CONTRACT_RE.match(line)
            if contract_match:
                contract = contract_match.group(1)
            def_match = _DEF_RE.match(line)
            if def_match:
                names.append(def_match.group(1))
                continue
            if contract is None:
                continue
            fn_match = _FUNCTION_RE.match(line)
            if fn_match and fn_match.group(1) not in _FUNCTION_KEYWORDS:
                names.append(f"{contract}.{fn_match.group(1)}")
                continue
            slot_match = _SLOT_RE.match(line)
            if slot_match:
                names.append(f"{contract}.{slot_match.group(1)}")
    return list(dict.fromkeys(names))


def public_symbol_summary(text: str, *, limit: int = 1200) -> str:
    """Compact display summary of a public file's declarations, used by the
    fair harness's show_task tool result."""
    namespace = ""
    lines: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        ns_match = re.match(r"namespace\s+([A-Za-z0-9_'.]+)", line)
        if ns_match:
            namespace = ns_match.group(1)
            lines.append(line)
            continue
        if re.match(r"(def|theorem|lemma|abbrev|structure|inductive)\s+[A-Za-z_]", line):
            lines.append(line)
            continue
        if line.startswith("verity_contract "):
            lines.append(line)
            continue
        if re.match(r"function\s+[A-Za-z_][A-Za-z0-9_']*", line):
            lines.append(f"{namespace}.{line}" if namespace else line)
            continue
        if re.match(r"[A-Za-z_][A-Za-z0-9_']*\s*:\s*.+:=\s*slot\s+\d+", line):
            lines.append(f"storage {line}")
    return "\n".join(lines)[:limit]
