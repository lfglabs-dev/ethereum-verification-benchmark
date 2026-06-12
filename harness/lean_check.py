"""Lean check execution and output interpretation for the default harness.

Running `lake env lean` / `lake build`, compacting output, classifying
failures, extracting goal diagnostics, and per-failure hints. Extracted
from runners/lean_tools.py."""

from __future__ import annotations

import os
import re
import signal
import subprocess
from pathlib import Path

LEAN_CHECK_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_LEAN_CHECK_TIMEOUT_SECONDS", os.environ.get("GAZELLA_LEAN_CHECK_TIMEOUT_SECONDS", "240")))

LEAN_CHECK_MODE = os.environ.get("DEFAULT_HARNESS_CHECK_MODE", "file").strip().lower()  # "file" = lake env lean <editable>, "module" = lake build

def _run_lean_command(workspace: Path, command: list[str], timeout_seconds: int) -> tuple[int, str]:
    process: subprocess.Popen[str] | None = None
    try:
        process = subprocess.Popen(
            command,
            cwd=workspace,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        stdout, stderr = process.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired as exc:
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
        else:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        return 124, stdout + stderr + "\ntimeout"
    return process.returncode, (stdout + stderr).strip()

def _compact_lean_output(output: str, limit: int = 4000) -> str:
    lines = output.splitlines()
    error_blocks: list[str] = []
    for index, line in enumerate(lines):
        if "error:" in line.lower():
            error_blocks.extend(lines[index : min(len(lines), index + 8)])
    if error_blocks:
        filtered = [line for line in error_blocks if not line.startswith("trace: .>") and "LEAN_PATH=" not in line]
        return "\n".join(filtered)[-limit:]
    return output[-limit:]

def _first_meaningful_lean_error(output: str) -> str:
    compact = _compact_lean_output(output, limit=1600)
    for line in compact.splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("trace: .>") and "LEAN_PATH=" not in stripped:
            return stripped[:500]
    return compact.splitlines()[0][:500] if compact.splitlines() else ""

def _classify_lean_failure(output: str) -> str:
    lowered = output.lower()
    # Order matters: goal/identifier outputs routinely contain the substring
    # "expected" (e.g. "expected to have type"), so the parse-error pattern
    # must come after the more specific classes.
    if "unsolved goals" in lowered:
        return "lean_unsolved_goals"
    if "unknown identifier" in lowered or "unknown constant" in lowered or "unknown namespace" in lowered:
        return "lean_unknown_name"
    if ("unexpected token" in lowered or "expected '" in lowered) and "error:" in lowered:
        return "lean_parse_error"
    if "type mismatch" in lowered or "application type mismatch" in lowered:
        return "lean_type_error"
    if "timeout" in lowered:
        return "lean_timeout"
    if "error:" in lowered:
        return "lean_error"
    return "lean_check_failed"

def _extract_goal_blocks(output: str, *, limit: int = 2400) -> list[str]:
    blocks: list[str] = []
    lines = output.splitlines()
    for index, line in enumerate(lines):
        if "⊢" not in line and not line.strip().startswith("⊢"):
            continue
        start = index
        while start > 0:
            previous = lines[start - 1]
            if not previous.strip():
                break
            if "error:" in previous.lower():
                break
            start -= 1
        end = index + 1
        while end < len(lines):
            current = lines[end]
            if "error:" in current.lower() and end > index + 1:
                break
            if not current.strip() and end > index + 2:
                break
            end += 1
        block = "\n".join(lines[start:end]).strip()
        if block and block not in blocks:
            blocks.append(block[-limit:])
    return blocks[:3]

def _split_goal_context(goal: str) -> dict[str, object]:
    hypotheses: list[str] = []
    target_lines: list[str] = []
    in_target = False
    for raw in goal.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("⊢") or "⊢" in line:
            in_target = True
            target_lines.append(line.split("⊢", 1)[1].strip() if "⊢" in line else line.lstrip("⊢").strip())
            continue
        if in_target:
            target_lines.append(line)
        elif " : " in line:
            hypotheses.append(line)
    return {"hypotheses": hypotheses[:30], "target": "\n".join(target_lines)[:1800]}

LEAN_KEYWORDS = {
    "by", "let", "fun", "forall", "if", "then", "else", "match", "with", "true", "false",
    "Type", "Prop", "Sort", "Nat", "Int", "Bool", "String", "Unit", "Fin", "Option", "List",
}

def _constants_from_text(text: str) -> list[str]:
    names: set[str] = set()
    for token in re.findall(r"\b[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)*\b", text):
        if token in LEAN_KEYWORDS or token.startswith("h") and len(token) <= 4:
            continue
        if token[0].isupper() or "." in token or token in {"getStorage", "setStorage", "getMapping", "setMapping", "require", "Contract", "ContractResult", "storage", "storageMap"}:
            names.add(token)
    return sorted(names)[:60]

def _goal_diagnostics(output: str) -> dict[str, object]:
    compact = _compact_lean_output(output)
    goals = _extract_goal_blocks(compact)
    primary = _split_goal_context(goals[0]) if goals else {"hypotheses": [], "target": ""}
    target_text = str(primary.get("target") or "")
    return {
        "output": compact,
        "goals": goals,
        "local_hypotheses": primary.get("hypotheses", []),
        "target": target_text,
        "constants": _constants_from_text("\n".join(goals) if goals else compact),
        "first_error": _first_meaningful_lean_error(compact),
        "failure_kind": _classify_lean_failure(compact) if compact else None,
    }

def _proof_result_diagnostics(output: str, *, baseline_goal: str = "") -> dict[str, object]:
    diagnostics = _goal_diagnostics(output)
    target = str(diagnostics.get("target") or "")
    return {
        "changed_goal": bool(target and target != baseline_goal),
        "new_goal": target,
        "first_error": diagnostics.get("first_error"),
        "failure_kind": diagnostics.get("failure_kind"),
        "local_hypotheses": diagnostics.get("local_hypotheses", []),
        "constants": diagnostics.get("constants", []),
    }

FAILURE_HINTS: dict[str, str] = {
    "lean_unsolved_goals": (
        "Unsolved goals: inspect the remaining goal in this result. Typical Verity closers: unfold the *_spec and the contract function, "
        "simp with the contract's storage field names (ContractName.field), getStorage/setStorage/getMapping/setMapping, "
        "Verity.require/Verity.bind/Bind.bind/Verity.pure/Pure.pure/Contract.run/ContractResult.snd, and the boolean guard hypotheses. "
        "If the goal contains an `if`/`ite`/`match` on a condition (including boolean `==` tests like (add x 1 == k)), "
        "case-split with by_cases on that exact condition and include the resulting hypothesis in the simp set of each branch. "
        "Prefer one combined `simp [contract fn, storage fields, guard hypotheses, monadic plumbing]` per branch over chained simp only + simp."
    ),
    "lean_unknown_name": (
        "Unknown identifier: use only names visible in the provided files; verify exact spelling with search_declarations before reusing it. "
        "Do not invent Verity.Storage.* helpers, storage_set lemmas, or ContractState methods."
    ),
    "lean_parse_error": (
        "Syntax error: check tactic-block indentation (bullets `·` need consistent two-space nesting) and that brackets/parentheses balance. "
        "You may submit the complete file (imports + namespace + theorem) instead of a bare tactic body."
    ),
    "lean_type_error": (
        "Type mismatch: compare both sides' types in the error; Uint256 comparisons often need `.val` forms or `Verity.Core.Uint256` lemmas. "
        "Use simp lemmas to normalize before exact/rw."
    ),
    "lean_timeout": (
        "Lean timed out: avoid broad recursive simp (never put ContractResult.snd in a bare simp list with the whole contract); "
        "prefer `simp only` with an explicit lemma list, or unfold the spec and case-split before simplifying."
    ),
    "lean_error": (
        "If 'failed to unfold': that name is not reducible by unfold; use simp [name] instead, or unfold only *_spec definitions and the concrete contract function. "
        "If 'maximum recursion depth': shrink the simp set and split branches with by_cases."
    ),
}

def _hint_for_failure(failure_kind: object, output: str) -> str | None:
    hint = FAILURE_HINTS.get(str(failure_kind)) if failure_kind else None
    if "maximum recursion depth" in output:
        extra = "Avoid broad recursive simp; use simp only with explicit lemmas and case-split contract branches with by_cases."
        hint = f"{hint} {extra}" if hint else extra
    if "simp made no progress" in output:
        extra = (
            "A simp step made no progress, which Lean treats as an error: wrap optional normalization steps in `try` "
            "(e.g. `try simp only [grind_norm] at *`) or delete the redundant simp line, then resubmit."
        )
        hint = f"{hint} {extra}" if hint else extra
    return hint
