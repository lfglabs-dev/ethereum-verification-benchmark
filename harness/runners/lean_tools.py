from __future__ import annotations

import argparse
import re
import json
import os
import signal
import shutil
import socket
import subprocess
import time
import urllib.request
import urllib.error
from urllib.parse import urlparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from ..manifests import filter_group_to_task, load_group
    from ..paths import RESULTS_DIR, ROOT
    from ..reports import write_run_report
    from ..verifier import verify_group
    from ..workspace_builder import agent_group_to_json, assert_workspace_isolated, build_group_workspace
except ImportError:
    from manifests import filter_group_to_task, load_group
    from paths import RESULTS_DIR, ROOT
    from reports import write_run_report
    from verifier import verify_group
    from workspace_builder import agent_group_to_json, assert_workspace_isolated, build_group_workspace

try:
    from ..transport import (
        ChatCompletionError, DEFAULT_BASE_URL, DEFAULT_MODEL, DEFAULT_PROVIDER, HTTP_USER_AGENT,
        _active_provider, _api_key, _harness_env, _local_no_auth_endpoint, _logged_response_message,
        _response_text, _append_jsonl, chat_completion, endpoint_smoke,
    )
    from ..lean_check import (
        FAILURE_HINTS, LEAN_CHECK_MODE, LEAN_CHECK_TIMEOUT_SECONDS, _classify_lean_failure,
        _compact_lean_output, _constants_from_text, _extract_goal_blocks, _first_meaningful_lean_error,
        _goal_diagnostics, _hint_for_failure, _proof_result_diagnostics, _run_lean_command,
        _split_goal_context,
    )
    from ..proof_patch import (
        FORBIDDEN_PROOF_RE, _candidate_from_response, _contains_forbidden_proof_token, _decl_basename,
        _extract_lean_file, _indent_proof_body, _looks_like_full_file, _patch_proof_body,
        _strip_thinking, _theorem_statement,
    )
except ImportError:
    from transport import (
        ChatCompletionError, DEFAULT_BASE_URL, DEFAULT_MODEL, DEFAULT_PROVIDER, HTTP_USER_AGENT,
        _active_provider, _api_key, _harness_env, _local_no_auth_endpoint, _logged_response_message,
        _response_text, _append_jsonl, chat_completion, endpoint_smoke,
    )
    from lean_check import (
        FAILURE_HINTS, LEAN_CHECK_MODE, LEAN_CHECK_TIMEOUT_SECONDS, _classify_lean_failure,
        _compact_lean_output, _constants_from_text, _extract_goal_blocks, _first_meaningful_lean_error,
        _goal_diagnostics, _hint_for_failure, _proof_result_diagnostics, _run_lean_command,
        _split_goal_context,
    )
    from proof_patch import (
        FORBIDDEN_PROOF_RE, _candidate_from_response, _contains_forbidden_proof_token, _decl_basename,
        _extract_lean_file, _indent_proof_body, _looks_like_full_file, _patch_proof_body,
        _strip_thinking, _theorem_statement,
    )


HARNESS_ID = "default"
RUN_SLUG = "default"
MAX_FILE_CHARS = int(os.environ.get("DEFAULT_HARNESS_MAX_FILE_CHARS", os.environ.get("GAZELLA_MAX_FILE_CHARS", "6000")))
PROMPT_CONTEXT_CHARS = int(os.environ.get("DEFAULT_HARNESS_PROMPT_CONTEXT_CHARS", os.environ.get("GAZELLA_PROMPT_CONTEXT_CHARS", "8000")))
DEFAULT_MAX_TOOL_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_TOOL_CALLS", "24"))
DEFAULT_NATIVE_TOOLS = os.environ.get("DEFAULT_HARNESS_NATIVE_TOOLS", "1").lower() not in {"0", "false", "no"}
DEFAULT_TOOL_RESULT_CHARS = int(os.environ.get("DEFAULT_HARNESS_TOOL_RESULT_CHARS", "6000"))
DEFAULT_TASK_SUMMARY_CHARS = int(os.environ.get("DEFAULT_HARNESS_TASK_SUMMARY_CHARS", "8000"))
DEFAULT_MAX_NON_PROOF_TOOL_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_NON_PROOF_TOOL_CALLS", "24"))
DEFAULT_MAX_SANDBOX_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_SANDBOX_CALLS", "16"))
DEFAULT_TOKEN_BUDGET = int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0"))  # 0 = unlimited; counts completion tokens per task
STUCK_NUDGE = os.environ.get("DEFAULT_HARNESS_STUCK_NUDGE", "1").lower() not in {"0", "false", "no"}


def _public_symbol_summary(text: str, *, limit: int = 1200) -> str:
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


def _read_workspace_file(workspace: Path, rel: str) -> str:
    text = (workspace / rel).read_text(encoding="utf-8")
    if len(text) <= MAX_FILE_CHARS:
        return text
    return text[:MAX_FILE_CHARS] + "\n/- file truncated for prompt -/\n"


def _run_lean_module(
    workspace: Path,
    module: str,
    timeout_seconds: int | None = None,
    *,
    file_rel: str | None = None,
) -> tuple[int, str]:
    if timeout_seconds is None:
        timeout_seconds = LEAN_CHECK_TIMEOUT_SECONDS
    if file_rel and LEAN_CHECK_MODE == "file":
        code, output = _run_lean_command(workspace, ["lake", "env", "lean", file_rel], timeout_seconds)
        # Fall back to a module build when the file check fails for build-graph
        # reasons (stale or missing dependency oleans), not proof reasons.
        lowered = output.lower()
        dependency_error = re.search(r"unknown module prefix|unknown package|object file .* does not exist|no such file or directory|bad import", lowered)
        if code not in (0, 124) and dependency_error:
            return _run_lean_command(workspace, ["lake", "build", module], timeout_seconds)
        return code, output
    return _run_lean_command(workspace, ["lake", "build", module], timeout_seconds)


def _run_tactic_snapshot(
    *,
    original: str,
    proof_path: Path,
    workspace: Path,
    target_module: str,
    tactic: str,
) -> dict[str, object]:
    previous = proof_path.read_text(encoding="utf-8") if proof_path.is_file() else original
    candidate = _candidate_from_response(original, tactic + "\nall_goals exact ?_", None)
    if _contains_forbidden_proof_token(tactic):
        return {"ok": False, "error": "sandbox tactic contains sorry, admit, axiom, or a placeholder"}
    try:
        proof_path.write_text(candidate, encoding="utf-8")
        code, output = _run_lean_module(workspace, target_module, file_rel=_workspace_rel(workspace, proof_path))
    finally:
        proof_path.write_text(previous, encoding="utf-8")
    diagnostics = _goal_diagnostics(output)
    return {
        "ok": True,
        "exit_code": code,
        "changed_goal": bool(diagnostics.get("goals")),
        "diagnostics": diagnostics,
    }


def _workspace_rel(workspace: Path, path: Path) -> str | None:
    try:
        return path.relative_to(workspace).as_posix()
    except ValueError:
        return None


def _run_lean_module_with_proof_content(
    *,
    proof_path: Path,
    workspace: Path,
    target_module: str,
    content: str,
) -> tuple[int, str]:
    previous = proof_path.read_text(encoding="utf-8") if proof_path.is_file() else content
    try:
        proof_path.write_text(content, encoding="utf-8")
        return _run_lean_module(workspace, target_module, file_rel=_workspace_rel(workspace, proof_path))
    finally:
        proof_path.write_text(previous, encoding="utf-8")


def _failure_taxonomy(status: str, attempts: list[dict[str, object]], *, tool_calls: int = 0, no_tool_responses: int = 0) -> str:
    if status in {"missing_credentials", "request_timeout", "request_failed"}:
        return "provider_or_context_failure"
    if status == "failed_no_tool_calls" or (tool_calls == 0 and not attempts):
        return "no_tool_calls"
    if status == "failed_no_attempt" and tool_calls > 0:
        return "context_loop"
    outputs = "\n".join(str(attempt.get("output", "")) for attempt in attempts)
    if attempts:
        lean_kind = _classify_lean_failure(outputs)
        if lean_kind == "lean_parse_error":
            return "proof_parse_failures"
        if lean_kind == "lean_unknown_name":
            return "proof_unknown_names"
        if lean_kind == "lean_unsolved_goals":
            return "proof_unsolved_goals"
        if lean_kind == "lean_timeout":
            return "timeout_after_progress"
        return "proof_lean_failures"
    if no_tool_responses:
        return "context_loop"
    return "unknown_failure"


def _stuck_signature(first_error: object) -> str:
    text = re.sub(r"\d+", "#", str(first_error or "")).strip()
    return text[:200]


FAIR_TOOLS: list[dict[str, Any]] = [
    {
        "type": "function",
        "function": {
            "name": "show_task",
            "description": "Show the benchmark task metadata and allowed files.",
            "parameters": {"type": "object", "properties": {}, "additionalProperties": False},
        },
    },
    {
        "type": "function",
        "function": {
            "name": "read_file",
            "description": "Read a public workspace file by relative path.",
            "parameters": {
                "type": "object",
                "properties": {"path": {"type": "string"}},
                "required": ["path"],
                "additionalProperties": False,
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "show_goal",
            "description": "Run Lean on the current editable proof file and return compact goal/error output.",
            "parameters": {"type": "object", "properties": {}, "additionalProperties": False},
        },
    },
    {
        "type": "function",
        "function": {
            "name": "check_proof",
            "description": "Replace the editable theorem placeholder with a tactic body under := by and check the target Lean module.",
            "parameters": {
                "type": "object",
                "properties": {"proof": {"type": "string"}},
                "required": ["proof"],
                "additionalProperties": False,
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "try_tactics",
            "description": "Check one or more tactic bodies under := by and return structured diagnostics. This counts as a proof attempt.",
            "parameters": {
                "type": "object",
                "properties": {
                    "tactics": {
                        "type": "array",
                        "items": {"type": "string"},
                        "minItems": 1,
                        "maxItems": 5,
                    }
                },
                "required": ["tactics"],
                "additionalProperties": False,
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "tactic_sandbox",
            "description": "Run one short exploratory tactic prefix under := by and return the resulting goal/error. This does not count as a proof attempt and is capped.",
            "parameters": {
                "type": "object",
                "properties": {"prefix": {"type": "string"}},
                "required": ["prefix"],
                "additionalProperties": False,
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "search_declarations",
            "description": "Search public workspace and dependency Lean files for declarations or text.",
            "parameters": {
                "type": "object",
                "properties": {
                    "query": {"type": "string"},
                    "limit": {"type": "integer", "minimum": 1, "maximum": 50},
                },
                "required": ["query"],
                "additionalProperties": False,
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "definition_outline",
            "description": "Return matching public Lean declarations with signatures, source paths, small def body previews, and nearby related simp lemmas.",
            "parameters": {
                "type": "object",
                "properties": {
                    "query": {"type": "string"},
                    "limit": {"type": "integer", "minimum": 1, "maximum": 25},
                },
                "required": ["query"],
                "additionalProperties": False,
            },
        },
    },
]


def _safe_workspace_path(workspace: Path, rel: str) -> Path:
    if rel.startswith("/") or ".." in Path(rel).parts:
        raise ValueError("path must be a relative workspace path")
    path = (workspace / rel).resolve()
    root = workspace.resolve()
    if path != root and root not in path.parents:
        for dependency_root in _fair_dependency_roots(workspace):
            if path == dependency_root or dependency_root in path.parents:
                return path
        raise ValueError("path escapes workspace")
    return path


def _task_public_view(task: dict[str, object]) -> dict[str, object]:
    return {
        "task_ref": task.get("task_ref"),
        "task_id": task.get("task_id"),
        "target_module": task.get("target_module"),
        "editable_files": task.get("editable_files"),
        "specification_files": task.get("specification_files"),
        "implementation_files": task.get("implementation_files"),
        "manifest_path": task.get("manifest_path"),
    }


def _fair_tool_can_read(rel: str) -> bool:
    parts = Path(rel).parts
    if rel == ".env" or ".env" in parts:
        return False
    if rel.startswith("Benchmark/GeneratedPreview/") or "/GeneratedPreview/" in rel:
        return False
    if rel.endswith("Proofs.lean") or "/Proofs/" in rel:
        return False
    return True


def _fair_dependency_roots(workspace: Path) -> list[Path]:
    roots: list[Path] = []
    lake = workspace / ".lake"
    try:
        if lake.exists():
            roots.append(lake.resolve())
    except OSError:
        pass
    root_lake = ROOT / ".lake"
    try:
        if root_lake.exists():
            resolved = root_lake.resolve()
            if resolved not in roots:
                roots.append(resolved)
    except OSError:
        pass
    return roots


def _public_lean_files(workspace: Path) -> list[tuple[str, Path]]:
    seen: set[Path] = set()
    files: list[tuple[str, Path]] = []

    for path in workspace.rglob("*.lean"):
        try:
            resolved = path.resolve()
            rel = path.relative_to(workspace).as_posix()
        except (OSError, ValueError):
            continue
        if resolved in seen or not _fair_tool_can_read(rel):
            continue
        seen.add(resolved)
        files.append((rel, path))

    for dependency_root in _fair_dependency_roots(workspace):
        for path in dependency_root.rglob("*.lean"):
            try:
                resolved = path.resolve()
                rel = ".lake/" + path.relative_to(dependency_root).as_posix()
            except (OSError, ValueError):
                continue
            if resolved in seen or not _fair_tool_can_read(rel):
                continue
            seen.add(resolved)
            files.append((rel, path))

    return sorted(files, key=lambda item: item[0])


def _search_declarations(workspace: Path, query: str, *, limit: int = 20) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    pattern = query.lower()
    for rel, path in _public_lean_files(workspace):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for lineno, line in enumerate(lines, start=1):
            stripped = line.strip()
            if pattern in stripped.lower():
                results.append({"path": rel, "line": lineno, "text": stripped[:240]})
                if len(results) >= limit:
                    return results
    return results


DECL_RE = re.compile(r"^\s*(?:@[^\n]+)?\s*(def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def _declaration_signature(lines: list[str], start: int) -> str:
    collected: list[str] = []
    paren_balance = 0
    bracket_balance = 0
    for raw in lines[start : min(len(lines), start + 12)]:
        stripped = raw.strip()
        if not stripped:
            break
        collected.append(stripped)
        paren_balance += stripped.count("(") - stripped.count(")")
        bracket_balance += stripped.count("[") - stripped.count("]")
        joined = " ".join(collected)
        if ":=" in joined or " where" in joined or (":" in joined and paren_balance <= 0 and bracket_balance <= 0):
            break
    signature = " ".join(collected)
    if ":=" in signature:
        signature = signature.split(":=", 1)[0].rstrip()
    return signature[:700]


def _declaration_body_preview(lines: list[str], start: int, *, limit: int = 700) -> str:
    preview: list[str] = []
    for raw in lines[start : min(len(lines), start + 18)]:
        if raw.startswith(("theorem ", "lemma ")) and preview:
            break
        preview.append(raw.rstrip())
    text = "\n".join(preview).strip()
    return text[:limit]


def _related_simp_lemmas(lines: list[str], decl_start: int, query: str) -> list[str]:
    related: list[str] = []
    q = query.lower()
    start = max(0, decl_start - 45)
    end = min(len(lines), decl_start + 46)
    for index in range(start, end):
        line = lines[index].strip()
        if not line:
            continue
        lower = line.lower()
        if "@[simp" not in lower and q not in lower:
            continue
        match = DECL_RE.match(line)
        if match and match.group(1) in {"theorem", "lemma", "def"}:
            related.append(_declaration_signature(lines, index))
        elif "@[simp" in lower and index + 1 < len(lines):
            next_match = DECL_RE.match(lines[index + 1].strip())
            if next_match:
                related.append(_declaration_signature(lines, index + 1))
        if len(related) >= 6:
            break
    return related


def _definition_outline(workspace: Path, query: str, *, limit: int = 12) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    pattern = query.lower()
    for rel, path in _public_lean_files(workspace):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        namespace_stack: list[str] = []
        for lineno, raw in enumerate(lines, start=1):
            stripped = raw.strip()
            ns_match = re.match(r"namespace\s+([A-Za-z0-9_'.]+)", stripped)
            if ns_match:
                namespace_stack.append(ns_match.group(1))
                continue
            if stripped == "end" or stripped.startswith("end "):
                if namespace_stack:
                    namespace_stack.pop()
                continue
            match = DECL_RE.match(stripped)
            if not match:
                continue
            kind, name = match.groups()
            namespace = ".".join(namespace_stack)
            qualified = name if "." in name or not namespace else f"{namespace}.{name}"
            signature = _declaration_signature(lines, lineno - 1)
            haystack = f"{qualified}\n{signature}".lower()
            if pattern not in haystack:
                continue
            item: dict[str, object] = {
                "name": qualified,
                "kind": kind,
                "namespace": namespace,
                "path": rel,
                "line": lineno,
                "signature": signature,
                "related_simp_lemmas": _related_simp_lemmas(lines, lineno - 1, query),
            }
            if kind in {"def", "abbrev"}:
                item["body_preview"] = _declaration_body_preview(lines, lineno - 1)
            results.append(item)
            if len(results) >= limit:
                return results
    return results


def _write_attempt_artifact(
    attempts_dir: Path,
    task: dict[str, object],
    label: str,
    candidate: str,
) -> Path:
    safe_task = str(task.get("task_id") or task.get("task_ref") or "task").replace("/", "__")
    safe_label = re.sub(r"[^A-Za-z0-9_.-]+", "-", label).strip("-") or "attempt"
    candidate_path = attempts_dir / f"{safe_task}-{safe_label}.lean"
    candidate_path.parent.mkdir(parents=True, exist_ok=True)
    candidate_path.write_text(candidate, encoding="utf-8")
    return candidate_path


def _append_jsonl(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")


def _shrink_strings(value: object, limit: int) -> object:
    if isinstance(value, str) and len(value) > limit:
        return value[:limit] + f"...[truncated {len(value) - limit} chars]"
    if isinstance(value, dict):
        return {key: _shrink_strings(item, limit) for key, item in value.items()}
    if isinstance(value, list):
        return [_shrink_strings(item, limit) for item in value]
    return value


def _tool_result_content(result: dict[str, object]) -> str:
    serialized = json.dumps(result, sort_keys=True)
    if len(serialized) <= DEFAULT_TOOL_RESULT_CHARS:
        return serialized
    # First shrink individual long strings (usually raw Lean output) so the
    # structured fields (first_error, hint, stuck) survive intact.
    for limit in (2000, 800, 300):
        shrunk = json.dumps(_shrink_strings(result, limit), sort_keys=True)
        if len(shrunk) <= DEFAULT_TOOL_RESULT_CHARS:
            return shrunk
    serialized = shrunk
    head_budget = max(0, DEFAULT_TOOL_RESULT_CHARS - 160)
    while True:
        payload = {
            "original_chars": len(serialized),
            "head": serialized[:head_budget] if head_budget else "",
            "truncated": True,
        }
        compact = json.dumps(payload, sort_keys=True)
        if len(compact) <= DEFAULT_TOOL_RESULT_CHARS or head_budget == 0:
            return compact
        head_budget = max(0, head_budget - (len(compact) - DEFAULT_TOOL_RESULT_CHARS))


def _proof_attempt_count(attempts: list[dict[str, object]]) -> int:
    return sum(1 for attempt in attempts if str(attempt.get("attempt", "")).startswith("tool:"))


def _task_summary_with_live_editable(summary: str, *, task: dict[str, object], workspace: Path) -> str:
    editable_files = task.get("editable_files")
    if not isinstance(editable_files, list) or len(editable_files) != 1:
        return summary
    rel = editable_files[0]
    if not isinstance(rel, str):
        return summary
    try:
        path = _safe_workspace_path(workspace, rel)
        content = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError, ValueError):
        return summary
    block = f"### Current Editable File\n\n`{rel}`\n\n```lean\n{content.rstrip()}\n```"
    pattern = (
        r"### Current Editable File\n\n"
        rf"`{re.escape(rel)}`\n\n"
        r"```lean\n.*?\n```"
    )
    refreshed, count = re.subn(pattern, block, summary, count=1, flags=re.S)
    if count:
        return refreshed
    return summary.rstrip() + "\n\n" + block + "\n"


def _execute_fair_tool(
    name: str,
    args: dict[str, object],
    *,
    task: dict[str, object],
    workspace: Path,
    original: str,
    proof_path: Path,
    target_module: str,
    attempts_dir: Path,
    attempts: list[dict[str, object]],
    sandbox_state: dict[str, int] | None = None,
) -> dict[str, object]:
    if name == "show_task":
        summary_path = workspace / "harness" / "TASK_SUMMARY.md"
        summary = summary_path.read_text(encoding="utf-8") if summary_path.is_file() else ""
        summary = _task_summary_with_live_editable(summary, task=task, workspace=workspace)
        patterns_path = workspace / "harness" / "PROOF_PATTERNS.md"
        patterns = patterns_path.read_text(encoding="utf-8")[:4000] if patterns_path.is_file() else ""
        return {
            "ok": True,
            "task": _task_public_view(task),
            "task_summary": summary[-DEFAULT_TASK_SUMMARY_CHARS:],
            "proof_patterns": patterns,
        }
    if name == "read_file":
        rel = args.get("path")
        if not isinstance(rel, str):
            return {"ok": False, "error": "path must be a string"}
        try:
            path = _safe_workspace_path(workspace, rel)
        except ValueError as exc:
            return {"ok": False, "error": str(exc)}
        if not _fair_tool_can_read(rel):
            return {"ok": False, "error": "fair mode does not expose hidden proof, GeneratedPreview, or .env files"}
        if not path.is_file():
            return {"ok": False, "error": "file not found"}
        try:
            content = _read_workspace_file(workspace, rel)
        except UnicodeDecodeError:
            return {"ok": False, "error": "file is not valid utf-8 text"}
        except OSError as exc:
            return {"ok": False, "error": str(exc)}
        return {"ok": True, "path": rel, "content": content}
    if name == "show_goal":
        try:
            current = proof_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            current = original
        code, output = _run_lean_module(workspace, target_module, file_rel=_workspace_rel(workspace, proof_path))
        normalized = _run_tactic_snapshot(
            original=current,
            proof_path=proof_path,
            workspace=workspace,
            target_module=target_module,
            tactic="dsimp",
        )
        return {
            "ok": True,
            "exit_code": code,
            "theorem_statement": _theorem_statement(current, task.get("theorem_name")),
            "diagnostics": _goal_diagnostics(output),
            "normalized_once": normalized.get("diagnostics") if normalized.get("ok") else normalized,
        }
    if name == "tactic_sandbox":
        prefix = args.get("prefix")
        if not isinstance(prefix, str) or not prefix.strip():
            return {"ok": False, "error": "prefix must be a non-empty string"}
        state = sandbox_state if sandbox_state is not None else {}
        used = state.get("count", 0)
        limit = state.get("limit", DEFAULT_MAX_SANDBOX_CALLS)
        if used >= limit:
            return {"ok": False, "error": "tactic_sandbox_budget_exceeded", "max_calls": limit}
        state["count"] = used + 1
        try:
            current = proof_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            current = original
        return _run_tactic_snapshot(
            original=current,
            proof_path=proof_path,
            workspace=workspace,
            target_module=target_module,
            tactic=prefix,
        ) | {"sandbox_calls_used": state["count"], "sandbox_calls_max": limit}
    if name in {"check_proof", "try_tactics"}:
        baseline_code, baseline_output = _run_lean_module_with_proof_content(
            proof_path=proof_path,
            workspace=workspace,
            target_module=target_module,
            content=original,
        )
        baseline_diag = _goal_diagnostics(baseline_output)
        baseline_goal = str(baseline_diag.get("target") or "")
        proofs: list[tuple[str, str]] = []
        if name == "check_proof":
            proof = args.get("proof")
            if not isinstance(proof, str):
                return {"ok": False, "error": "proof must be a string"}
            proofs.append(("check_proof", proof))
        else:
            raw_tactics = args.get("tactics")
            if not isinstance(raw_tactics, list) or not raw_tactics:
                return {"ok": False, "error": "tactics must be a non-empty array"}
            for index, tactic in enumerate(raw_tactics[:5], start=1):
                if isinstance(tactic, str):
                    proofs.append((f"try_tactics-{index}", tactic))
            if not proofs:
                return {"ok": False, "error": "tactics must contain at least one string"}
        results: list[dict[str, object]] = []
        original_statement = " ".join(_theorem_statement(original, task.get("theorem_name")).split())
        for label, proof in proofs:
            candidate = _candidate_from_response(original, proof, task.get("theorem_name"))
            candidate_statement = " ".join(_theorem_statement(candidate, task.get("theorem_name")).split())
            # Fail closed when the skeleton statement cannot be extracted:
            # proof-body patches keep the statement byte-identical by
            # construction, so only whole-file submissions can change it.
            statement_guard_failed = (
                candidate_statement != original_statement
                if original_statement
                else _looks_like_full_file(_extract_lean_file(proof))
            )
            if statement_guard_failed:
                attempt = {
                    "attempt": f"tool:{name}",
                    "status": "rejected_statement_mismatch",
                    "exit_code": None,
                    "candidate_path": None,
                    "output": "the submitted file changes or drops the target theorem statement; keep the theorem signature byte-identical and only change the proof after := by",
                    "failure_kind": "statement_mismatch",
                    "diagnostics": {
                        "changed_goal": False,
                        "new_goal": baseline_goal,
                        "first_error": "theorem statement mismatch",
                        "failure_kind": "statement_mismatch",
                    },
                    "duration_seconds": 0,
                    "response_usage": None,
                }
                attempts.append(attempt)
                results.append(attempt)
                continue
            if _contains_forbidden_proof_token(candidate):
                candidate_path = _write_attempt_artifact(attempts_dir, task, f"fair-{len(attempts) + 1}-{label}", candidate)
                attempt = {
                    "attempt": f"tool:{name}",
                    "status": "rejected_forbidden_placeholder",
                    "exit_code": None,
                    "candidate_path": str(candidate_path),
                    "output": "proof contains sorry, admit, axiom, or an unsolved placeholder",
                    "failure_kind": "forbidden_placeholder",
                    "diagnostics": {
                        "changed_goal": False,
                        "new_goal": baseline_goal,
                        "first_error": "proof contains sorry, admit, axiom, or an unsolved placeholder",
                        "failure_kind": "forbidden_placeholder",
                    },
                    "duration_seconds": 0,
                    "response_usage": None,
                }
                attempts.append(attempt)
                results.append(attempt)
                continue
            proof_path.write_text(candidate, encoding="utf-8")
            candidate_path = _write_attempt_artifact(attempts_dir, task, f"fair-{len(attempts) + 1}-{label}", candidate)
            lean_start = time.time()
            code, output = _run_lean_module(workspace, target_module, file_rel=_workspace_rel(workspace, proof_path))
            failure_kind = None if code == 0 else _classify_lean_failure(output)
            diagnostics = _proof_result_diagnostics(output, baseline_goal=baseline_goal)
            attempt = {
                "attempt": f"tool:{name}",
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": str(candidate_path),
                "output": _compact_lean_output(output),
                "failure_kind": failure_kind,
                "diagnostics": diagnostics,
                "duration_seconds": round(time.time() - lean_start, 3),
                "response_usage": None,
            }
            if code != 0:
                hint = _hint_for_failure(failure_kind, output)
                if hint:
                    attempt["hint"] = hint
                if STUCK_NUDGE:
                    signature = _stuck_signature(diagnostics.get("first_error"))
                    previous_signatures = [
                        _stuck_signature(prior.get("diagnostics", {}).get("first_error"))
                        for prior in attempts
                        if isinstance(prior, dict) and prior.get("status") == "lean_failed"
                    ]
                    if signature and signature in previous_signatures:
                        attempt["stuck"] = (
                            "Same error as a previous attempt - do not retry a minor variation. "
                            "Change strategy: use show_goal or tactic_sandbox to inspect the goal state, "
                            "case-split differently, or build the proof stepwise with have/calc."
                        )
            attempts.append(attempt)
            results.append(attempt)
            if code == 0:
                return {"ok": True, "passed": True, "results": results}
        return {"ok": True, "passed": False, "results": results}
    if name == "search_declarations":
        query = args.get("query")
        if not isinstance(query, str) or not query:
            return {"ok": False, "error": "query must be a non-empty string"}
        limit = args.get("limit")
        return {"ok": True, "results": _search_declarations(workspace, query, limit=int(limit) if isinstance(limit, int) else 20)}
    if name == "definition_outline":
        query = args.get("query")
        if not isinstance(query, str) or not query:
            return {"ok": False, "error": "query must be a non-empty string"}
        limit = args.get("limit")
        return {"ok": True, "results": _definition_outline(workspace, query, limit=int(limit) if isinstance(limit, int) else 12)}
    return {"ok": False, "error": f"unknown tool: {name}"}


def _json_payload_from_text(text: str) -> object | None:
    stripped = _strip_thinking(text).strip()
    fenced = re.search(r"```(?:json)?\s*(.*?)```", stripped, flags=re.DOTALL | re.IGNORECASE)
    if fenced:
        stripped = fenced.group(1).strip()
    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        return None


def _normalise_text_tool_call(raw: object, index: int) -> dict[str, object] | None:
    if not isinstance(raw, dict):
        return None
    function = raw.get("function")
    if isinstance(function, dict):
        name = function.get("name")
        arguments = function.get("arguments", {})
    else:
        name = raw.get("name") or raw.get("tool")
        arguments = raw.get("arguments", raw.get("args", {}))
    if not isinstance(name, str):
        return None
    return {
        "id": raw.get("id") if isinstance(raw.get("id"), str) else f"text-call-{index}",
        "function": {
            "name": name,
            "arguments": arguments,
        },
        "text_protocol": True,
    }


def _tool_calls_from_text(text: str) -> list[dict[str, object]]:
    payload = _json_payload_from_text(text)
    if isinstance(payload, dict):
        raw_calls = payload.get("tool_calls", payload.get("calls"))
        if raw_calls is None and ("tool" in payload or "name" in payload or "function" in payload):
            raw_calls = [payload]
    elif isinstance(payload, list):
        raw_calls = payload
    else:
        raw_calls = None
    if not isinstance(raw_calls, list):
        return []
    calls: list[dict[str, object]] = []
    for index, raw in enumerate(raw_calls, start=1):
        call = _normalise_text_tool_call(raw, index)
        if call is not None:
            calls.append(call)
    return calls


def _attempt_task_fair(
    task: dict[str, object],
    workspace: Path,
    *,
    base_url: str,
    max_attempts: int,
    max_tool_calls: int,
    attempts_dir: Path,
    tool_log_path: Path,
    conversation_log_path: Path,
) -> dict[str, object]:
    editable_files = task.get("editable_files")
    target_module = task.get("target_module")
    if not isinstance(editable_files, list) or len(editable_files) != 1 or not isinstance(target_module, str):
        return {"task_ref": task.get("task_ref"), "status": "unsupported_task_shape"}
    editable = str(editable_files[0])
    proof_path = workspace / editable
    original = proof_path.read_text(encoding="utf-8")
    attempts: list[dict[str, object]] = []

    if DEFAULT_NATIVE_TOOLS:
        system_prompt = (
            "You are an agent solving one public Lean benchmark task through tools only. "
            "Call show_task first; it returns the shared TASK_SUMMARY.md and a proof_patterns guide with the Verity-specific "
            "simp/unfold recipe (contract function + storage field names + getStorage/setStorage/Verity.require/Verity.bind/Bind.bind/"
            "Verity.pure/Pure.pure/Contract.run/ContractResult.snd) that closes most goals; follow it before inventing your own approach. "
            "Then inspect files with read_file, show_goal, definition_outline, and search_declarations. "
            "Use tactic_sandbox for exploratory tactic prefixes (it shows the resulting goal and does not count as a proof attempt), "
            "show_goal to see the current goal state, and check_proof or try_tactics for proof attempts. "
            "check_proof accepts either a tactic body to place under `:= by`, or a complete Lean file "
            "(with imports, namespace, helper lemmas, and the target theorem); the theorem statement must stay byte-identical. "
            "Iterate: submit, read the Lean error, fix, resubmit. "
            "Do not use sorry, admit, axiom, hidden imports, "
            "Benchmark.GeneratedPreview, or reference Proofs modules. Do not assume a hardcoded solution from the task name. "
            "If native tool calling is unavailable, return JSON like {\"tool\":\"show_task\",\"arguments\":{}}."
        )
        user_prompt = (
            f"Solve the Lean task in editable file {editable}. "
            "Call show_task first, then inspect the public files and check proof bodies until Lean passes."
        )
    else:
        system_prompt = (
            "Solve one Lean task by JSON tool calls only. "
            "Allowed tools: show_task {}, read_file {path}, show_goal {}, "
            "definition_outline {query,limit}, search_declarations {query,limit}, "
            "tactic_sandbox {prefix}, try_tactics {tactics}, check_proof {proof}. "
            "Non-proof tools are capped; reserve budget for try_tactics/check_proof. "
            "No sorry/admit/axiom/hidden imports/reference Proofs. "
            "Reply only as JSON, e.g. {\"tool\":\"show_task\",\"arguments\":{}}."
        )
        user_prompt = f"Task file: {editable}. First call show_task."

    messages: list[dict[str, Any]] = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_prompt},
    ]

    def set_compact_user_context(content: str) -> None:
        messages[:] = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": f"{user_prompt}\n{content}\nReply with the next JSON tool call."},
        ]
    no_tool_response_limit = max(3, min(20, max_tool_calls))
    request_limit = max_tool_calls + max_attempts + no_tool_response_limit
    tool_calls_executed = 0
    non_proof_tool_calls = 0
    non_proof_tool_limit = min(
        DEFAULT_MAX_NON_PROOF_TOOL_CALLS,
        max(3, max_tool_calls // 2),
    )
    no_tool_responses = 0
    sandbox_state = {"count": 0, "limit": min(DEFAULT_MAX_SANDBOX_CALLS, max(1, max_tool_calls // 4))}
    usage_totals = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0}

    def _accumulate_usage(response: dict[str, object]) -> None:
        usage = response.get("usage") if isinstance(response, dict) else None
        if isinstance(usage, dict):
            usage_totals["requests"] += 1
            for key in ("prompt_tokens", "completion_tokens", "total_tokens"):
                value = usage.get(key)
                if isinstance(value, (int, float)):
                    usage_totals[key] += int(value)

    token_budget_exhausted = False
    for request_index in range(1, request_limit + 1):
        if _proof_attempt_count(attempts) >= max_attempts:
            break
        if tool_calls_executed >= max_tool_calls:
            break
        if DEFAULT_TOKEN_BUDGET and usage_totals["completion_tokens"] >= DEFAULT_TOKEN_BUDGET:
            token_budget_exhausted = True
            break
        try:
            response = chat_completion(
                messages,
                base_url=base_url,
                tools=FAIR_TOOLS if DEFAULT_NATIVE_TOOLS else None,
                tool_choice="auto" if DEFAULT_NATIVE_TOOLS else None,
                request_log_path=conversation_log_path,
                request_index=request_index,
            )
        except Exception as exc:
            error_payload = exc.to_dict() if isinstance(exc, ChatCompletionError) else {"message": str(exc)}
            status = "request_timeout" if isinstance(exc, ChatCompletionError) and exc.kind == "request_timeout" else "request_failed"
            _append_jsonl(
                conversation_log_path,
                {
                    "task_ref": task.get("task_ref"),
                    "request_index": request_index,
                    "status": status,
                    "error": error_payload,
                },
            )
            return {
                "task_ref": task.get("task_ref"),
                "status": status,
                "error": error_payload,
                "usage": usage_totals,
                "attempts": attempts,
                "tool_calls_executed": tool_calls_executed,
                "non_proof_tool_calls": non_proof_tool_calls,
                "non_proof_tool_limit": non_proof_tool_limit,
                "tool_log": str(tool_log_path),
                "conversation_log": str(conversation_log_path),
                "failure_class": _failure_taxonomy(status, attempts, tool_calls=tool_calls_executed, no_tool_responses=no_tool_responses),
            }
        _accumulate_usage(response)
        response_message = {}
        choices = response.get("choices")
        if isinstance(choices, list) and choices and isinstance(choices[0], dict):
            message = choices[0].get("message")
            if isinstance(message, dict):
                response_message = message
        tool_calls = response_message.get("tool_calls")
        _append_jsonl(
            conversation_log_path,
            {
                "task_ref": task.get("task_ref"),
                "request_index": request_index,
                "message": _logged_response_message(response_message),
                "usage": response.get("usage") if isinstance(response, dict) else None,
            },
        )
        assistant_message = {k: v for k, v in response_message.items() if k in {"role", "content", "tool_calls"}}
        if assistant_message:
            assistant_message.setdefault("role", "assistant")
            if "tool_calls" in assistant_message:
                assistant_message.setdefault("content", None)
        messages.append(assistant_message or {"role": "assistant", "content": _response_text(response)})
        if not isinstance(tool_calls, list) or not tool_calls:
            text = _response_text(response)
            tool_calls = _tool_calls_from_text(text)
        text_protocol = bool(tool_calls and all(isinstance(call, dict) and call.get("text_protocol") is True for call in tool_calls))
        if not isinstance(tool_calls, list) or not tool_calls:
            text = _response_text(response)
            if text.strip():
                no_tool_responses += 1
                if no_tool_responses >= no_tool_response_limit:
                    _append_jsonl(
                        conversation_log_path,
                        {
                            "task_ref": task.get("task_ref"),
                            "request_index": request_index,
                            "status": "no_tool_response_limit_exceeded",
                            "no_tool_responses": no_tool_responses,
                        },
                    )
                    break
                messages.append(
                    {
                        "role": "user",
                        "content": "Fair mode requires a tool call. Reply only with JSON for one allowed tool.",
                    }
                )
                continue
            break
        for tool_call in tool_calls:
            if not isinstance(tool_call, dict):
                continue
            function = tool_call.get("function")
            if not isinstance(function, dict):
                continue
            name = function.get("name")
            raw_args = function.get("arguments") or "{}"
            try:
                args = json.loads(raw_args) if isinstance(raw_args, str) else raw_args
            except json.JSONDecodeError:
                args = {}
            if not isinstance(args, dict):
                args = {}
            if not isinstance(name, str):
                continue
            if tool_calls_executed >= max_tool_calls:
                result = {"ok": False, "error": "max_tool_calls_exceeded"}
                _append_jsonl(
                    tool_log_path,
                    {
                        "task_ref": task.get("task_ref"),
                        "tool": name,
                        "arguments": args,
                        "result": result,
                        "tool_call_id": tool_call.get("id"),
                        "duration_seconds": 0,
                    },
                )
                if text_protocol:
                    content = f"Tool result for {name}: {_tool_result_content(result)}"
                    if DEFAULT_NATIVE_TOOLS:
                        messages.append({"role": "user", "content": content})
                    else:
                        set_compact_user_context(content)
                else:
                    messages.append(
                        {
                            "role": "tool",
                            "tool_call_id": tool_call.get("id") or f"call-{request_index}",
                            "name": name,
                            "content": _tool_result_content(result),
                        }
                    )
                continue
            if name in {"check_proof", "try_tactics"} and _proof_attempt_count(attempts) >= max_attempts:
                result = {"ok": False, "error": "max_attempts_exceeded"}
                _append_jsonl(
                    tool_log_path,
                    {
                        "task_ref": task.get("task_ref"),
                        "tool": name,
                        "arguments": args,
                        "result": result,
                        "tool_call_id": tool_call.get("id"),
                        "duration_seconds": 0,
                    },
                )
                if text_protocol:
                    content = f"Tool result for {name}: {_tool_result_content(result)}"
                    if DEFAULT_NATIVE_TOOLS:
                        messages.append({"role": "user", "content": content})
                    else:
                        set_compact_user_context(content)
                else:
                    messages.append(
                        {
                            "role": "tool",
                            "tool_call_id": tool_call.get("id") or f"call-{request_index}",
                            "name": name,
                            "content": _tool_result_content(result),
                        }
                    )
                continue
            if name not in {"check_proof", "try_tactics", "tactic_sandbox", "show_goal"} and non_proof_tool_calls >= non_proof_tool_limit:
                result = {
                    "ok": False,
                    "error": "non_proof_tool_budget_exceeded",
                    "non_proof_tool_calls": non_proof_tool_calls,
                    "non_proof_tool_limit": non_proof_tool_limit,
                    "message": "Use check_proof or try_tactics now. Do not re-read or re-show task context.",
                }
                tool_calls_executed += 1
                _append_jsonl(
                    tool_log_path,
                    {
                        "task_ref": task.get("task_ref"),
                        "tool": name,
                        "arguments": args,
                        "result": result,
                        "tool_call_id": tool_call.get("id"),
                        "duration_seconds": 0,
                    },
                )
                if text_protocol:
                    content = f"Tool result for {name}: {_tool_result_content(result)}"
                    if DEFAULT_NATIVE_TOOLS:
                        messages.append({"role": "user", "content": content})
                    else:
                        set_compact_user_context(content)
                else:
                    messages.append(
                        {
                            "role": "tool",
                            "tool_call_id": tool_call.get("id") or f"call-{request_index}",
                            "name": name,
                            "content": _tool_result_content(result),
                        }
                    )
                continue
            if name == "try_tactics":
                remaining = max(0, max_attempts - _proof_attempt_count(attempts))
                raw_tactics = args.get("tactics")
                if isinstance(raw_tactics, list):
                    args["tactics"] = raw_tactics[:remaining]
            tool_start = time.time()
            result = _execute_fair_tool(
                name,
                args,
                task=task,
                workspace=workspace,
                original=original,
                proof_path=proof_path,
                target_module=target_module,
                attempts_dir=attempts_dir,
                attempts=attempts,
                sandbox_state=sandbox_state,
            )
            tool_calls_executed += 1
            if name not in {"check_proof", "try_tactics", "tactic_sandbox", "show_goal"}:
                non_proof_tool_calls += 1
            _append_jsonl(
                tool_log_path,
                {
                    "task_ref": task.get("task_ref"),
                    "tool": name,
                    "arguments": args,
                    "result": result,
                    "tool_call_id": tool_call.get("id"),
                    "duration_seconds": round(time.time() - tool_start, 3),
                },
            )
            if text_protocol:
                content = f"Tool result for {name}: {_tool_result_content(result)}"
                if DEFAULT_NATIVE_TOOLS:
                    messages.append({"role": "user", "content": content})
                else:
                    set_compact_user_context(content)
            else:
                messages.append(
                    {
                        "role": "tool",
                        "tool_call_id": tool_call.get("id") or f"call-{request_index}",
                        "name": name,
                        "content": _tool_result_content(result),
                    }
                )
            if result.get("passed") is True:
                return {
                    "task_ref": task.get("task_ref"),
                    "status": "lean_passed",
                    "failure_class": None,
                    "usage": usage_totals,
                    "attempts": attempts,
                    "tool_calls_executed": tool_calls_executed,
                    "non_proof_tool_calls": non_proof_tool_calls,
                    "non_proof_tool_limit": non_proof_tool_limit,
                    "tactic_sandbox_calls": sandbox_state["count"],
                    "tool_log": str(tool_log_path),
                    "conversation_log": str(conversation_log_path),
                }
    if not attempts:
        proof_path.write_text(original, encoding="utf-8")
    final_status = (
        "failed_no_tool_calls"
        if no_tool_responses >= no_tool_response_limit
        else ("failed_submitted" if attempts else "failed_no_attempt")
    )
    return {
        "task_ref": task.get("task_ref"),
        "status": final_status,
        "failure_class": _failure_taxonomy(final_status, attempts, tool_calls=tool_calls_executed, no_tool_responses=no_tool_responses),
        "usage": usage_totals,
        "token_budget_exhausted": token_budget_exhausted,
        "attempts": attempts,
        "tool_calls_executed": tool_calls_executed,
        "non_proof_tool_calls": non_proof_tool_calls,
        "non_proof_tool_limit": non_proof_tool_limit,
        "no_tool_responses": no_tool_responses,
        "tactic_sandbox_calls": sandbox_state["count"],
        "tool_log": str(tool_log_path),
        "conversation_log": str(conversation_log_path),
    }


def run_group(
    group_id: str,
    *,
    suite: str = "active",
    keep_workspace: bool = False,
    dry_run: bool = False,
    max_attempts: int = 1,
    max_tool_calls: int = DEFAULT_MAX_TOOL_CALLS,
    task_ref: str | None = None,
) -> tuple[int, Path]:
    if max_attempts < 0:
        raise ValueError("max_attempts must be non-negative")
    if max_tool_calls < 0:
        raise ValueError("max_tool_calls must be non-negative")
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_subject = task_ref or group_id
    model_slug = "".join(ch if ch.isalnum() else "-" for ch in DEFAULT_MODEL).strip("-").lower()
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{RUN_SLUG}-fair-{model_slug}-{run_subject.replace('/', '__')}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    start = time.time()
    group = load_group(group_id, suite)
    if task_ref:
        group = filter_group_to_task(group, task_ref)
    built = build_group_workspace(group, run_id=run_id)
    assert_workspace_isolated(built.path)
    base_url = DEFAULT_BASE_URL
    response: dict[str, object]
    if dry_run:
        response = {
            "status": "dry_run",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_MODEL,
            "mode": "fair",
            "max_attempts": max_attempts,
            "max_tool_calls": max_tool_calls,
        }
    elif not _api_key() and not _local_no_auth_endpoint(base_url):
        provider_key_hint = f", DEFAULT_HARNESS_{DEFAULT_PROVIDER.upper()}_API_KEY" if DEFAULT_PROVIDER else ""
        response = {
            "status": "missing_credentials",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_MODEL,
            "mode": "fair",
            "error": f"fair mode requires DEFAULT_HARNESS_API_KEY{provider_key_hint}, GAZELLA_API_KEY, OPENAI_API_KEY, or a localhost-compatible no-auth endpoint",
            "tasks": [],
        }
    else:
        task_results: list[dict[str, object]] = []
        warm_builds: list[dict[str, object]] = []
        try:
            tasks_payload = json.loads((built.path / "harness" / "TASKS.json").read_text(encoding="utf-8"))
            # Warm the Lean dependency graph once per target module so agent-visible
            # check timeouts measure proof elaboration, not cold dependency builds.
            warm_timeout = int(os.environ.get("DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS", "1800"))
            for task in tasks_payload.get("tasks", []):
                module = task.get("target_module") if isinstance(task, dict) else None
                if isinstance(module, str) and module:
                    warm_start = time.time()
                    warm_code, _warm_output = _run_lean_module(built.path, module, timeout_seconds=warm_timeout)
                    warm_builds.append(
                        {
                            "task_ref": task.get("task_ref"),
                            "module": module,
                            "exit_code": warm_code,
                            "duration_seconds": round(time.time() - warm_start, 3),
                        }
                    )
            for task in tasks_payload.get("tasks", []):
                if isinstance(task, dict):
                    task_results.append(
                        _attempt_task_fair(
                            task,
                            built.path,
                            base_url=base_url,
                            max_attempts=max_attempts,
                            max_tool_calls=max_tool_calls,
                            attempts_dir=run_dir / "attempts",
                            tool_log_path=run_dir / "tool-calls" / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}.jsonl",
                            conversation_log_path=run_dir / "conversations" / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}.jsonl",
                        )
                    )
            aggregate_usage = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0}
            for task_result in task_results:
                task_usage = task_result.get("usage")
                if isinstance(task_usage, dict):
                    for key in aggregate_usage:
                        value = task_usage.get(key)
                        if isinstance(value, (int, float)):
                            aggregate_usage[key] += int(value)
            response = {"status": "completed", "provider": _active_provider(), "base_url": base_url, "model": DEFAULT_MODEL, "mode": "fair", "usage": aggregate_usage, "warm_builds": warm_builds, "tasks": task_results}
        except Exception as exc:
            response = {"status": "harness_error", "error": str(exc), "provider": _active_provider(), "base_url": base_url, "model": DEFAULT_MODEL, "mode": "fair", "warm_builds": warm_builds, "tasks": task_results}

    (run_dir / "workspace-manifest.json").write_text((built.path / "workspace-manifest.json").read_text(encoding="utf-8"), encoding="utf-8")
    shutil.copy2(built.path / "harness" / "TASK_SUMMARY.md", run_dir / "TASK_SUMMARY.md")
    (run_dir / "harness-request.json").write_text(
        json.dumps(
            {
                "group": agent_group_to_json(group),
                "provider": _active_provider(),
                "base_url": base_url,
                "model": DEFAULT_MODEL,
                "mode": "fair",
                "max_attempts": max_attempts,
                "max_tool_calls": max_tool_calls,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (run_dir / "harness-response.json").write_text(json.dumps(response, indent=2) + "\n", encoding="utf-8")
    (run_dir / "stdout.txt").write_text("", encoding="utf-8")
    (run_dir / "stderr.txt").write_text("", encoding="utf-8")
    submitted_dir = run_dir / "submitted"
    for task in group.tasks:
        for rel in task.editable_files:
            src = built.path / rel
            if src.is_file():
                dst = submitted_dir / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
    verifier_result = verify_group(group, built.path, artifact_dir=run_dir / "verifier")
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": HARNESS_ID,
        "provider": _active_provider(),
        "model": DEFAULT_MODEL,
        "track": "group/lean_tools",
        "mode": "fair",
        "run_mode": "task" if task_ref else "group",
        "group_id": group_id,
        "task_ref": task_ref,
        "suite": suite,
        "started_at": started_at,
        "base_url": base_url,
        "auth_mode": "env" if _api_key() else "none",
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": response["status"],
        "usage": response.get("usage"),
        "workspace": str(built.path) if keep_workspace else None,
        "verifier": verifier_result,
    }
    (run_dir / "run.json").write_text(json.dumps(run, indent=2) + "\n", encoding="utf-8")
    write_run_report(run_dir, run)
    if not keep_workspace:
        shutil.rmtree(built.path, ignore_errors=True)
    return (0 if response["status"] == "completed" and verifier_result["score"]["passed_targets"] == verifier_result["score"]["total_targets"] else 1), run_dir


def main() -> int:
    parser = argparse.ArgumentParser(description="Default OpenAI-compatible Lean-tool harness")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("smoke")
    run = sub.add_parser("run-group")
    run.add_argument("group_id")
    run.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    run.add_argument("--keep-workspace", action="store_true")
    run.add_argument("--dry-run", action="store_true")
    run.add_argument("--max-attempts", type=int, default=1)
    run.add_argument("--max-tool-calls", type=int, default=DEFAULT_MAX_TOOL_CALLS)
    run.add_argument("--task-ref")
    args = parser.parse_args()
    if args.command == "smoke":
        print(json.dumps(endpoint_smoke(DEFAULT_BASE_URL, DEFAULT_MODEL), indent=2))
        return 0
    code, run_dir = run_group(
        args.group_id,
        suite=args.suite,
        keep_workspace=args.keep_workspace,
        dry_run=args.dry_run,
        max_attempts=args.max_attempts,
        max_tool_calls=args.max_tool_calls,
        task_ref=args.task_ref,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
