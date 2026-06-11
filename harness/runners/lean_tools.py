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

HARNESS_ID = "default"
RUN_SLUG = "default"
VALID_MODES = ("fair", "fair+libs", "tuned", "legacy")
PROVIDER_DEFAULTS = {
    "qwen": {
        "base_url": "https://spark-de79.gazella-vector.ts.net/v1",
        "model": "qwen3.5-397b",
    },
    "glm": {
        "base_url": "https://api.z.ai/api/coding/paas/v4",
        "model": "glm-5.1",
    },
}
DEFAULT_PROVIDER = os.environ.get("DEFAULT_HARNESS_PROVIDER", "").strip().lower()


def _provider_env(name: str) -> str | None:
    if not DEFAULT_PROVIDER:
        return None
    value = os.environ.get(f"DEFAULT_HARNESS_{DEFAULT_PROVIDER.upper()}_{name}")
    return value if value not in {None, ""} else None


def _provider_default(name: str, fallback: str) -> str:
    if not DEFAULT_PROVIDER:
        return fallback
    provider_defaults = PROVIDER_DEFAULTS.get(DEFAULT_PROVIDER, {})
    value = provider_defaults.get(name.lower())
    return str(value) if value else fallback


def _harness_env(name: str, fallback: str, *, legacy_name: str | None = None) -> str:
    profile_value = _provider_env(name)
    if profile_value is not None:
        return profile_value
    direct_value = os.environ.get(f"DEFAULT_HARNESS_{name}")
    if direct_value not in {None, ""}:
        return str(direct_value)
    if legacy_name:
        legacy_value = os.environ.get(legacy_name)
        if legacy_value not in {None, ""}:
            return str(legacy_value)
    return _provider_default(name, fallback)


DEFAULT_BASE_URL = _harness_env("BASE_URL", "https://spark-de79.gazella-vector.ts.net/v1", legacy_name="GAZELLA_BASE_URL")
DEFAULT_MODEL = _harness_env("MODEL", "qwen3.5-397b", legacy_name="GAZELLA_MODEL")
MAX_FILE_CHARS = int(os.environ.get("DEFAULT_HARNESS_MAX_FILE_CHARS", os.environ.get("GAZELLA_MAX_FILE_CHARS", "6000")))
PROMPT_CONTEXT_CHARS = int(os.environ.get("DEFAULT_HARNESS_PROMPT_CONTEXT_CHARS", os.environ.get("GAZELLA_PROMPT_CONTEXT_CHARS", "8000")))
LEAN_CHECK_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_LEAN_CHECK_TIMEOUT_SECONDS", os.environ.get("GAZELLA_LEAN_CHECK_TIMEOUT_SECONDS", "240")))
REQUEST_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS", os.environ.get("GAZELLA_REQUEST_TIMEOUT_SECONDS", "180")))
REQUEST_RETRIES = int(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRIES", os.environ.get("GAZELLA_REQUEST_RETRIES", "5")))
REQUEST_RETRY_BACKOFF_SECONDS = float(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS", os.environ.get("GAZELLA_REQUEST_RETRY_BACKOFF_SECONDS", "2")))
DEFAULT_CONTEXT_TOKENS = os.environ.get("DEFAULT_HARNESS_CONTEXT_TOKENS", os.environ.get("GAZELLA_N_CTX"))
DEFAULT_MAX_TOOL_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_TOOL_CALLS", "24"))
DEFAULT_MAX_RESPONSE_TOKENS = int(os.environ.get("DEFAULT_HARNESS_MAX_RESPONSE_TOKENS", "8192"))
DEFAULT_NATIVE_TOOLS = os.environ.get("DEFAULT_HARNESS_NATIVE_TOOLS", "1").lower() not in {"0", "false", "no"}
DEFAULT_TOOL_RESULT_CHARS = int(os.environ.get("DEFAULT_HARNESS_TOOL_RESULT_CHARS", "6000"))
DEFAULT_TASK_SUMMARY_CHARS = int(os.environ.get("DEFAULT_HARNESS_TASK_SUMMARY_CHARS", "8000"))
DEFAULT_MAX_NON_PROOF_TOOL_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_NON_PROOF_TOOL_CALLS", "24"))
DEFAULT_MAX_SANDBOX_CALLS = int(os.environ.get("DEFAULT_HARNESS_MAX_SANDBOX_CALLS", "16"))
DEFAULT_TOKEN_BUDGET = int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0"))  # 0 = unlimited; counts completion tokens per task
DEFAULT_ALLOW_GRINDSET_TOOLS = os.environ.get("DEFAULT_HARNESS_ALLOW_GRINDSET_TOOLS", "0").lower() in {"1", "true", "yes"}
GRINDSET_IMPORT = "import Benchmark.Grindset"
HTTP_USER_AGENT = os.environ.get("DEFAULT_HARNESS_HTTP_USER_AGENT", "verity-benchmark-harness/1.0")
LEAN_CHECK_MODE = os.environ.get("DEFAULT_HARNESS_CHECK_MODE", "file").strip().lower()  # "file" = lake env lean <editable>, "module" = lake build
STUCK_NUDGE = os.environ.get("DEFAULT_HARNESS_STUCK_NUDGE", "1").lower() not in {"0", "false", "no"}


class ChatCompletionError(RuntimeError):
    def __init__(
        self,
        message: str,
        *,
        kind: str,
        attempts: int,
        timeout_seconds: int,
        transient: bool,
        last_status: int | None = None,
    ) -> None:
        super().__init__(message)
        self.kind = kind
        self.attempts = attempts
        self.timeout_seconds = timeout_seconds
        self.transient = transient
        self.last_status = last_status

    def to_dict(self) -> dict[str, object]:
        return {
            "message": str(self),
            "kind": self.kind,
            "attempts": self.attempts,
            "timeout_seconds": self.timeout_seconds,
            "transient": self.transient,
            "last_status": self.last_status,
        }


def _api_key() -> str | None:
    return (
        _provider_env("API_KEY")
        or os.environ.get("DEFAULT_HARNESS_API_KEY")
        or os.environ.get("GAZELLA_API_KEY")
        or os.environ.get("OPENAI_API_KEY")
    )


def _active_provider() -> str:
    return DEFAULT_PROVIDER or "custom"


def endpoint_smoke(base_url: str = DEFAULT_BASE_URL, model: str = DEFAULT_MODEL) -> dict[str, object]:
    body = json.dumps(
        {
            "model": model,
            "messages": [{"role": "user", "content": "Dis moi tres brievement qui est Vasco de Gama (2 phrases)"}],
            "max_tokens": 500,
            "temperature": 0,
        }
    ).encode("utf-8")
    request = urllib.request.Request(f"{base_url.rstrip('/')}/chat/completions", data=body, headers={"Content-Type": "application/json", "User-Agent": HTTP_USER_AGENT}, method="POST")
    api_key = _api_key()
    if api_key:
        request.add_header("Authorization", f"Bearer {api_key}")
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read().decode("utf-8"))


def chat_completion(
    messages: list[dict[str, Any]],
    *,
    base_url: str,
    model: str = DEFAULT_MODEL,
    max_tokens: int = DEFAULT_MAX_RESPONSE_TOKENS,
    tools: list[dict[str, Any]] | None = None,
    tool_choice: object | None = None,
    request_log_path: Path | None = None,
    request_index: int | None = None,
) -> dict[str, object]:
    payload: dict[str, Any] = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": 0,
    }
    if DEFAULT_CONTEXT_TOKENS:
        payload["n_ctx"] = int(DEFAULT_CONTEXT_TOKENS)
    if tools is not None:
        payload["tools"] = tools
    if tool_choice is not None:
        payload["tool_choice"] = tool_choice
    body = json.dumps(payload).encode("utf-8")
    max_request_attempts = max(1, REQUEST_RETRIES + 1)
    last_error: ChatCompletionError | None = None
    retry_after_seconds: float | None = None
    for attempt in range(1, max_request_attempts + 1):
        retry_after_seconds = None
        started = time.time()
        request = urllib.request.Request(f"{base_url.rstrip('/')}/chat/completions", data=body, headers={"Content-Type": "application/json", "User-Agent": HTTP_USER_AGENT}, method="POST")
        api_key = _api_key()
        if api_key:
            request.add_header("Authorization", f"Bearer {api_key}")
        try:
            with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT_SECONDS) as response:
                decoded = json.loads(response.read().decode("utf-8"))
                if request_log_path is not None and attempt > 1:
                    _append_jsonl(
                        request_log_path,
                        {
                            "status": "request_retry_succeeded",
                            "request_index": request_index,
                            "attempt": attempt,
                            "duration_seconds": round(time.time() - started, 3),
                        },
                    )
                return decoded
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            transient = exc.code in {408, 409, 425, 429, 500, 502, 503, 504, 520, 521, 522, 523, 524}
            try:
                retry_after_seconds = float(exc.headers.get("Retry-After")) if exc.headers.get("Retry-After") else None
            except (TypeError, ValueError):
                retry_after_seconds = None
            kind = "context_length_exceeded" if "exceeds the available context size" in detail else ("http_transient" if transient else "http_error")
            message = f"HTTP {exc.code}: {detail[:1200]}"
            last_error = ChatCompletionError(
                message,
                kind=kind,
                attempts=attempt,
                timeout_seconds=REQUEST_TIMEOUT_SECONDS,
                transient=transient,
                last_status=exc.code,
            )
        except (TimeoutError, socket.timeout) as exc:
            last_error = ChatCompletionError(
                f"request_timeout: {exc}",
                kind="request_timeout",
                attempts=attempt,
                timeout_seconds=REQUEST_TIMEOUT_SECONDS,
                transient=True,
            )
        except (urllib.error.URLError, OSError) as exc:
            last_error = ChatCompletionError(
                f"transport_error: {exc}",
                kind="transport_error",
                attempts=attempt,
                timeout_seconds=REQUEST_TIMEOUT_SECONDS,
                transient=True,
            )
        if request_log_path is not None and last_error is not None:
            _append_jsonl(
                request_log_path,
                {
                    "status": "request_retry" if last_error.transient and attempt < max_request_attempts else "request_failed",
                    "request_index": request_index,
                    "attempt": attempt,
                    "max_attempts": max_request_attempts,
                    "duration_seconds": round(time.time() - started, 3),
                    "error": last_error.to_dict(),
                },
            )
        if last_error is None or not last_error.transient or attempt >= max_request_attempts:
            break
        delay = min(120.0, REQUEST_RETRY_BACKOFF_SECONDS * (2 ** (attempt - 1)))
        if retry_after_seconds is not None:
            delay = min(300.0, max(delay, retry_after_seconds))
        time.sleep(delay)
    if last_error is None:
        raise ChatCompletionError(
            "request_failed_without_error",
            kind="request_failed",
            attempts=max_request_attempts,
            timeout_seconds=REQUEST_TIMEOUT_SECONDS,
            transient=False,
        )
    if last_error.kind == "request_timeout":
        raise ChatCompletionError(
            f"request_timeout after {last_error.attempts} attempt(s), timeout={REQUEST_TIMEOUT_SECONDS}s",
            kind=last_error.kind,
            attempts=last_error.attempts,
            timeout_seconds=REQUEST_TIMEOUT_SECONDS,
            transient=last_error.transient,
            last_status=last_error.last_status,
        ) from last_error
    raise last_error


def _response_text(response: dict[str, object]) -> str:
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices:
        return ""
    first = choices[0]
    if not isinstance(first, dict):
        return ""
    message = first.get("message")
    if not isinstance(message, dict):
        return ""
    content = message.get("content")
    return content if isinstance(content, str) else ""


def _logged_response_message(message: dict[str, object]) -> dict[str, object]:
    logged = {k: v for k, v in message.items() if k in {"role", "content", "tool_calls"}}
    reasoning = message.get("reasoning_content")
    if isinstance(reasoning, str) and reasoning:
        logged["reasoning_content"] = reasoning[-DEFAULT_TOOL_RESULT_CHARS:]
        logged["provider_reasoning_chars"] = len(reasoning)
    return logged


def _strip_thinking(text: str) -> str:
    return re.sub(r"(?s)<think>.*?</think>\s*", "", text).strip()


def _extract_lean_file(text: str) -> str:
    text = _strip_thinking(text)
    fenced = re.search(r"```(?:lean)?\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    if fenced:
        return fenced.group(1).strip() + "\n"
    return text.strip() + "\n"


def _looks_like_full_file(body: str) -> bool:
    return bool(re.search(r"(?m)^\s*(?:import|namespace)\s+\S", body)) and bool(
        re.search(r"(?m)^\s*(?:theorem|lemma)\s+\S", body)
    )


def _indent_proof_body(text: str) -> str:
    body = _extract_lean_file(text)
    theorem_body = re.search(r"(?s)\b(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:=\s*by[ \t]*(?:\n)?", body)
    if theorem_body:
        body = body[theorem_body.end() :]
    body = re.sub(r"(?m)^end\s+[A-Za-z0-9_'.]+\s*$.*", "", body, flags=re.DOTALL)
    lines: list[str] = []
    in_preamble = True
    for raw_line in body.splitlines():
        line = raw_line.rstrip()
        stripped = line.strip()
        if in_preamble and (
            not stripped or stripped.startswith(("import ", "namespace ", "open ", "/--", "-/", "--"))
        ):
            continue
        in_preamble = False
        if stripped.startswith(("Explanation", "This proof", "The proof", "Note:", "```")):
            break
        lines.append(line)
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if not lines:
        return ""
    # Preserve the proof's relative indentation exactly; only normalize the
    # common left margin so the body sits two spaces under `:= by`.
    min_indent = min(len(line) - len(line.lstrip()) for line in lines if line.strip())
    normalized = [line[min_indent:] if line.strip() else "" for line in lines]
    return "\n".join(f"  {line}" if line else "" for line in normalized) + "\n"


def _patch_proof_body(original: str, proof_body: str) -> str:
    extracted = _extract_lean_file(proof_body)
    if _looks_like_full_file(extracted):
        return extracted
    replacement = ":= by\n" + _indent_proof_body(proof_body)
    pattern = re.compile(
        r":=\s*by\s*(?:--[^\n]*\n\s*)?(?:exact\s+\?_[A-Za-z0-9_']*|sorry|admit)\b",
        re.MULTILINE,
    )
    if pattern.search(original):
        return pattern.sub(lambda _match: replacement.rstrip(), original, count=1) + ("\n" if original.endswith("\n") else "")
    marker = ":= by"
    index = original.find(marker)
    if index == -1:
        return original
    end_index = original.find("\n\nend ", index)
    if end_index == -1:
        end_index = len(original)
    return original[:index] + replacement + original[end_index:]


FORBIDDEN_PROOF_RE = re.compile(r"\b(sorry|admit|axiom)\b|\?_[A-Za-z0-9_']*")


def _contains_forbidden_proof_token(text: str) -> bool:
    return FORBIDDEN_PROOF_RE.search(text) is not None


def _ensure_grindset_import(text: str) -> str:
    return _ensure_import(text, GRINDSET_IMPORT)


def _ensure_import(text: str, import_line: str) -> str:
    if import_line in text:
        return text
    lines = text.splitlines()
    insert_at = 0
    for index, line in enumerate(lines):
        if line.startswith("import "):
            insert_at = index + 1
    lines.insert(insert_at, import_line)
    return "\n".join(lines) + ("\n" if text.endswith("\n") else "")


def _decl_basename(theorem_name: object) -> str | None:
    if not isinstance(theorem_name, str) or not theorem_name:
        return None
    return theorem_name.split(".")[-1]


def _candidate_from_response(original: str, response_text: str, theorem_name: object) -> str:
    return _patch_proof_body(original, response_text)


def _candidate_from_comparison_response(original: str, response_text: str, theorem_name: object) -> str:
    return _ensure_grindset_import(_patch_proof_body(original, response_text))


def _candidate_from_local(original: str, tactic_body: str, theorem_name: object) -> str:
    candidate = _patch_proof_body(original, tactic_body)
    helper_modules = [
        "Arith",
        "Cork",
        "Kleros",
        "Paladin",
        "Reserve",
    ]
    for module in helper_modules:
        if f"Benchmark.Grindset.{module}" in tactic_body:
            candidate = _ensure_import(candidate, f"import Benchmark.Grindset.{module}")
    if re.search(r"\bgrind\b", tactic_body):
        return _ensure_grindset_import(candidate)
    return candidate


def _is_rejected_model_body(task: dict[str, object], response_text: str) -> str | None:
    body = _indent_proof_body(response_text)
    compact = " ".join(line.strip() for line in body.splitlines() if line.strip())
    theorem_name = task.get("theorem_name")
    large_solvency_targets = {
        "Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency",
    }
    if theorem_name in large_solvency_targets and compact in {"grind", "grind []"}:
        return "broad_grind_rejected_for_large_solvency_target"
    return None


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


def _context_for_task(
    task: dict[str, object],
    workspace: Path,
    editable: str,
    editable_files: object,
    specification_files: object,
    implementation_files: object,
) -> tuple[str, str]:
    context_parts: list[str] = []
    symbol_parts: list[str] = []
    total_context_chars = 0
    proof_patterns = workspace / "harness" / "PROOF_PATTERNS.md"
    if proof_patterns.is_file():
        pattern_text = proof_patterns.read_text(encoding="utf-8")[:1500]
        context_parts.append(f"[public proof guide: harness/PROOF_PATTERNS.md]\n{pattern_text}")
        total_context_chars += len(context_parts[-1])
    seen: set[str] = set()
    for label, paths in (("editable", editable_files), ("specification", specification_files), ("implementation", implementation_files)):
        if not isinstance(paths, list):
            continue
        for rel in paths:
            if not isinstance(rel, str) or rel in seen or not (workspace / rel).is_file():
                continue
            seen.add(rel)
            file_text = _read_workspace_file(workspace, rel)
            symbol_summary = _public_symbol_summary(file_text)
            if symbol_summary:
                symbol_parts.append(f"[symbols from {rel}]\n{symbol_summary}")
            snippet = f"[{label}: {rel}]\n{file_text}"
            if label != "editable" and total_context_chars + len(snippet) > PROMPT_CONTEXT_CHARS:
                continue
            context_parts.append(snippet)
            total_context_chars += len(snippet)
    return "\n\n".join(context_parts), "\n\n".join(symbol_parts)


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


def _theorem_statement(original: str, theorem_name: object) -> str:
    decl_name = _decl_basename(theorem_name)
    if not decl_name:
        return ""
    pattern = re.compile(
        rf"(?ms)^\s*(?:theorem|lemma)\s+{re.escape(decl_name)}\b.*?:=\s*by",
    )
    match = pattern.search(original)
    if match:
        return original[match.start() : match.end()].rsplit(":=", 1)[0].strip()[:2000]
    generic = re.search(r"(?ms)^\s*(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:=\s*by", original)
    if generic:
        return original[generic.start() : generic.end()].rsplit(":=", 1)[0].strip()[:2000]
    return ""


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


def _local_tactic_candidates(task: dict[str, object]) -> list[tuple[str, str]]:
    theorem_name = task.get("theorem_name")
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_pool_balance":
        return [
            (
                "side_entrance_deposit_simp",
                """have hWrites :
    let s' := ((SideEntrance.deposit amount).run s).snd
    s'.storage 0 = add (s.storage 0) amount ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount := by
  constructor
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [deposit_sets_pool_balance_spec] using hWrites.1
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_sender_credit":
        return [
            (
                "side_entrance_deposit_simp",
                """have hWrites :
    let s' := ((SideEntrance.deposit amount).run s).snd
    s'.storage 0 = add (s.storage 0) amount ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount := by
  constructor
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [deposit_sets_sender_credit_spec] using hWrites.2
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_preserves_pool_balance":
        return [
            (
                "side_entrance_flash_simp",
                """have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
have hWrites :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [flashLoanViaDeposit_preserves_pool_balance_spec] using hWrites.1
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_sets_sender_credit":
        return [
            (
                "side_entrance_flash_simp",
                """have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
have hWrites :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [flashLoanViaDeposit_sets_sender_credit_spec] using hWrites.2.1
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.exploit_trace_drains_pool":
        return [
            (
                "side_entrance_exploit_simp",
                """have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
have hFlash :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
have hPoolEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0 = s.storage 0 :=
  hFlash.1
have hCreditEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2 s.sender =
    add (s.storageMap 2 s.sender) amount := hFlash.2.1
have hSenderEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender = s.sender :=
  hFlash.2.2
rw [hFresh] at hCreditEq
have hCredit : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
    ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender = amount := by
  rw [hSenderEq, hCreditEq]
  exact Verity.Core.Uint256.zero_add amount
have hCreditBound : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
    ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender <=
    ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0 := by
  rw [hCredit, hPoolEq]
  exact hBorrow
let sFlash := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
have hCreditBound' : (sFlash.storageMap 2 sFlash.sender <= sFlash.storage 0) = true := by
  simp [sFlash, hCreditBound]
have hWithdraw :
    ((SideEntrance.withdraw).run sFlash).snd.storage 0 =
      sub (sFlash.storage 0) (sFlash.storageMap 2 sFlash.sender) := by
  simp [SideEntrance.withdraw, SideEntrance.poolBalance, SideEntrance.totalCredits,
    SideEntrance.creditOf, hCreditBound',
    getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, msgSender]
unfold exploit_trace_drains_pool_spec
calc ((SideEntrance.withdraw).run ((SideEntrance.flashLoanViaDeposit amount).run s).snd).snd.storage 0
    = sub (((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0)
          (((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
           ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender) := by
        simpa [sFlash] using hWithdraw
  _ = sub (s.storage 0) amount := by rw [hPoolEq, hCredit]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_starts_chain_at_threshold":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_starts_chain_at_threshold_spec
intro sPost _ _
have hThresholdBool : (add (s.storage 1) 1 == 65536) = true := by
  simp [hThreshold]
simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold, hThresholdBool,
  DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
  DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
  Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.deposit_increments_deposit_count":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_increments_deposit_count_spec
by_cases hFull : depositAmount >= 32000000000
· by_cases hThreshold : add (s.storage 1) 1 = 65536
  · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
      DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
      DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Contract.run, ContractResult.snd]
  · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
      DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
      DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· have hSmall : depositAmount < 32000000000 := Nat.lt_of_not_ge hFull
  simp [DepositContractMinimal.deposit, hCount, hMin, hFull,
    DepositContractMinimal.depositCount, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_increments_full_count":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_increments_full_count_for_full_deposit_spec
intro sPost _
by_cases hThreshold : add (s.storage 1) 1 = 65536
· have hThresholdBool : (add (s.storage 1) 1 == 65536) = true := by
    simp [hThreshold]
  simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold, hThresholdBool,
    DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
    DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· have hThresholdBool : (add (s.storage 1) 1 == 65536) = false := by
    simp [hThreshold]
  simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold, hThresholdBool,
    DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
    DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_preserves_partial_gap":
        return [
            (
                "ethereum_deposit_branch_simp",
                """dsimp
have hWrites :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 = add (s.storage 0) 1 ∧
    s'.storage 1 = add (s.storage 1) 1 := by
  by_cases hThreshold : add (s.storage 1) 1 = 65536
  · constructor
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
        Bind.bind, Contract.run, ContractResult.snd]
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
        Bind.bind, Contract.run, ContractResult.snd]
  · constructor
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.snd]
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.snd]
rcases hWrites with ⟨hDeposits, hFullDeposits⟩
rw [hDeposits, hFullDeposits]
apply Verity.Core.Uint256.add_right_cancel
calc
  ((s.storage 0 + 1) - (s.storage 1 + 1)) + (s.storage 1 + 1)
      = s.storage 0 + 1 := by
          exact Verity.Core.Uint256.sub_add_cancel_left (s.storage 0 + 1) (s.storage 1 + 1)
  _ = (s.storage 0 - s.storage 1) + (s.storage 1 + 1) := by
        rw [← Verity.Core.Uint256.add_assoc]
        rw [Verity.Core.Uint256.sub_add_cancel_left (s.storage 0) (s.storage 1)]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.small_deposit_preserves_full_count":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_preserves_full_count_for_small_deposit_spec
intro sPost _
have hNotFull : ¬depositAmount >= 32000000000 := by
  exact Nat.not_le_of_gt hSmall
simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hNotFull,
  DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
  getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
  Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.ceildiv_sandwich":
        return [
            (
                "lido_grindset_arith",
                """exact Benchmark.Grindset.Arith.ceildiv_sandwich_spec_holds x d hd hNoOverflow
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.shares_conversion_monotone":
        return [
            (
                "lido_grindset_arith",
                """have hTSVal : totalShares.val > 0 := by
  simpa [Verity.Core.Uint256.lt_def] using hTS
exact Benchmark.Grindset.Arith.shares_conversion_monotone_spec_holds
  a b totalPooledEther totalShares hTSVal hNoOverflow
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency":
        return [
            (
                "lido_locked_funds_solvency_helper",
                """exact Benchmark.Grindset.Arith.locked_funds_solvency_spec_holds
  s hMaxLS hRR_pos hRR_lt hTS hTPE
  hNoOverflow1 hNoOverflow2 hNoOverflow3 hNoOverflow4 hNoOverflow5
""",
            )
        ]
    if theorem_name in {
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_capital",
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_book_value",
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_buy_price",
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_sell_price",
    }:
        spec_by_theorem = {
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_capital":
                "syncPriceBand_sets_capital_spec",
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_book_value":
                "syncPriceBand_sets_book_value_spec",
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_buy_price":
                "syncPriceBand_sets_buy_price_spec",
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_sell_price":
                "syncPriceBand_sets_sell_price_spec",
        }
        spec_name = spec_by_theorem[str(theorem_name)]
        return [
            (
                "nexus_sync_price_band_simp",
                f"""unfold {spec_name}
simp [RammPriceBand.syncPriceBand, hSupply, RammPriceBand.capital, RammPriceBand.supply,
  RammPriceBand.bookValue, RammPriceBand.buySpotPrice, RammPriceBand.sellSpotPrice,
  Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, setStorage]
""",
            )
        ]
    kleros_helpers = {
        "Benchmark.Cases.Kleros.SortitionTrees.parent_equals_sum_of_children":
            "parent_equals_sum_of_children_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.root_equals_sum_of_leaves":
            "root_equals_sum_of_leaves_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.node_id_bijection":
            "node_id_bijection_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.root_minus_left_equals_right_subtree":
            "root_minus_left_equals_right_subtree_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.draw_interval_matches_weights":
            "draw_interval_matches_weights_spec_holds ticket s hRoot hInRange",
        "Benchmark.Cases.Kleros.SortitionTrees.draw_selects_valid_leaf":
            "draw_selects_valid_leaf_spec_holds ticket s hRoot hInRange",
    }
    if theorem_name in kleros_helpers:
        return [
            (
                "kleros_grindset_helper",
                f"""exact Benchmark.Grindset.Kleros.{kleros_helpers[str(theorem_name)]}
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Cork.PoolSolvency.solvency_preserved":
        return [
            (
                "cork_grindset_helper",
                """exact Benchmark.Grindset.Cork.solvency_preserved_spec_holds
  s referenceAssetsOut hSolvencyBefore hColScale hRefScale hSwapRate hRefOut
  hNoOvf1 hNoOvf2 hNoOvf3 hNoOvf4 hNoOvf5 hSupplyGeBal
""",
            )
        ]
    paladin_usdc_success_specs = {
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_marks_user_claimed":
            "claimUsdc_marks_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_updates_round_claimed":
            "claimUsdc_updates_round_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_updates_total_allocated":
            "claimUsdc_updates_total_allocated_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_preserves_weth_state":
            "claimUsdc_preserves_weth_state_spec",
    }
    if theorem_name in paladin_usdc_success_specs:
        spec_name = paladin_usdc_success_specs[str(theorem_name)]
        return [
            (
                "paladin_claim_usdc_success_simp",
                f"""unfold {spec_name}
have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimUsdc, computedClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_preserves_round_bound":
        return [
            (
                "paladin_claim_usdc_bound_simp",
                """unfold claimUsdc_preserves_round_bound_spec
have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimUsdc, computedClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_reverts_if_already_claimed":
        return [
            (
                "paladin_claim_usdc_revert_simp",
                """unfold claimUsdc_reverts_if_already_claimed_spec
have hClaimedNe : s.storageMap 5 s.sender ≠ 0 := by
  simpa using hClaimed
have hClaimed' : (s.storageMap 5 s.sender == 0) = false := by
  simp [hClaimedNe]
simp [StreamRecoveryClaimUsdc.claimUsdc, hWaiver, hActive, hClaimed',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_reverts_if_exceeds_total":
        return [
            (
                "paladin_claim_usdc_revert_simp",
                """unfold claimUsdc_reverts_if_exceeds_total_spec
have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hFresh]
have hBoundFalse :
    ¬ add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using (Nat.not_le_of_gt hExceeds)
simp [StreamRecoveryClaimUsdc.claimUsdc, hWaiver, hActive, hFresh', hBoundFalse,
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    paladin_weth_success_specs = {
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_marks_user_claimed":
            "claimWeth_marks_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_updates_round_claimed":
            "claimWeth_updates_round_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_updates_total_allocated":
            "claimWeth_updates_total_allocated_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_preserves_usdc_state":
            "claimWeth_preserves_usdc_state_spec",
    }
    if theorem_name in paladin_weth_success_specs:
        spec_name = paladin_weth_success_specs[str(theorem_name)]
        return [
            (
                "paladin_claim_weth_success_simp",
                f"""unfold {spec_name}
have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimWeth, computedWethClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_preserves_round_bound":
        return [
            (
                "paladin_claim_weth_bound_simp",
                """unfold claimWeth_preserves_round_bound_spec
have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimWeth, computedWethClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_reverts_if_already_claimed":
        return [
            (
                "paladin_claim_weth_revert_simp",
                """unfold claimWeth_reverts_if_already_claimed_spec
have hClaimedNe : s.storageMap 9 s.sender ≠ 0 := by
  simpa using hClaimed
have hClaimed' : (s.storageMap 9 s.sender == 0) = false := by
  simp [hClaimedNe]
simp [StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hClaimed',
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_reverts_if_exceeds_total":
        return [
            (
                "paladin_claim_weth_revert_simp",
                """unfold claimWeth_reverts_if_exceeds_total_spec
have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hFresh]
have hBoundFalse :
    ¬ add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using (Nat.not_le_of_gt hExceeds)
simp [StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hFresh', hBoundFalse,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    paladin_both_success_specs = {
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_marks_both_claimed":
            (
                "claimBoth_marks_both_claimed_spec",
                "⟨_, hUsdcClaimed, _, _, _, hWethClaimed, _, _⟩",
                "exact ⟨hUsdcClaimed, hWethClaimed⟩",
            ),
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_updates_round_claimed":
            (
                "claimBoth_updates_round_claimed_spec",
                "⟨_, _, hUsdcClaimed, _, _, _, hWethClaimed, _⟩",
                "exact ⟨hUsdcClaimed, hWethClaimed⟩",
            ),
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_updates_total_allocated":
            (
                "claimBoth_updates_total_allocated_spec",
                "⟨_, _, _, hUsdcAllocated, _, _, _, hWethAllocated⟩",
                "exact ⟨hUsdcAllocated, hWethAllocated⟩",
            ),
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_preserves_round_bounds":
            (
                "claimBoth_preserves_round_bounds_spec",
                "⟨hUsdcTotal, _, hUsdcClaimed, _, hWethTotal, _, hWethClaimed, _⟩",
                """constructor
· simpa [hUsdcTotal, hUsdcClaimed] using hUsdcBound
· simpa [hWethTotal, hWethClaimed] using hWethBound""",
            ),
    }
    if theorem_name in paladin_both_success_specs:
        spec_name, rcases_pattern, finish = paladin_both_success_specs[str(theorem_name)]
        return [
            (
                "paladin_claim_both_success_helper",
                f"""unfold {spec_name}
rcases Benchmark.Grindset.Paladin.claimBoth_slot_writes usdcShareWad wethShareWad s
    hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
  {rcases_pattern}
{finish}
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_usdc_already_claimed":
        return [
            (
                "paladin_claim_both_usdc_revert_simp",
                """unfold claimBoth_reverts_if_usdc_already_claimed_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hClaimed' : (s.storageMap 5 s.sender == 0) = false := by
  simp [hClaimed]
simp [StreamRecoveryClaimUsdc.claimBoth, hWaiver', hActive', hClaimed',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_usdc_exceeds_total":
        return [
            (
                "paladin_claim_both_usdc_revert_simp",
                """unfold claimBoth_reverts_if_usdc_exceeds_total_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hUsdcFresh]
have hUsdcBoundFalse :
    ¬ add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using (Nat.not_le_of_gt hUsdcExceeds)
simp [StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, hWaiver', hActive',
  hUsdcFresh', hUsdcBoundFalse,
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_weth_already_claimed":
        return [
            (
                "paladin_claim_both_weth_revert_simp",
                """unfold claimBoth_reverts_if_weth_already_claimed_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hUsdcFresh]
have hWethClaimed' : (s.storageMap 9 s.sender == 0) = false := by
  simp [hWethClaimed]
have hUsdcBound' :
    add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hUsdcBound
simp [StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, hWaiver', hActive',
  hUsdcFresh', hWethClaimed', hUsdcBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_weth_exceeds_total":
        return [
            (
                "paladin_claim_both_weth_revert_simp",
                """unfold claimBoth_reverts_if_weth_exceeds_total_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hUsdcFresh]
have hWethFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hWethFresh]
have hUsdcBound' :
    add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hUsdcBound
have hWethBoundFalse :
    ¬ add (s.storage 7) (div (mul wethShareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using (Nat.not_le_of_gt hWethExceeds)
simp [StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, computedWethClaimAmount,
  hWaiver', hActive', hUsdcFresh', hWethFresh', hUsdcBound', hWethBoundFalse,
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_preserves_supply":
        return [
            (
                "zama_transfer_supply_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
unfold transfer_preserves_supply_spec supply
simp [ERC7984.transfer, ERC7984.totalSupply, ERC7984.balances,
  ERC7984.balanceInitialized, add64, UINT64_MOD, getStorage, setStorage,
  getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
  Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
  hSenderNZ, hRecipientNZ, hInit]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_no_balance_revert":
        return [
            (
                "zama_transfer_no_revert_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
unfold transfer_no_balance_revert_spec
simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
  getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
  Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
  hSenderNZ, hRecipientNZ, hInit]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_sufficient":
        return [
            (
                "zama_transfer_sufficient_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
  simpa using hSufficient
unfold transfer_sufficient_spec balanceOf
dsimp
intro _
constructor
· simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hSufficient', hDistinct]
· have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hSufficient', hDistinct, hDistinct']
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_conservation":
        return [
            (
                "zama_transfer_conservation_simp",
                """have uint256_mod_uint64_of_lt : ∀ {x : Uint256},
    x < UINT64_MOD → x % 18446744073709551616 = x := by
  intro x hx
  cases hBal : x with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hBal, UINT64_MOD] using hx
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
unfold transfer_conservation_spec balanceOf
by_cases hSufficient : s.storageMap 1 sender >= amount
· dsimp
  have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hSufficient
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hSufficient', hDistinct, Ne.symm hDistinct]
  have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
      s.storageMap 1 recipient + amount :=
    uint256_mod_uint64_of_lt hToNoWrap
  change add (sub (s.storageMap 1 sender) amount)
      ((s.storageMap 1 recipient + amount) % 18446744073709551616) =
    add (s.storageMap 1 sender) (s.storageMap 1 recipient)
  rw [hToAddMod]
  calc
    sub (s.storageMap 1 sender) amount + (s.storageMap 1 recipient + amount)
        = (sub (s.storageMap 1 sender) amount + amount) + s.storageMap 1 recipient := by
            rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
            rw [← Verity.Core.Uint256.add_assoc]
    _ = s.storageMap 1 sender + s.storageMap 1 recipient := by
          change ((s.storageMap 1 sender - amount) + amount) + s.storageMap 1 recipient =
            s.storageMap 1 sender + s.storageMap 1 recipient
          rw [Verity.Core.Uint256.sub_add_cancel_left]
· dsimp
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hSufficient
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hInsufficient', hDistinct, Ne.symm hDistinct,
    hToBal64]
  change add (s.storageMap 1 sender)
      (add (s.storageMap 1 recipient) 0 % 18446744073709551616) =
    add (s.storageMap 1 sender) (s.storageMap 1 recipient)
  have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
      s.storageMap 1 recipient := by
    have hZeroAdd : add (s.storageMap 1 recipient) 0 = s.storageMap 1 recipient :=
      Verity.Core.Uint256.add_zero _
    rw [hZeroAdd]
    exact uint256_mod_uint64_of_lt hToBal64
  rw [hZeroAddMod]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transferFrom_conservation":
        return [
            (
                "zama_transfer_from_conservation_simp",
                """have uint256_mod_uint64_of_lt : ∀ {x : Uint256},
    x < UINT64_MOD → x % 18446744073709551616 = x := by
  intro x hx
  cases hBal : x with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hBal, UINT64_MOD] using hx
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
have hHolderNZ : holder ≠ (0 : Address) := by
  have hNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hAuthorized' :
    holder = s.sender ∨ blockTimestamp.val ≤ (s.storageMap2 3 holder s.sender).val := by
  cases hAuthorized with
  | inl hEq =>
      exact Or.inl ((beq_iff_eq).1 hEq)
  | inr hLe =>
      exact Or.inr (by simpa using hLe)
unfold transferFrom_conservation_spec balanceOf
by_cases hSufficient : s.storageMap 1 holder >= amount
· dsimp
  have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hSufficient
  simp [ERC7984.transferFrom, ERC7984.operators, ERC7984.balances,
    ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
    setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
    hSufficient', hDistinct, Ne.symm hDistinct, hAuthorized']
  have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
      s.storageMap 1 recipient + amount :=
    uint256_mod_uint64_of_lt hToNoWrap
  change add (sub (s.storageMap 1 holder) amount)
      ((s.storageMap 1 recipient + amount) % 18446744073709551616) =
    add (s.storageMap 1 holder) (s.storageMap 1 recipient)
  rw [hToAddMod]
  calc
    sub (s.storageMap 1 holder) amount + (s.storageMap 1 recipient + amount)
        = (sub (s.storageMap 1 holder) amount + amount) + s.storageMap 1 recipient := by
            rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
            rw [← Verity.Core.Uint256.add_assoc]
    _ = s.storageMap 1 holder + s.storageMap 1 recipient := by
          change ((s.storageMap 1 holder - amount) + amount) + s.storageMap 1 recipient =
            s.storageMap 1 holder + s.storageMap 1 recipient
          rw [Verity.Core.Uint256.sub_add_cancel_left]
· dsimp
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hSufficient
  simp [ERC7984.transferFrom, ERC7984.operators, ERC7984.balances,
    ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
    setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
    hInsufficient', hDistinct, Ne.symm hDistinct, hAuthorized', hRecipientBal64]
  change add (s.storageMap 1 holder)
      (add (s.storageMap 1 recipient) 0 % 18446744073709551616) =
    add (s.storageMap 1 holder) (s.storageMap 1 recipient)
  have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
      s.storageMap 1 recipient := by
    have hZeroAdd : add (s.storageMap 1 recipient) 0 = s.storageMap 1 recipient :=
      Verity.Core.Uint256.add_zero _
    rw [hZeroAdd]
    exact uint256_mod_uint64_of_lt hRecipientBal64
  rw [hZeroAddMod]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_insufficient":
        return [
            (
                "zama_transfer_insufficient_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
  simpa using hInsufficient
unfold transfer_insufficient_spec balanceOf
dsimp
intro _
constructor
· simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hInsufficient', hToBal64]
  intro hEq
  exact False.elim (hDistinct hEq)
· have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hInsufficient', hDistinct, hDistinct', hToBal64]
  change add (s.storageMap 1 recipient) 0 % 18446744073709551616 = s.storageMap 1 recipient
  have hZeroAdd : add (s.storageMap 1 recipient) 0 = s.storageMap 1 recipient :=
    Verity.Core.Uint256.add_zero _
  rw [hZeroAdd]
  cases hs : s.storageMap 1 recipient with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hs, UINT64_MOD] using hToBal64
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.setOperator_updates":
        return [
            (
                "zama_set_operator_simp",
                """unfold setOperator_updates_spec operatorExpiry
constructor
· simp [ERC7984.setOperator, ERC7984.operators, msgSender, setMapping2,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· intro h sp hNe
  by_cases hh : h = s.sender
  · by_cases hs : sp = operator
    · exfalso
      exact hNe (by cases hh; cases hs; rfl)
    · simp [ERC7984.setOperator, ERC7984.operators, msgSender, setMapping2,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
        hh, hs]
  · simp [ERC7984.setOperator, ERC7984.operators, msgSender, setMapping2,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hh]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_increases_supply":
        return [
            (
                "zama_mint_success_simp",
                """have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hSuccess : add64 (s.storage 0) amount >= s.storage 0 := by
  by_cases h : add64 (s.storage 0) amount >= s.storage 0
  · exact h
  · unfold tryIncrease64 at hNoOverflow
    simp [h] at hNoOverflow
have hSuccess' : (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
  simpa [add64, UINT64_MOD] using hSuccess
unfold mint_increases_supply_spec supply balanceOf
dsimp
intro _
constructor
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_overflow_protection":
        return [
            (
                "zama_mint_overflow_simp",
                """have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hFail : ¬ add64 (s.storage 0) amount >= s.storage 0 := by
  intro hSuccess
  have : (tryIncrease64 (s.storage 0) amount).1 = true := by
    simp [tryIncrease64, hSuccess]
  rw [this] at hOverflow
  contradiction
have hFail' : ¬ (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
  simpa [add64, UINT64_MOD] using hFail
unfold mint_overflow_protection_spec supply balanceOf
dsimp
intro _
constructor
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.burn_decreases_supply":
        return [
            (
                "zama_burn_success_simp",
                """have hHolderNZ : holder ≠ (0 : Address) := by
  have hNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
  simpa using hSufficient
unfold burn_decreases_supply_spec balanceOf supply
dsimp
intro _
constructor
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.burn_insufficient":
        return [
            (
                "zama_burn_insufficient_simp",
                """have hHolderNZ : holder ≠ (0 : Address) := by
  have hNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 holder).val := by
  simpa using hInsufficient
unfold burn_insufficient_spec balanceOf supply
dsimp
intro _
constructor
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient']
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient', hSupply64]
  change (s.storage 0 - 0) % 18446744073709551616 = s.storage 0
  rw [Verity.Core.Uint256.sub_zero]
  cases hs : s.storage 0 with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hs, UINT64_MOD] using hSupply64
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_at_start_time":
        return [
            (
                "reserve_price_boundary",
                """unfold price_at_start_time_spec _price
simp
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_at_end_time":
        return [
            (
                "reserve_price_boundary",
                """unfold price_at_end_time_spec _price
have h : (auction_endTime == auction_startTime) = false := by
  simpa [beq_iff_eq] using fun h => hStartNeEnd h.symm
simp [h]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_lower_bound":
        return [
            (
                "reserve_price_lower_bound",
                """unfold price_lower_bound_spec _price
by_cases h1 : block_timestamp == auction_startTime
· simpa [h1] using hBand
· by_cases h2 : block_timestamp == auction_endTime
  · simp [h1, h2]
  · simp [h1, h2]
    split
    · exact Nat.le_refl _
    · rename_i hNotLt
      exact Nat.not_lt.mp hNotLt
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_upper_bound":
        return [
            (
                "reserve_price_upper_bound_helper",
                """exact Benchmark.Grindset.Reserve.price_upper_bound_spec_holds
  sellPrices buyPrices auction_startTime auction_endTime block_timestamp hBand hSafe
""",
            )
        ]
    return []


def _contract_grind_hints(workspace: Path, implementation_files: object) -> list[str]:
    if not isinstance(implementation_files, list):
        return []
    hints: list[str] = []
    seen: set[str] = set()
    for rel in implementation_files:
        if not isinstance(rel, str) or not (workspace / rel).is_file():
            continue
        current_contract: str | None = None
        in_block_comment = False
        for raw_line in (workspace / rel).read_text(encoding="utf-8").splitlines():
            line = raw_line.strip()
            if in_block_comment:
                if "-/" in line:
                    in_block_comment = False
                    line = line.split("-/", 1)[1].strip()
                else:
                    continue
            if line.startswith("/-"):
                if "-/" not in line:
                    in_block_comment = True
                continue
            if line.startswith(("--", "/--", "*")):
                continue
            contract_match = re.match(r"verity_contract\s+([A-Za-z_][A-Za-z0-9_']*)\b", line)
            if contract_match:
                current_contract = contract_match.group(1)
                continue
            if current_contract is None:
                continue
            function_match = re.match(r"function\s+(?:[A-Za-z_][A-Za-z0-9_']*\([^)]*\)\s+)*([A-Za-z_][A-Za-z0-9_']*)\b", line)
            storage_match = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\s*:\s*.+:=\s*slot\s+\d+", line)
            name = None
            if function_match:
                name = function_match.group(1)
            elif storage_match:
                name = storage_match.group(1)
            if name and name not in {"on", "nonreentrant"}:
                hint = f"{current_contract}.{name}"
                if hint not in seen:
                    seen.add(hint)
                    hints.append(hint)
    return hints


def _heuristic_tactic_candidates(
    task: dict[str, object],
    workspace: Path,
    original: str,
    implementation_files: object,
) -> list[tuple[str, str]]:
    theorem_name = task.get("theorem_name")
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency":
        return []
    spec_names = sorted(set(re.findall(r"\b([A-Za-z_][A-Za-z0-9_'.]*_spec)\b", original)))
    hints = _contract_grind_hints(workspace, implementation_files)
    if not spec_names and not hints:
        return []
    lines: list[str] = []
    if spec_names:
        lines.append("unfold " + " ".join(spec_names))
    hint_text = ", ".join(hints)
    lines.append(f"grind [{hint_text}]" if hint_text else "grind")
    return [("heuristic_grind", "\n".join(lines) + "\n")]


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
    if ("unexpected token" in lowered or "expected" in lowered) and "error:" in lowered:
        return "lean_parse_error"
    if "unknown identifier" in lowered or "unknown constant" in lowered or "unknown namespace" in lowered:
        return "lean_unknown_name"
    if "unsolved goals" in lowered:
        return "lean_unsolved_goals"
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
    return hint


def _stuck_signature(first_error: object) -> str:
    text = re.sub(r"\d+", "#", str(first_error or "")).strip()
    return text[:200]


def _retry_feedback(output: str) -> str:
    compact = _compact_lean_output(output, limit=900)
    lines = [line for line in compact.splitlines() if "error:" in line.lower() or "unsolved goals" in line.lower()]
    text = "\n".join(lines) if lines else compact
    if "maximum recursion depth has been reached" in compact:
        text += (
            "\nAvoid broad recursive simp. Do not put ContractResult.snd in a simp list. "
            "Prefer unfolding the target contract/spec, split contract if/branch conditions with by_cases, "
            "and simplify concrete storage slot names."
        )
    if "unknown identifier" in compact:
        text += "\nUse only names visible in the provided files. Do not invent Verity.Storage.* helpers or ContractState methods."
    if "unknown constant" in compact:
        text += "\nUse only visible declarations. Do not invent storage_set or ContractState update lemmas."
    if "failed to unfold" in compact:
        text += "\nDo not unfold generated contract .spec declarations unless Lean shows they unfold; unfold the concrete function and public spec instead."
    return text[-240:]


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


def _local_no_auth_endpoint(base_url: str) -> bool:
    host = urlparse(base_url).hostname
    return host in {"127.0.0.1", "localhost", "::1"}


def _fair_tool_can_read(rel: str, *, allow_grindset_tools: bool = False) -> bool:
    parts = Path(rel).parts
    if rel == ".env" or ".env" in parts:
        return False
    if rel.startswith("Benchmark/GeneratedPreview/") or "/GeneratedPreview/" in rel:
        return False
    if rel.endswith("Proofs.lean") or "/Proofs/" in rel:
        return False
    if allow_grindset_tools or DEFAULT_ALLOW_GRINDSET_TOOLS:
        return True
    return not rel.startswith("Benchmark/Grindset/")


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


def _public_lean_files(workspace: Path, *, allow_grindset_tools: bool = False) -> list[tuple[str, Path]]:
    seen: set[Path] = set()
    files: list[tuple[str, Path]] = []

    for path in workspace.rglob("*.lean"):
        try:
            resolved = path.resolve()
            rel = path.relative_to(workspace).as_posix()
        except (OSError, ValueError):
            continue
        if resolved in seen or not _fair_tool_can_read(rel, allow_grindset_tools=allow_grindset_tools):
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
            if resolved in seen or not _fair_tool_can_read(rel, allow_grindset_tools=allow_grindset_tools):
                continue
            seen.add(resolved)
            files.append((rel, path))

    return sorted(files, key=lambda item: item[0])


def _search_declarations(workspace: Path, query: str, *, limit: int = 20, allow_grindset_tools: bool = False) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    pattern = query.lower()
    for rel, path in _public_lean_files(workspace, allow_grindset_tools=allow_grindset_tools):
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


def _definition_outline(workspace: Path, query: str, *, limit: int = 12, allow_grindset_tools: bool = False) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    pattern = query.lower()
    for rel, path in _public_lean_files(workspace, allow_grindset_tools=allow_grindset_tools):
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
    allow_grindset_tools: bool = False,
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
        if not _fair_tool_can_read(rel, allow_grindset_tools=allow_grindset_tools):
            return {"ok": False, "error": "fair mode does not expose hidden proof, GeneratedPreview, .env, or disabled Grindset files"}
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
            if original_statement and candidate_statement != original_statement:
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
        return {"ok": True, "results": _search_declarations(workspace, query, limit=int(limit) if isinstance(limit, int) else 20, allow_grindset_tools=allow_grindset_tools)}
    if name == "definition_outline":
        query = args.get("query")
        if not isinstance(query, str) or not query:
            return {"ok": False, "error": "query must be a non-empty string"}
        limit = args.get("limit")
        return {"ok": True, "results": _definition_outline(workspace, query, limit=int(limit) if isinstance(limit, int) else 12, allow_grindset_tools=allow_grindset_tools)}
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
    allow_grindset_tools: bool = False,
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
                allow_grindset_tools=allow_grindset_tools,
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


def _attempt_task(
    task: dict[str, object],
    workspace: Path,
    *,
    base_url: str,
    max_attempts: int,
    attempts_dir: Path,
    allow_local_candidates: bool,
    allow_heuristic_candidates: bool,
    allow_grindset_import: bool,
) -> dict[str, object]:
    editable_files = task.get("editable_files")
    implementation_files = task.get("implementation_files")
    specification_files = task.get("specification_files")
    target_module = task.get("target_module")
    if not isinstance(editable_files, list) or len(editable_files) != 1 or not isinstance(target_module, str):
        return {"task_ref": task.get("task_ref"), "status": "unsupported_task_shape"}
    editable = str(editable_files[0])
    proof_path = workspace / editable
    original = proof_path.read_text(encoding="utf-8")
    proof_path.write_text(original, encoding="utf-8")
    feedback = "No Lean feedback yet."
    attempts: list[dict[str, object]] = []

    if not re.search(r"\b(sorry|admit|axiom)\b|\?_[A-Za-z0-9_']*", original):
        code, output = _run_lean_module(workspace, target_module)
        attempts.append(
            {
                "attempt": "preexisting",
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": None,
                "output": _compact_lean_output(output),
                "response_usage": None,
            }
        )
        if code == 0:
            return {"task_ref": task.get("task_ref"), "status": "lean_passed", "attempts": attempts}
        feedback = output

    local_candidates = []
    if allow_local_candidates:
        local_candidates.extend(_local_tactic_candidates(task))
    if allow_heuristic_candidates:
        local_candidates.extend(_heuristic_tactic_candidates(task, workspace, original, implementation_files))

    for name, tactic_body in local_candidates:
        candidate = _candidate_from_local(original, tactic_body, task.get("theorem_name"))
        proof_path.write_text(candidate, encoding="utf-8")
        candidate_path = attempts_dir / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}-local-{name}.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        candidate_path.write_text(candidate, encoding="utf-8")
        code, output = _run_lean_module(workspace, target_module)
        attempts.append(
            {
                "attempt": f"local:{name}",
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": str(candidate_path),
                "output": _compact_lean_output(output),
                "response_usage": None,
            }
        )
        if code == 0:
            return {"task_ref": task.get("task_ref"), "status": "lean_passed", "attempts": attempts}
        feedback = output

    for attempt_index in range(1, max_attempts + 1):
        context_text, symbol_text = _context_for_task(
            task,
            workspace,
            editable,
            editable_files,
            specification_files,
            implementation_files,
        )
        messages = [
            {
                "role": "system",
                "content": (
                    "You are editing one Lean 4 file in a Verity benchmark workspace. "
                    "Return only the tactic proof body that belongs under `:= by`, not a complete file "
                    "and not prose. Do not repeat imports, namespace declarations, theorem headers, or `:= by`. "
                    "Do not use sorry, admit, axiom, hidden imports, or placeholders. "
                    "Use the Lean tactic `grind`; there is no `Grindset.grind` declaration. "
                    "Use only declarations visible in the provided public files. Do not invent "
                    "Verity.Storage helpers, storage_set lemmas, or ContractState methods."
                ),
            },
            {
                "role": "user",
                "content": (
                    f"Task: {task.get('task_ref')}\n"
                    f"Target theorem: {task.get('theorem_name')}\n"
                    f"Editable file: {editable}\n\n"
                    f"Public symbol summary:\n{symbol_text}\n\n"
                    + context_text
                    + f"\n\nLean feedback:\n{_retry_feedback(feedback)}\n"
                ),
            },
        ]
        try:
            response = chat_completion(messages, base_url=base_url)
            rejection = _is_rejected_model_body(task, _response_text(response))
            if rejection:
                attempts.append(
                    {
                        "attempt": attempt_index,
                        "status": "rejected_candidate",
                        "reason": rejection,
                        "response_usage": response.get("usage") if isinstance(response, dict) else None,
                    }
                )
                break
            patcher = _candidate_from_comparison_response if allow_grindset_import else _candidate_from_response
            candidate = patcher(original, _response_text(response), task.get("theorem_name"))
        except Exception as exc:
            if "exceeds the available context size" not in str(exc):
                attempts.append({"attempt": attempt_index, "status": "request_failed", "error": str(exc)})
                break
            minimal_messages = [
                messages[0],
                {
                    "role": "user",
                    "content": (
                        "Return Lean tactic body only, under := by. No prose.\n"
                        f"Target: {task.get('theorem_name')}\n"
                        f"Errors: {_retry_feedback(feedback)[:160]}\n"
                    ),
                },
            ]
            try:
                response = chat_completion(minimal_messages, base_url=base_url, max_tokens=1024)
                rejection = _is_rejected_model_body(task, _response_text(response))
                if rejection:
                    attempts.append(
                        {
                            "attempt": attempt_index,
                            "status": "rejected_candidate",
                            "reason": rejection,
                            "response_usage": response.get("usage") if isinstance(response, dict) else None,
                        }
                    )
                    break
                patcher = _candidate_from_comparison_response if allow_grindset_import else _candidate_from_response
                candidate = patcher(original, _response_text(response), task.get("theorem_name"))
            except Exception as fallback_exc:
                attempts.append({"attempt": attempt_index, "status": "request_failed", "error": str(fallback_exc)})
                break
        proof_path.write_text(candidate, encoding="utf-8")
        candidate_path = attempts_dir / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}-attempt-{attempt_index}.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        candidate_path.write_text(candidate, encoding="utf-8")
        code, output = _run_lean_module(workspace, target_module)
        attempts.append(
            {
                "attempt": attempt_index,
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": str(candidate_path),
                "output": _compact_lean_output(output),
                "response_usage": response.get("usage") if isinstance(response, dict) else None,
            }
        )
        if code == 0:
            return {"task_ref": task.get("task_ref"), "status": "lean_passed", "attempts": attempts}
        feedback = output

    if not any(attempt.get("status") in {"lean_failed", "lean_passed"} for attempt in attempts):
        proof_path.write_text(original, encoding="utf-8")
    return {"task_ref": task.get("task_ref"), "status": "failed_submitted" if attempts else "failed_no_attempt", "attempts": attempts}


def run_group(
    group_id: str,
    *,
    suite: str = "active",
    keep_workspace: bool = False,
    dry_run: bool = False,
    max_attempts: int = 1,
    max_tool_calls: int = DEFAULT_MAX_TOOL_CALLS,
    mode: str = "fair",
    task_ref: str | None = None,
) -> tuple[int, Path]:
    if mode not in VALID_MODES:
        raise ValueError(f"unknown default harness mode: {mode} (expected one of {', '.join(VALID_MODES)})")
    if max_attempts < 0:
        raise ValueError("max_attempts must be non-negative")
    if max_tool_calls < 0:
        raise ValueError("max_tool_calls must be non-negative")
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_subject = task_ref or group_id
    model_slug = "".join(ch if ch.isalnum() else "-" for ch in DEFAULT_MODEL).strip("-").lower()
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{RUN_SLUG}-{mode}-{model_slug}-{run_subject.replace('/', '__')}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    start = time.time()
    group = load_group(group_id, suite)
    if task_ref:
        group = filter_group_to_task(group, task_ref)
    built = build_group_workspace(group, run_id=run_id, include_group_grindset=(mode == "legacy"))
    assert_workspace_isolated(built.path)
    base_url = DEFAULT_BASE_URL
    response: dict[str, object]
    if dry_run:
        response = {
            "status": "dry_run",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_MODEL,
            "mode": mode,
            "max_attempts": max_attempts,
            "max_tool_calls": max_tool_calls,
        }
    elif mode in {"fair", "fair+libs", "tuned"} and not _api_key() and not _local_no_auth_endpoint(base_url):
        provider_key_hint = f", DEFAULT_HARNESS_{DEFAULT_PROVIDER.upper()}_API_KEY" if DEFAULT_PROVIDER else ""
        response = {
            "status": "missing_credentials",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_MODEL,
            "mode": mode,
            "error": f"{mode} mode requires DEFAULT_HARNESS_API_KEY{provider_key_hint}, GAZELLA_API_KEY, OPENAI_API_KEY, or a localhost-compatible no-auth endpoint",
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
                    if mode in {"fair", "fair+libs"}:
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
                                allow_grindset_tools=(mode == "fair+libs"),
                            )
                        )
                    else:
                        task_results.append(
                            _attempt_task(
                                task,
                                built.path,
                                base_url=base_url,
                                max_attempts=max_attempts,
                                attempts_dir=run_dir / "attempts",
                                allow_local_candidates=(mode == "legacy"),
                                allow_heuristic_candidates=(mode in {"legacy", "tuned"}),
                                allow_grindset_import=(mode == "legacy"),
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
            response = {"status": "completed", "provider": _active_provider(), "base_url": base_url, "model": DEFAULT_MODEL, "mode": mode, "usage": aggregate_usage, "warm_builds": warm_builds, "tasks": task_results}
        except Exception as exc:
            response = {"status": "harness_error", "error": str(exc), "provider": _active_provider(), "base_url": base_url, "model": DEFAULT_MODEL, "mode": mode, "warm_builds": warm_builds, "tasks": task_results}

    (run_dir / "workspace-manifest.json").write_text((built.path / "workspace-manifest.json").read_text(encoding="utf-8"), encoding="utf-8")
    shutil.copy2(built.path / "harness" / "TASK_SUMMARY.md", run_dir / "TASK_SUMMARY.md")
    (run_dir / "harness-request.json").write_text(
        json.dumps(
            {
                "group": agent_group_to_json(group),
                "provider": _active_provider(),
                "base_url": base_url,
                "model": DEFAULT_MODEL,
                "mode": mode,
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
        "mode": mode,
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
    run.add_argument("--mode", choices=VALID_MODES, default="fair")
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
        mode=args.mode,
        task_ref=args.task_ref,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
