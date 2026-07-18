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
    from .. import transport
    from ..classification import classify_run
    from ..lean_lsp_mcp_client import (
        LeanLspMcpError,
        LeanLspMcpSession,
        LeanLspMcpTransportError,
    )
    from ..manifests import Group, filter_group_to_task, load_group
    from ..paths import RESULTS_DIR, ROOT
    from ..reports import write_run_report
    from ..verifier import setup_failure_verifier_result, verify_group
    from ..workspace_builder import (
        agent_group_to_json,
        assert_workspace_isolated,
        build_group_workspace,
        warm_public_dependencies,
        warm_result_failed,
    )
except ImportError:
    import transport
    from classification import classify_run
    from lean_lsp_mcp_client import (
        LeanLspMcpError,
        LeanLspMcpSession,
        LeanLspMcpTransportError,
    )
    from manifests import Group, filter_group_to_task, load_group
    from paths import RESULTS_DIR, ROOT
    from reports import write_run_report
    from verifier import setup_failure_verifier_result, verify_group
    from workspace_builder import (
        agent_group_to_json,
        assert_workspace_isolated,
        build_group_workspace,
        warm_public_dependencies,
        warm_result_failed,
    )

try:
    from ..transport import (
        ChatCompletionError, DEFAULT_BASE_URL, DEFAULT_MODEL, DEFAULT_PROVIDER, HTTP_USER_AGENT,
        _active_provider, _api_key, _harness_env, _local_no_auth_endpoint, _logged_response_message,
        _response_text, _append_jsonl, _effective_sampling, _streaming_fallback_reason, _transport_mode,
        chat_completion, endpoint_smoke, generic_preflight,
    )
    from ..budgets import dependency_warm_timeout_seconds, operational_budget
    from ..lean_check import (
        FAILURE_HINTS, LEAN_CHECK_MODE, LEAN_CHECK_TIMEOUT_SECONDS, _classify_lean_failure,
        _compact_lean_output, _constants_from_text, _extract_goal_blocks, _first_meaningful_lean_error,
        _goal_diagnostics, _hint_for_failure, _proof_result_diagnostics, _run_lean_command,
        _split_goal_context,
    )
    from ..proof_patch import (
        FORBIDDEN_PROOF_RE, _candidate_from_response, _contains_forbidden_proof_token, _decl_basename,
        _extract_lean_file, _full_file_context_preserved, _indent_proof_body, _looks_like_full_file, _patch_proof_body,
        _strip_thinking, _theorem_statement,
    )
    from ..result_validity import failure_counts_from_tasks, failure_taxonomy, row_validity
    from ..symbols import public_symbol_summary as _public_symbol_summary
except ImportError:
    from transport import (
        ChatCompletionError, DEFAULT_BASE_URL, DEFAULT_MODEL, DEFAULT_PROVIDER, HTTP_USER_AGENT,
        _active_provider, _api_key, _harness_env, _local_no_auth_endpoint, _logged_response_message,
        _response_text, _append_jsonl, _effective_sampling, _streaming_fallback_reason, _transport_mode,
        chat_completion, endpoint_smoke, generic_preflight,
    )
    from budgets import dependency_warm_timeout_seconds, operational_budget
    from lean_check import (
        FAILURE_HINTS, LEAN_CHECK_MODE, LEAN_CHECK_TIMEOUT_SECONDS, _classify_lean_failure,
        _compact_lean_output, _constants_from_text, _extract_goal_blocks, _first_meaningful_lean_error,
        _goal_diagnostics, _hint_for_failure, _proof_result_diagnostics, _run_lean_command,
        _split_goal_context,
    )
    from proof_patch import (
        FORBIDDEN_PROOF_RE, _candidate_from_response, _contains_forbidden_proof_token, _decl_basename,
        _extract_lean_file, _full_file_context_preserved, _indent_proof_body, _looks_like_full_file, _patch_proof_body,
        _strip_thinking, _theorem_statement,
    )
    from result_validity import failure_counts_from_tasks, failure_taxonomy, row_validity
    from symbols import public_symbol_summary as _public_symbol_summary


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
DEFAULT_MAX_FAIR_MESSAGES = int(os.environ.get("DEFAULT_HARNESS_MAX_FAIR_MESSAGES", "16"))
DEFAULT_CONTEXT_STOP_FRACTION = float(os.environ.get("DEFAULT_HARNESS_CONTEXT_STOP_FRACTION", "0.88"))
DEFAULT_TOKEN_BUDGET = int(os.environ.get("DEFAULT_HARNESS_TOKEN_BUDGET", "0"))  # 0 = unlimited; counts completion tokens per task
STUCK_NUDGE = os.environ.get("DEFAULT_HARNESS_STUCK_NUDGE", "1").lower() not in {"0", "false", "no"}
DEFAULT_DRIVER_MODEL = os.environ.get("DEFAULT_HARNESS_DRIVER_MODEL", DEFAULT_MODEL).strip() or DEFAULT_MODEL
DEFAULT_PROVER_MODEL = os.environ.get("DEFAULT_HARNESS_PROVER_MODEL", "").strip()
DEFAULT_PROVER_MODE = os.environ.get("DEFAULT_HARNESS_PROVER_MODE", "").strip().lower()
# Optional prover-specific OpenAI-compatible endpoint. Unset values fall back to
# the driver endpoint so single-endpoint hybrid runs keep working unchanged. When
# set, the driver/tool loop still uses DEFAULT_HARNESS_BASE_URL/API_KEY while the
# draft_proof prover routes to this cross-provider endpoint (e.g. MiniMax driver
# controlling tools, Leanstral prover drafting proof bodies on a second provider).
DEFAULT_PROVER_BASE_URL = os.environ.get("DEFAULT_HARNESS_PROVER_BASE_URL", "").strip()
DEFAULT_PROVER_API_KEY = os.environ.get("DEFAULT_HARNESS_PROVER_API_KEY", "").strip()
DRAFT_PROOF_ENABLED = DEFAULT_PROVER_MODE == "draft_proof" and bool(DEFAULT_PROVER_MODEL)
DRAFT_PROOF_CONTEXT_CHARS = int(os.environ.get("DEFAULT_HARNESS_DRAFT_PROOF_CONTEXT_CHARS", "12000"))
# Strict driver/prover role separation for hybrid draft_proof runs. When enabled
# (and draft_proof is active), the driver model is treated as a pure orchestrator
# (context_builder): it never writes or edits proof bodies itself. All proof
# bodies come from the prover model in two explicit stages - prover_writer for the
# first draft and proof_repairer for bounded minimal-edit repairs after a failed
# Lean check. This keeps hybrid ensemble scores honest: the driver's own Lean
# ability is never mixed into the recorded result. Backward compatible: defaults
# off, so existing draft_proof runs keep the driver-side diagnostic repair loop.
STRICT_ROLE_SEPARATION = (
    os.environ.get("DEFAULT_HARNESS_STRICT_ROLE_SEPARATION", "0").lower() in {"1", "true", "yes"}
    and DRAFT_PROOF_ENABLED
)
# Maximum number of proof_repairer (prover repair-mode) calls per task. 0 disables
# prover repairs and leaves only the initial prover_writer draft.
PROVER_REPAIR_ATTEMPTS = max(0, int(os.environ.get("DEFAULT_HARNESS_PROVER_REPAIR_ATTEMPTS", "2")))
# Bounded, content-free public declaration index injected into prover prompts to
# curb invented theorem names. Public declarations only (never hidden Proofs/
# GeneratedPreview). 0 disables the index.
DRAFT_PROOF_DECL_INDEX_LIMIT = max(0, int(os.environ.get("DEFAULT_HARNESS_DRAFT_PROOF_DECL_INDEX", "40")))
# After a failed check_proof/try_tactics attempt, replace the accumulated group
# transcript with a compact, model-agnostic repair prompt (current candidate +
# Lean errors/goal + target names + a strict "modify the existing proof"
# instruction). Keeps the next request small and focused for both strict
# providers and frontier chat models. Disable with DEFAULT_HARNESS_DIAGNOSTIC_RETRY=0.
DIAGNOSTIC_RETRY_ENABLED = os.environ.get("DEFAULT_HARNESS_DIAGNOSTIC_RETRY", "1").lower() not in {"0", "false", "no"}
REPAIR_PROMPT_CANDIDATE_CHARS = int(os.environ.get("DEFAULT_HARNESS_REPAIR_PROMPT_CANDIDATE_CHARS", "4000"))
REPAIR_PROMPT_ERROR_CHARS = int(os.environ.get("DEFAULT_HARNESS_REPAIR_PROMPT_ERROR_CHARS", "2500"))
# Generic, content-free nudge appended to the repair prompt when a proof failed
# via automation-heavy tactics (grind/broad simp/timeout/recursion). Points the
# model at a minimal explicit proof instead of leaking any task-specific answer.
# Disable with DEFAULT_HARNESS_MINIMAL_PROOF_HINT=0.
MINIMAL_PROOF_HINT_ENABLED = os.environ.get("DEFAULT_HARNESS_MINIMAL_PROOF_HINT", "1").lower() not in {"0", "false", "no"}
MINIMAL_PROOF_HINT = (
    "Fallback: if heavy automation (grind, Grindset, or a broad simp over the whole contract) keeps failing "
    "or timing out, drop it and build a minimal explicit proof instead - intro the hypotheses, unfold the "
    "*_spec definition and the concrete contract function, then close each branch with a small `simp only` on "
    "the named lemmas, `rfl`, or `decide`. Prefer the smallest proof Lean accepts over more automation."
)
AUTOMATION_FALLBACK_KINDS = {"lean_timeout", "lean_unsolved_goals", "lean_error"}
AUTOMATION_FALLBACK_MARKERS = ("maximum recursion depth", "grind", "deterministic timeout", "simp made no progress")
# The base system prompt tells the model to call show_task first; after the
# repair reset drops the transcript, that instruction would outrank the user
# message and send the model back to inspection tools. Override it explicitly.
REPAIR_SYSTEM_SUFFIX = (
    " REPAIR MODE: you already called show_task and inspected the task earlier in this session; the user "
    "message below contains the current proof and the Lean diagnostics. Ignore the instruction above to call "
    "show_task first - do not call show_task or other inspection tools again. Repair the proof and submit it "
    "with a single check_proof call."
)

# Explicit hybrid stages. The driver/context_builder orchestrates tools and
# assembles context; the prover_writer drafts the first proof body; the
# proof_repairer edits a failed proof; the verifier/checker runs Lean. Recorded in
# artifacts so ensemble runs can be compared honestly by role.
STAGE_DRIVER = "context_builder"
STAGE_WRITER = "prover_writer"
STAGE_REPAIRER = "proof_repairer"
STAGE_VERIFIER = "verifier"
PROVER_PROMPT_KINDS = {"write": STAGE_WRITER, "repair": STAGE_REPAIRER}
# When strict role separation is on, the driver is told to route every failed
# proof to the prover repairer instead of editing the proof itself.
STRICT_DRIVER_REPAIR_NUDGE = (
    "STRICT ROLE SEPARATION: you are the orchestrator only and must not write or edit Lean proof bodies "
    "yourself. The last proof from the prover did not pass Lean. Call draft_proof with "
    '{"mode":"repair"} to ask the prover for a minimal repair of the current proof, then submit the '
    "returned body verbatim with check_proof."
)


def _role_config() -> dict[str, object]:
    """Publication-honest description of which model plays which role.

    ``role_label`` is a human-readable ensemble tag so a hybrid driver+prover
    result is never confused with a standalone writer-model score.
    """
    driver = DEFAULT_DRIVER_MODEL
    prover = DEFAULT_PROVER_MODEL or None
    if DRAFT_PROOF_ENABLED and prover:
        writer = repairer = prover
        ensemble = prover != driver
    else:
        writer = repairer = driver
        ensemble = False
    if STRICT_ROLE_SEPARATION:
        driver_writes_proofs = False
        role_label = f"strict-hybrid: driver={driver}; writer={writer}; repairer={repairer}"
    elif DRAFT_PROOF_ENABLED and prover:
        # Non-strict hybrid: the driver may still edit proofs via diagnostic retry.
        driver_writes_proofs = True
        role_label = f"hybrid: driver={driver}; prover={prover}; driver_may_repair"
    else:
        driver_writes_proofs = True
        role_label = f"standalone: {driver}"
    return {
        "strict_role_separation": STRICT_ROLE_SEPARATION,
        "draft_proof_enabled": DRAFT_PROOF_ENABLED,
        "ensemble": ensemble,
        "driver_writes_proofs": driver_writes_proofs,
        "driver_model": driver,
        "prover_model": prover,
        "prover_mode": DEFAULT_PROVER_MODE or None,
        "prover_repair_attempts": PROVER_REPAIR_ATTEMPTS if STRICT_ROLE_SEPARATION else 0,
        "sampling": {
            "driver": _effective_sampling(),
            "prover": _effective_sampling(PROVER_SAMPLING or None)
            if DRAFT_PROOF_ENABLED and prover
            else None,
        },
        "stages": {
            STAGE_DRIVER: driver,
            STAGE_WRITER: writer,
            STAGE_REPAIRER: repairer,
            STAGE_VERIFIER: "lean",
        },
        "role_label": role_label,
    }


def _provider_setup_task_rows(
    group: Group,
    benchmark_budget: dict[str, object],
    error: str,
) -> list[dict[str, object]]:
    return [
        {
            "task_ref": task.task_ref,
            "status": "preflight_failed",
            "failure_class": "provider_setup_error",
            "provider_setup_error": True,
            "error": {"kind": "provider_setup_error", "message": error},
            "attempts": [],
            "benchmark_budget": benchmark_budget,
            "usage": {
                "prompt_tokens": 0,
                "completion_tokens": 0,
                "total_tokens": 0,
                "requests": 0,
            },
        }
        for task in group.tasks
    ]


def _warm_target_modules(
    *,
    workspace: Path,
    run_dir: Path,
    tasks: list[object],
    timeout_seconds: int,
) -> list[dict[str, object]]:
    """Warm target modules, stopping once the setup is known invalid."""
    results: list[dict[str, object]] = []
    for task in tasks:
        module = task.get("target_module") if isinstance(task, dict) else None
        if not isinstance(module, str) or not module:
            continue
        warm_start = time.time()
        print(f"[target-warm] module={module} state=starting", flush=True)
        warm_code, warm_output = _run_lean_module(
            workspace, module, timeout_seconds=timeout_seconds
        )
        with (run_dir / "target-warm.log").open("a", encoding="utf-8") as handle:
            handle.write(f"\n$ lake build {module}\n{warm_output}\n")
        duration = round(time.time() - warm_start, 3)
        print(
            f"[target-warm] module={module} state=finished exit_code={warm_code} "
            f"duration_seconds={duration}",
            flush=True,
        )
        results.append(
            {
                "task_ref": task.get("task_ref"),
                "module": module,
                "exit_code": warm_code,
                "duration_seconds": duration,
            }
        )
        if warm_code == 124:
            break
    return results


ROLE_METRIC_COUNTERS = (
    "prover_writer_calls",
    "prover_repair_calls",
    "draft_valid_syntax_count",
    "draft_rejected_count",
    "draft_normalized_count",
    "draft_submitted_count",
    "lean_check_failed_count",
    "repair_no_submission",
    "repair_blocked_no_failure",
    "repair_improved",
    "repair_improved_no_baseline",
    "repair_regressed",
    "repair_no_change",
    "strict_submission_blocked",
    "strict_context_blocked",
)


def _normalize_proof_body(text: str) -> str:
    """Whitespace-insensitive form used to match a submission against prover
    drafts, so re-indentation never defeats strict-mode enforcement."""
    return " ".join(text.split())


_TACTIC_LINE_RE = re.compile(
    r"^\s*(?:simp\b|ring\b|omega\b|decide\b|rfl\b|exact\b|apply\b|intro\b|intros\b|rw\b|rewrite\b"
    r"|unfold\b|constructor\b|rcases\b|induction\b|obtain\b|refine\b|calc\b|linarith\b|nlinarith\b"
    r"|norm_num\b|aesop\b|field_simp\b|positivity\b)",
    re.MULTILINE,
)


def _strict_context_proof_reason(text: str) -> str | None:
    """Reject driver-supplied prover context that looks like a Lean proof.

    In strict mode the driver is a context builder only; letting it pass a
    tactic script through task_context would let the prover echo driver-authored
    Lean back as a "draft". Heuristic and conservative: declarative summaries,
    goal displays, and declaration names all pass."""
    if ":= by" in text:
        return "strict_context_contains_proof_assignment"
    if "```" in text:
        return "strict_context_contains_markdown_fence"
    if len(_TACTIC_LINE_RE.findall(text)) >= 2:
        return "strict_context_contains_tactic_script"
    return None


def _strict_auto_writer_context(*, task: dict[str, object], workspace: Path, original: str) -> str:
    """Trusted context for the strict liveness bridge.

    This is deliberately built only from task metadata and workspace files, never
    from the driver's rejected proof text or free-form tool arguments.
    """
    lines = [
        "The driver attempted to submit before obtaining a prover draft. Produce the initial proof body.",
        f"Task metadata: {json.dumps(_task_public_view(task), sort_keys=True)}",
    ]
    theorem = _theorem_statement(original, task.get("theorem_name")).strip()
    if theorem:
        lines += ["Target theorem statement:", theorem]
    summary_path = workspace / "harness" / "TASK_SUMMARY.md"
    if summary_path.is_file():
        try:
            summary = _task_summary_with_live_editable(
                summary_path.read_text(encoding="utf-8"),
                task=task,
                workspace=workspace,
            )
            if summary.strip():
                lines += ["Task summary:", summary[-DEFAULT_TASK_SUMMARY_CHARS:]]
        except (OSError, UnicodeDecodeError):
            pass
    return "\n".join(lines)


def _aggregate_role_metrics(task_results: list[dict[str, object]]) -> dict[str, object]:
    """Sum per-task role_metrics counters into a run-level total for honest,
    per-role reporting of a hybrid ensemble run."""
    totals = {key: 0 for key in ROLE_METRIC_COUNTERS}
    for task_result in task_results:
        metrics = task_result.get("role_metrics") if isinstance(task_result, dict) else None
        if not isinstance(metrics, dict):
            continue
        for key in ROLE_METRIC_COUNTERS:
            value = metrics.get(key)
            if isinstance(value, (int, float)):
                totals[key] += int(value)
    totals["role_config"] = _role_config()
    return totals


def _native_tools_for_preflight(preflight: dict[str, object]) -> bool:
    """Select the tool protocol from observed provider capabilities."""
    if not DEFAULT_NATIVE_TOOLS:
        return False
    checks = preflight.get("checks")
    if not isinstance(checks, dict):
        return True
    if checks.get("tool_calls") is False and checks.get("json_text_fallback") is True:
        return False
    return True


def _role_provider_preflight(base_url: str) -> dict[str, object]:
    """Preflight every model endpoint required by the configured role graph."""

    def run_role(
        role: str,
        role_base_url: str,
        model: str,
        api_key_override: str | None = None,
    ) -> dict[str, object]:
        try:
            result = generic_preflight(
                role_base_url,
                model,
                api_key_override=api_key_override,
            )
        except Exception as exc:  # noqa: BLE001 - normalize setup failures into artifacts
            result = {
                "status": "failed",
                "base_url": role_base_url,
                "model": model,
                "error": str(exc),
                "usage": {
                    "prompt_tokens": 0,
                    "completion_tokens": 0,
                    "total_tokens": 0,
                    "requests": 0,
                },
            }
        result["role"] = role
        return result

    driver = run_role("driver", base_url, DEFAULT_DRIVER_MODEL)
    combined = dict(driver)
    roles: dict[str, dict[str, object]] = {"driver": driver}

    if DRAFT_PROOF_ENABLED and DEFAULT_PROVER_MODEL:
        prover_base_url = DEFAULT_PROVER_BASE_URL or base_url
        if DEFAULT_PROVER_API_KEY:
            prover_api_key_override: str | None = DEFAULT_PROVER_API_KEY
        elif prover_base_url.rstrip("/") == base_url.rstrip("/"):
            prover_api_key_override = None
        else:
            prover_api_key_override = ""
        roles["prover"] = run_role(
            "prover",
            prover_base_url,
            DEFAULT_PROVER_MODEL,
            prover_api_key_override,
        )

    combined["roles"] = roles
    combined["status"] = (
        "passed"
        if all(result.get("status") == "passed" for result in roles.values())
        else "failed"
    )
    if combined["status"] != "passed":
        failures = [
            f"{role}: {result.get('error') or result}"
            for role, result in roles.items()
            if result.get("status") != "passed"
        ]
        combined["error"] = "; ".join(failures)
    aggregate_usage = {
        "prompt_tokens": 0,
        "completion_tokens": 0,
        "total_tokens": 0,
        "requests": 0,
    }
    for result in roles.values():
        usage = result.get("usage")
        if not isinstance(usage, dict):
            continue
        for key in aggregate_usage:
            value = usage.get(key)
            if isinstance(value, (int, float)):
                aggregate_usage[key] += int(value)
    combined["usage"] = aggregate_usage
    return combined


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
        if code == 0:
            build_code, build_output = _run_lean_command(workspace, ["lake", "build", module], timeout_seconds)
            if build_code != 0:
                combined = output
                if combined:
                    combined += "\n"
                combined += build_output
                return build_code, combined
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
    return failure_taxonomy(status, attempts, tool_calls=tool_calls, no_tool_responses=no_tool_responses)


def _tool_call_signature(name: str, args: dict[str, object]) -> str:
    try:
        encoded_args = json.dumps(args, sort_keys=True, separators=(",", ":"))
    except TypeError:
        encoded_args = str(args)
    return f"{name}:{encoded_args}"


def _compact_fair_messages(messages: list[dict[str, Any]], *, system_prompt: str, user_prompt: str) -> None:
    if DEFAULT_MAX_FAIR_MESSAGES <= 0 or len(messages) <= DEFAULT_MAX_FAIR_MESSAGES:
        return
    snippets: list[str] = []
    for message in messages[-6:]:
        role = str(message.get("role") or "")
        if role == "system":
            continue
        content = message.get("content")
        if content is None and message.get("tool_calls"):
            content = "[assistant requested tool call]"
        if content is None:
            continue
        text = str(content).replace("\n", " ")
        snippets.append(f"{role}: {text[:500]}")
    recent_summary = "\n".join(snippets[-6:])
    messages[:] = [
        {"role": "system", "content": system_prompt},
        {
            "role": "user",
            "content": (
                f"{user_prompt}\n"
                "Earlier tool transcript was compacted to keep the request within context. "
                "Recent context:\n"
                f"{recent_summary}\n"
                "Continue with one allowed tool call and make progress toward check_proof/try_tactics."
            ),
        },
    ]


def _stuck_signature(first_error: object) -> str:
    text = re.sub(r"\d+", "#", str(first_error or "")).strip()
    return text[:200]


def _minimal_proof_hint_applies(attempt: dict[str, Any]) -> bool:
    """Whether an automation-heavy failure should get the minimal-proof nudge.

    Generic and content-free: triggers on timeout/recursion/grind-style failure
    kinds and markers, never on the task identity, so it cannot leak a solution.
    """
    failure_kind = str(attempt.get("failure_kind") or "")
    diagnostics = attempt.get("diagnostics")
    if isinstance(diagnostics, dict) and not failure_kind:
        failure_kind = str(diagnostics.get("failure_kind") or "")
    output = str(attempt.get("output") or "").lower()
    if failure_kind in AUTOMATION_FALLBACK_KINDS:
        return True
    return any(marker in output for marker in AUTOMATION_FALLBACK_MARKERS)


def _repair_prompt_user_content(
    *,
    task: dict[str, Any],
    editable: str,
    candidate: str,
    attempt: dict[str, Any],
    minimal_hint: bool,
) -> str:
    diagnostics = attempt.get("diagnostics") if isinstance(attempt.get("diagnostics"), dict) else {}
    first_error = str(diagnostics.get("first_error") or attempt.get("failure_kind") or "").strip()
    goal = str(diagnostics.get("new_goal") or diagnostics.get("target") or "").strip()
    hypotheses = diagnostics.get("local_hypotheses") if isinstance(diagnostics, dict) else None
    output = str(attempt.get("output") or "").strip()
    hint = str(attempt.get("hint") or "").strip()
    theorem_name = str(task.get("theorem_name") or "").strip()
    spec_files = task.get("specification_files")
    candidate_block = candidate.rstrip()
    if len(candidate_block) > REPAIR_PROMPT_CANDIDATE_CHARS:
        candidate_block = candidate_block[:REPAIR_PROMPT_CANDIDATE_CHARS] + "\n-- [candidate truncated for repair prompt] --"
    if len(output) > REPAIR_PROMPT_ERROR_CHARS:
        output = output[-REPAIR_PROMPT_ERROR_CHARS:]

    lines: list[str] = [
        f"Your last proof attempt for task {task.get('task_ref')} did not pass Lean. "
        "Repair the existing proof - do not restart from scratch, re-read the task summary, or call other inspection tools first.",
        "",
    ]
    if theorem_name:
        lines.append(f"Target theorem: {theorem_name}")
    if isinstance(spec_files, list) and spec_files:
        lines.append("Specification files: " + ", ".join(str(item) for item in spec_files))
    lines.append(f"Editable file: {editable}")
    lines += [
        "",
        "Current proof (edit this; keep the theorem statement byte-identical, only change the body after := by):",
        "```lean",
        candidate_block,
        "```",
        "",
    ]
    if first_error:
        lines += ["Lean first error:", first_error, ""]
    if output and output != first_error:
        lines += ["Lean output:", output, ""]
    if goal:
        lines += ["Remaining goal:", goal, ""]
    if isinstance(hypotheses, list) and hypotheses:
        lines += ["Local hypotheses:", "\n".join(str(item) for item in hypotheses[:20]), ""]
    if hint:
        lines += ["Fix hint:", hint, ""]
    if minimal_hint and _minimal_proof_hint_applies(attempt):
        lines += [MINIMAL_PROOF_HINT, ""]
    lines.append("Submit the corrected proof with a single check_proof call.")
    return "\n".join(lines).rstrip() + "\n"


def _diagnostic_repair_messages(
    *,
    system_prompt: str,
    task: dict[str, Any],
    editable: str,
    candidate: str,
    attempt: dict[str, Any],
    minimal_hint: bool = MINIMAL_PROOF_HINT_ENABLED,
) -> list[dict[str, Any]]:
    """Compact [system, user] messages that focus the model on repairing the
    last failed proof, dropping the accumulated group transcript."""
    return [
        {"role": "system", "content": system_prompt + REPAIR_SYSTEM_SUFFIX},
        {
            "role": "user",
            "content": _repair_prompt_user_content(
                task=task,
                editable=editable,
                candidate=candidate,
                attempt=attempt,
                minimal_hint=minimal_hint,
            ),
        },
    ]


def _last_failed_proof_attempt(result: dict[str, object]) -> dict[str, Any] | None:
    """The most recent gradeable-or-rejected proof attempt from a check_proof/
    try_tactics result that did not pass, if any."""
    results = result.get("results")
    if not isinstance(results, list):
        return None
    for attempt in reversed(results):
        if isinstance(attempt, dict) and attempt.get("status") != "lean_passed":
            return attempt
    return None


def _classify_repair_outcome(baseline: dict[str, object] | None, attempt: dict[str, object]) -> str:
    """Compare a post-repair proof attempt against the pre-repair failure.

    Deliberately conservative so hybrid ensemble metrics never over-claim: only a
    proof that actually passes Lean counts as ``improved``. A repair that fails to
    reach Lean (rejected) or newly fails to parse is a ``regressed``. Everything
    else - including a still-failing proof with a changed error - is ``no_change``.
    """
    status = str(attempt.get("status") or "")
    if status == "lean_passed":
        return "improved"
    if status.startswith("rejected"):
        return "regressed"
    new_kind = attempt.get("failure_kind") or (attempt.get("diagnostics") or {}).get("failure_kind")
    base_kind = None
    if isinstance(baseline, dict):
        base_kind = baseline.get("failure_kind") or (baseline.get("diagnostics") or {}).get("failure_kind")
    if new_kind == "lean_parse_error" and base_kind != "lean_parse_error":
        return "regressed"
    return "no_change"


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

DRAFT_PROOF_TOOL: dict[str, Any] = {
    "type": "function",
    "function": {
        "name": "draft_proof",
        "description": (
            "Ask the configured prover model for one Lean proof-body candidate. "
            "mode='write' (default) drafts a fresh proof from task_context/goal; task_context is required for mode='write'. "
            "mode='repair' asks for a minimal edit of the current failing proof given the Lean errors and needs no other arguments. "
            "This does not check Lean and does not count as a proof attempt; use check_proof or try_tactics to submit it."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "task_context": {"type": "string"},
                "goal": {"type": "string"},
                "errors": {"type": "string"},
                "mode": {"type": "string", "enum": ["write", "repair"]},
                "current_proof": {"type": "string"},
            },
            # task_context is enforced at runtime for mode='write' only; keeping
            # it out of the JSON-schema required list lets schema-validating
            # providers make the bare {"mode":"repair"} call the strict nudge
            # asks for.
            "required": [],
            "additionalProperties": False,
        },
    },
}


MCP_BENCHMARK_TOOLS = [
    tool
    for tool in FAIR_TOOLS
    if tool.get("function", {}).get("name") in {"show_task", "read_file", "check_proof"}
]


def _fair_tools(mcp_tools: list[dict[str, object]] | None = None) -> list[dict[str, Any]]:
    if mcp_tools is None and not DRAFT_PROOF_ENABLED:
        return FAIR_TOOLS
    tools: list[dict[str, Any]] = (
        [*MCP_BENCHMARK_TOOLS, *mcp_tools] if mcp_tools is not None else list(FAIR_TOOLS)
    )
    if DRAFT_PROOF_ENABLED:
        tools.append(DRAFT_PROOF_TOOL)
    return tools


def _compact_tool_schemas(tools: list[dict[str, object]]) -> str:
    schemas: list[dict[str, object]] = []
    for tool in tools:
        function = tool.get("function")
        if not isinstance(function, dict) or not isinstance(function.get("name"), str):
            continue
        parameters = function.get("parameters")
        schemas.append(
            {
                "name": function["name"],
                "parameters": parameters if isinstance(parameters, dict) else {},
            }
        )
    return json.dumps(schemas, separators=(",", ":"), sort_keys=True)


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


def _task_index_source_files(task: dict[str, object]) -> list[str]:
    """Relative paths whose PUBLIC declarations are safe to index for prompts.

    Only editable/specification/implementation files named by the task manifest,
    each screened by ``_fair_tool_can_read`` so hidden reference Proofs, the
    GeneratedPreview module, and .env can never enter the index. This keeps the
    declaration index content-free with respect to hidden solutions.
    """
    rels: list[str] = []
    seen: set[str] = set()
    for key in ("specification_files", "implementation_files", "editable_files"):
        value = task.get(key)
        if not isinstance(value, list):
            continue
        for rel in value:
            if not isinstance(rel, str) or rel in seen:
                continue
            seen.add(rel)
            if _fair_tool_can_read(rel):
                rels.append(rel)
    return rels


def _task_declaration_index(
    workspace: Path,
    task: dict[str, object],
    *,
    limit: int = DRAFT_PROOF_DECL_INDEX_LIMIT,
) -> list[dict[str, object]]:
    """Bounded index of public declaration names + signatures for a task.

    Public declarations only (see ``_task_index_source_files``); used to reduce
    invented theorem names in prover prompts without leaking any hidden proof.
    """
    if limit <= 0:
        return []
    index: list[dict[str, object]] = []
    seen_names: set[str] = set()
    for rel in _task_index_source_files(task):
        try:
            path = _safe_workspace_path(workspace, rel)
        except ValueError:
            continue
        if not path.is_file():
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError):
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
            if stripped.startswith("private "):
                continue
            match = DECL_RE.match(stripped)
            if not match:
                continue
            kind, name = match.groups()
            namespace = ".".join(namespace_stack)
            qualified = name if "." in name or not namespace else f"{namespace}.{name}"
            if qualified in seen_names:
                continue
            seen_names.add(qualified)
            index.append(
                {
                    "name": qualified,
                    "kind": kind,
                    "path": rel,
                    "signature": _declaration_signature(lines, lineno - 1),
                }
            )
            if len(index) >= limit:
                return index
    return index


def _declaration_index_block(index: list[dict[str, object]], *, char_limit: int = 3000) -> str:
    """Compact newline list of `kind name : signature-tail` for prompt context."""
    if not index:
        return ""
    lines: list[str] = []
    for item in index:
        signature = str(item.get("signature") or "").strip()
        name = str(item.get("name") or "")
        kind = str(item.get("kind") or "")
        entry = signature if signature else f"{kind} {name}".strip()
        lines.append(f"- {entry}")
    block = "\n".join(lines)
    if len(block) > char_limit:
        block = block[:char_limit].rstrip() + "\n- ...[declaration index truncated]"
    return block


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


PROVER_WRITER_SYSTEM = (
    "You are the proof writer in a strict driver/prover pipeline. "
    "You are given a compact theorem, goal, context, an index of available public declarations, and any errors. "
    "Return only the Lean proof body that belongs after `:= by`. "
    "Do not return markdown fences, JSON, explanations, imports, theorem statements, or comments. "
    "Do not invent theorem or lemma names: prefer names from the declaration index. "
    "Do not use sorry, admit, axiom, placeholder holes such as ?_, or TODO-style placeholders, and do not add hidden imports. "
    "If you are uncertain, still provide the best complete Lean tactic proof body only."
)

PROVER_REPAIR_SYSTEM = (
    "You are the proof repairer in a strict driver/prover pipeline. "
    "You are given the current failing Lean proof body, a compact Lean diagnostic, and the available public declarations. "
    "Make the smallest edit that fixes the reported error - do not rewrite the proof from scratch. "
    "Return only the corrected Lean proof body that belongs after `:= by`. "
    "Do not return markdown fences, JSON, explanations, imports, theorem statements, or comments. "
    "Do not invent theorem or lemma names: prefer names from the declaration index. "
    "Do not use sorry, admit, axiom, placeholder holes such as ?_, or TODO-style placeholders, and do not add hidden imports."
)


def _draft_proof_prompt(
    *,
    task: dict[str, object],
    theorem_statement: str,
    task_context: str,
    goal: str,
    errors: str,
    prompt_kind: str = "write",
    current_proof: str = "",
    declaration_index: str = "",
) -> list[dict[str, Any]]:
    is_repair = prompt_kind == "repair"
    context_parts = [
        f"Task ref: {task.get('task_ref')}",
        f"Target module: {task.get('target_module')}",
        "Target theorem statement:",
        theorem_statement.strip(),
    ]
    if task_context.strip():
        context_parts.extend(["Task context:", task_context.strip()])
    if declaration_index.strip():
        context_parts.extend(["Available public declarations (use these names; do not invent others):", declaration_index.strip()])
    if is_repair and current_proof.strip():
        context_parts.extend(["Current failing proof body (edit this minimally):", current_proof.strip()])
    if goal.strip():
        context_parts.extend(["Current Lean goal/diagnostics:", goal.strip()])
    if errors.strip():
        context_parts.extend(["Recent Lean errors or failed attempts:", errors.strip()])
    user_content = "\n\n".join(part for part in context_parts if part)
    if len(user_content) > DRAFT_PROOF_CONTEXT_CHARS:
        user_content = user_content[:DRAFT_PROOF_CONTEXT_CHARS] + "\n...[truncated for prover prompt]"
    return [
        {"role": "system", "content": PROVER_REPAIR_SYSTEM if is_repair else PROVER_WRITER_SYSTEM},
        {"role": "user", "content": user_content},
    ]


# A single fenced code block: ```lang\n ... ``` . The info string (``lang``)
# is optional; the closing fence is required, so an unterminated fence never
# matches and is treated as unbalanced/ambiguous below.
_CODE_FENCE_RE = re.compile(r"```[^\n]*\n(.*?)```", re.DOTALL)
# A leading ``by`` or ``:= by`` wrapper. The prover is asked for the body that
# belongs *after* ``:= by``; some models still echo the keyword.
_LEADING_BY_RE = re.compile(r"^\s*(?::=\s*)?by\b[ \t]*\r?\n?")


def _strip_leading_by(text: str) -> tuple[str, bool]:
    """Drop a leading ``by`` / ``:= by`` wrapper from a proof body.

    Returns ``(body, stripped)``. Only strips when a non-empty body follows, so a
    bare ``by`` (nothing to keep) is left untouched for the caller to reject."""
    match = _LEADING_BY_RE.match(text)
    if not match:
        return text, False
    rest = text[match.end():].strip()
    if not rest:
        return text, False
    return rest, True


def _normalize_prover_draft(raw: str) -> dict[str, object]:
    """Deterministically extract a single Lean proof body from prover output.

    Accepts a bare body plus common harmless presentational wrappers: exactly one
    Markdown code fence, a leading ``by``/``:= by``, and surrounding explanatory
    prose *only* when an unambiguous fenced Lean block delimits the proof. Rejects
    empty output, unbalanced fences, and multiple/ambiguous candidates. This is a
    structural boundary only - content safety (forbidden tokens, theorem
    statements, leftover JSON) stays in :func:`_reject_draft_reason`, applied by
    the caller to the extracted body. ``raw`` is always returned unmodified so the
    caller can persist it for audit."""
    text = _strip_template_sentinels(raw).strip()
    provenance: list[str] = ["stripped_template_sentinel"] if text != raw.strip() else []
    if not text:
        return {"body": None, "provenance": "empty", "reject_reason": "empty_prover_output", "raw": raw}

    fences = _CODE_FENCE_RE.findall(text)
    if fences:
        if len(fences) > 1:
            return {
                "body": None,
                "provenance": "multiple_fences",
                "reject_reason": "prover_output_multiple_code_blocks",
                "raw": raw,
            }
        # Exactly one closed fence. Text outside it must be explanatory prose,
        # not additional Lean, or the real candidate is ambiguous.
        outside = _CODE_FENCE_RE.sub("", text)
        if ":= by" in outside or _TACTIC_LINE_RE.search(outside) is not None:
            return {
                "body": None,
                "provenance": "ambiguous_outside_fence",
                "reject_reason": "prover_output_ambiguous_multiple_candidates",
                "raw": raw,
            }
        text = fences[0].strip()
        provenance.append("code_fence")
        if not text:
            return {"body": None, "provenance": "code_fence", "reject_reason": "empty_prover_output", "raw": raw}
    elif "```" in text:
        # Backticks present but no complete fence pair: unbalanced/ambiguous.
        return {
            "body": None,
            "provenance": "unbalanced_fence",
            "reject_reason": "prover_output_unbalanced_fence",
            "raw": raw,
        }
    else:
        provenance.append("bare")

    stripped_body, stripped_by = _strip_leading_by(text)
    if stripped_by:
        text = stripped_body
        provenance.append("stripped_leading_by")

    return {"body": text, "provenance": "+".join(provenance), "reject_reason": None, "raw": raw}


def _reject_draft_reason(text: str) -> str | None:
    stripped = text.strip()
    if not stripped:
        return "empty_prover_output"
    if "```" in stripped:
        return "prover_output_contains_markdown"
    if stripped.startswith("{") or stripped.startswith("["):
        return "prover_output_looks_like_json"
    if re.search(r"\b(theorem|lemma)\s+[A-Za-z_]", stripped):
        return "prover_output_contains_theorem_statement"
    if re.search(r"\b(TODO|FIXME|placeholder|fill\s+in|omitted)\b", stripped, flags=re.IGNORECASE):
        return "prover_output_contains_placeholder_text"
    if _contains_forbidden_proof_token(stripped):
        return "prover_output_contains_forbidden_placeholder"
    return None


def _draft_valid_syntax(body: str) -> bool | None:
    """Cheap, best-effort syntax sanity flag for a proof body (no Lean call).

    Returns True/False when we can judge it cheaply, else None. Conservative:
    only flags clearly-broken bodies (unbalanced delimiters or a duplicate
    `:= by`/bare-`by` mistake) so a False is a strong signal, not noise.
    """
    text = body.strip()
    if not text:
        return False
    if text.count("(") != text.count(")"):
        return False
    if text.count("[") != text.count("]"):
        return False
    if text.count("{") != text.count("}"):
        return False
    if ":= by" in text and re.search(r":=\s*by\b[\s\S]*?\bby\b\s*$", text):
        return False
    if re.match(r"^by\b", text):
        return False
    return True


# Optional per-call sampling for the hybrid prover, so it can run at its
# vendor-recommended regime (e.g. Leanstral: temperature=1.0, high reasoning
# effort) without changing the driver's sampling. Empty by default.
PROVER_SAMPLING: dict[str, object] = {}
_prover_temp = (os.environ.get("DEFAULT_HARNESS_PROVER_TEMPERATURE", "") or "").strip()
if _prover_temp:
    PROVER_SAMPLING["temperature"] = float(_prover_temp)
_prover_effort = (os.environ.get("DEFAULT_HARNESS_PROVER_REASONING_EFFORT", "") or "").strip()
if _prover_effort:
    PROVER_SAMPLING["reasoning_effort"] = _prover_effort


def _draft_proof_with_prover(
    args: dict[str, object],
    *,
    task: dict[str, object],
    original: str,
    base_url: str,
    draft_log_path: Path | None,
    workspace: Path | None = None,
    current_proof: str = "",
) -> dict[str, object]:
    if not DRAFT_PROOF_ENABLED:
        return {"ok": False, "error": "draft_proof_not_enabled"}
    task_context = args.get("task_context", "")
    goal = args.get("goal", "")
    errors = args.get("errors", "")
    raw_mode = args.get("mode", "write")
    prompt_kind = "repair" if str(raw_mode).strip().lower() == "repair" else "write"
    stage = PROVER_PROMPT_KINDS[prompt_kind]
    if prompt_kind == "write" and (not isinstance(task_context, str) or not task_context.strip()):
        return {"ok": False, "error": "task_context must be a non-empty string"}
    if not isinstance(task_context, str):
        return {"ok": False, "error": "task_context must be a string when provided"}
    if not isinstance(goal, str):
        return {"ok": False, "error": "goal must be a string when provided"}
    if not isinstance(errors, str):
        return {"ok": False, "error": "errors must be a string when provided"}
    arg_proof = args.get("current_proof")
    if isinstance(arg_proof, str) and arg_proof.strip():
        current_proof = arg_proof
    if prompt_kind == "repair" and not current_proof.strip():
        return {"ok": False, "error": "current_proof is required for repair mode"}

    declaration_index = ""
    if workspace is not None and DRAFT_PROOF_DECL_INDEX_LIMIT > 0:
        declaration_index = _declaration_index_block(_task_declaration_index(workspace, task))

    messages = _draft_proof_prompt(
        task=task,
        theorem_statement=_theorem_statement(original, task.get("theorem_name")),
        task_context=task_context,
        goal=goal,
        errors=errors,
        prompt_kind=prompt_kind,
        current_proof=current_proof,
        declaration_index=declaration_index,
    )
    prover_base_url = DEFAULT_PROVER_BASE_URL or base_url
    if DEFAULT_PROVER_API_KEY:
        prover_api_key_override = DEFAULT_PROVER_API_KEY
    elif prover_base_url.rstrip("/") == base_url.rstrip("/"):
        prover_api_key_override = None
    else:
        # Never fall back to the driver credential on a separate prover host; an
        # empty override sends no Authorization header (no-auth/local endpoints).
        prover_api_key_override = ""
    started = time.time()
    try:
        response = chat_completion(
            messages,
            base_url=prover_base_url,
            model=DEFAULT_PROVER_MODEL,
            tools=None,
            tool_choice=None,
            request_log_path=draft_log_path,
            api_key_override=prover_api_key_override,
            sampling=PROVER_SAMPLING or None,
        )
    except Exception as exc:
        error_payload = exc.to_dict() if isinstance(exc, ChatCompletionError) else {"message": str(exc)}
        if draft_log_path is not None:
            _append_jsonl(
                draft_log_path,
                {
                    "task_ref": task.get("task_ref"),
                    "tool": "draft_proof",
                    "stage": stage,
                    "prompt_kind": prompt_kind,
                    "status": "request_failed",
                    "driver_model": DEFAULT_DRIVER_MODEL,
                    "prover_model": DEFAULT_PROVER_MODEL,
                    "prover_base_url": prover_base_url,
                    "error": error_payload,
                    "duration_seconds": round(time.time() - started, 3),
                },
            )
        return {"ok": False, "error": "prover_request_failed", "detail": error_payload, "prover_model": DEFAULT_PROVER_MODEL, "stage": stage, "prompt_kind": prompt_kind}

    raw_proof = _strip_thinking(_response_text(response)).strip()
    normalized = _normalize_prover_draft(raw_proof)
    provenance = str(normalized["provenance"])
    proof = str(normalized["body"]) if normalized["body"] is not None else ""
    reject_reason = normalized["reject_reason"]
    if not reject_reason:
        # Content safety runs on the extracted body: a fenced draft carrying
        # `sorry` or a full theorem statement must still be rejected.
        reject_reason = _reject_draft_reason(proof)
    valid_syntax = None if reject_reason else _draft_valid_syntax(proof)
    usage = response.get("usage") if isinstance(response, dict) else None
    metadata = {
        key: response.get(key)
        for key in ("id", "model", "system_fingerprint")
        if isinstance(response, dict) and response.get(key) is not None
    }
    log_payload = {
        "task_ref": task.get("task_ref"),
        "tool": "draft_proof",
        "stage": stage,
        "prompt_kind": prompt_kind,
        "status": "rejected" if reject_reason else "drafted",
        "driver_model": DEFAULT_DRIVER_MODEL,
        "prover_model": DEFAULT_PROVER_MODEL,
        "prover_base_url": prover_base_url,
        "declaration_index_size": declaration_index.count("\n- ") + (1 if declaration_index else 0),
        "draft_valid_syntax": valid_syntax,
        "provenance": provenance,
        "usage": usage,
        "metadata": metadata,
        "duration_seconds": round(time.time() - started, 3),
        # Persist both the raw model output and the normalized body so an audit
        # can see exactly what wrapper (if any) was stripped before submission.
        "raw_preview": raw_proof[:1000],
        "proof_preview": proof[:1000],
        "reject_reason": reject_reason,
    }
    if draft_log_path is not None:
        _append_jsonl(draft_log_path, log_payload)
    if reject_reason:
        return {
            "ok": False,
            "error": reject_reason,
            "stage": stage,
            "prompt_kind": prompt_kind,
            "provenance": provenance,
            "prover_model": DEFAULT_PROVER_MODEL,
            "usage": usage,
            "metadata": metadata,
            # Preserve what the prover produced so a follow-up repair authorized by
            # this structured rejection can forward the rejected draft (raw output,
            # or the extracted body when a wrapper was stripped) back to the prover.
            "raw": raw_proof,
            "body": proof,
            "message": "Prover draft was rejected before any Lean proof attempt. Ask for a different draft or submit your own proof via check_proof.",
        }
    return {
        "ok": True,
        "proof": proof,
        "stage": stage,
        "prompt_kind": prompt_kind,
        "provenance": provenance,
        "draft_valid_syntax": valid_syntax,
        "prover_model": DEFAULT_PROVER_MODEL,
        "driver_model": DEFAULT_DRIVER_MODEL,
        "usage": usage,
        "metadata": metadata,
        "message": (
            "Repair draft only; submit the returned body with check_proof to count as an attempt."
            if prompt_kind == "repair"
            else "Draft only; submit with check_proof or try_tactics to count as a proof attempt."
        ),
    }


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
    base_url: str | None = None,
    draft_log_path: Path | None = None,
    prover_state: dict[str, object] | None = None,
    role_metrics: dict[str, object] | None = None,
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
    if name == "draft_proof":
        if base_url is None:
            return {"ok": False, "error": "base_url is required for draft_proof"}
        raw_mode = str(args.get("mode", "write")).strip().lower()
        prompt_kind = "repair" if raw_mode == "repair" else "write"
        current_proof = ""
        if prompt_kind == "repair":
            if prover_state is not None:
                used = int(prover_state.get("repair_count", 0))
                limit = int(prover_state.get("repair_limit", PROVER_REPAIR_ATTEMPTS))
                if used >= limit:
                    return {
                        "ok": False,
                        "error": "prover_repair_budget_exceeded",
                        "max_repairs": limit,
                        "stage": STAGE_REPAIRER,
                        "prompt_kind": "repair",
                        "message": "No more prover repair drafts are allowed for this task; submit the best proof you have with check_proof.",
                    }
            if STRICT_ROLE_SEPARATION:
                # A strict repairer may only edit a prover-derived candidate that
                # was actually submitted and rejected by Lean. Pre-Lean output,
                # transport, schema, or context failures have no measured proof
                # baseline; repairing them would misattribute a fresh proof as a
                # repair and could make the prover edit the untouched skeleton.
                has_lean_failure = isinstance(_last_failed_proof_attempt({"results": attempts}), dict)
                if not has_lean_failure:
                    if role_metrics is not None:
                        role_metrics["repair_blocked_no_failure"] = int(role_metrics.get("repair_blocked_no_failure", 0)) + 1
                    return {
                        "ok": False,
                        "error": "repair_requires_prior_lean_failure",
                        "stage": STAGE_REPAIRER,
                        "prompt_kind": "repair",
                        "message": (
                            "Strict repair mode requires a prior prover-derived proof submission that failed Lean. "
                            "Request a fresh draft_proof write, then submit it with check_proof first."
                        ),
                    }
            try:
                current_proof = proof_path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                current_proof = original
            last_failed = _last_failed_proof_attempt({"results": attempts})
            if STRICT_ROLE_SEPARATION:
                # Strict repair builds the entire prover input from trusted state
                # (workspace proof + recorded Lean failure). Honoring driver
                # free-text here would let it launder a driver-authored proof.
                args = {"mode": "repair"}
            else:
                args = dict(args)
            # The repair prompt promises the prover a Lean diagnostic. Do not
            # depend on the driver forwarding it: fill it from the measured
            # failed attempt so the independent prover sees why it failed.
            if isinstance(last_failed, dict):
                diagnostics = last_failed.get("diagnostics")
                diagnostics = diagnostics if isinstance(diagnostics, dict) else {}
                if not str(args.get("errors") or "").strip():
                    fallback_errors = str(last_failed.get("output") or "").strip() or str(diagnostics.get("first_error") or "").strip()
                    if fallback_errors:
                        args["errors"] = fallback_errors
                if not str(args.get("goal") or "").strip():
                    fallback_goal = str(diagnostics.get("new_goal") or "").strip()
                    if fallback_goal:
                        args["goal"] = fallback_goal
        elif STRICT_ROLE_SEPARATION:
            # Strict write mode: the driver may only pass declarative context.
            # Proof-like context (tactic scripts, `:= by` bodies, code fences) is
            # rejected so the prover cannot be used to launder driver-authored
            # proofs into "prover drafts".
            combined_context = "\n".join(
                str(args.get(key) or "") for key in ("task_context", "goal", "errors")
            )
            context_reason = _strict_context_proof_reason(combined_context)
            if context_reason:
                if role_metrics is not None:
                    role_metrics["strict_context_blocked"] = int(role_metrics.get("strict_context_blocked", 0)) + 1
                return {
                    "ok": False,
                    "error": context_reason,
                    "stage": STAGE_WRITER,
                    "prompt_kind": "write",
                    "message": (
                        "STRICT ROLE SEPARATION: draft_proof context must be declarative (definitions, goals, "
                        "constraints, declaration names) and must not contain Lean proof scripts or code "
                        "fences. Remove the proof-like text and call draft_proof again."
                    ),
                }
        result = _draft_proof_with_prover(
            args,
            task=task,
            original=original,
            base_url=base_url,
            draft_log_path=draft_log_path,
            workspace=workspace,
            current_proof=current_proof,
        )
        if role_metrics is not None:
            if prompt_kind == "repair":
                role_metrics["prover_repair_calls"] = int(role_metrics.get("prover_repair_calls", 0)) + 1
            else:
                role_metrics["prover_writer_calls"] = int(role_metrics.get("prover_writer_calls", 0)) + 1
            if result.get("ok"):
                if result.get("draft_valid_syntax") is True:
                    role_metrics["draft_valid_syntax_count"] = int(role_metrics.get("draft_valid_syntax_count", 0)) + 1
                # A draft accepted only because a harmless wrapper was stripped
                # (fence / leading `by`) is the false-negative this boundary fixes.
                if str(result.get("provenance") or "bare") != "bare":
                    role_metrics["draft_normalized_count"] = int(role_metrics.get("draft_normalized_count", 0)) + 1
            else:
                role_metrics["draft_rejected_count"] = int(role_metrics.get("draft_rejected_count", 0)) + 1
        if prover_state is not None:
            if result.get("ok") and isinstance(result.get("proof"), str):
                # Only the most recent draft is submittable in strict mode, so a
                # stale draft can never be graded as the current stage's output.
                prover_state["latest_draft"] = _normalize_proof_body(str(result["proof"]))
            if prompt_kind == "repair":
                prover_state["repair_count"] = int(prover_state.get("repair_count", 0)) + 1
                if result.get("ok"):
                    # Baseline for outcome classification = the last failed attempt
                    # before this repair draft. Cleared once a submission grades it.
                    prover_state["pending_repair"] = True
                    prover_state["pending_repair_baseline"] = _last_failed_proof_attempt({"results": attempts})
                elif role_metrics is not None:
                    # A rejected repair draft never reaches Lean = no submission.
                    role_metrics["repair_no_submission"] = int(role_metrics.get("repair_no_submission", 0)) + 1
            else:
                prover_state["write_count"] = int(prover_state.get("write_count", 0)) + 1
        return result
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
        auto_writer_usage: object | None = None
        if STRICT_ROLE_SEPARATION and prover_state is not None:
            # Enforce the role split in the tool loop, not just the prompt: a
            # submission is only accepted if its body is (whitespace-normalized)
            # verbatim the LATEST prover draft. Anything else - a driver-authored
            # proof or a stale earlier draft - is rejected without reaching Lean,
            # so driver_writes_proofs=false stays true and repair outcomes are
            # always graded against the draft they belong to.
            latest_draft = prover_state.get("latest_draft")
            latest_draft = latest_draft if isinstance(latest_draft, str) and latest_draft else None
            for _, submitted in proofs:
                if latest_draft is None or _normalize_proof_body(submitted) != latest_draft:
                    if latest_draft is None and DRAFT_PROOF_ENABLED:
                        if base_url is None:
                            return {"ok": False, "error": "base_url is required for strict auto writer"}
                        auto_result = _draft_proof_with_prover(
                            {"mode": "write", "task_context": _strict_auto_writer_context(task=task, workspace=workspace, original=original)},
                            task=task,
                            original=original,
                            base_url=base_url,
                            draft_log_path=draft_log_path,
                            workspace=workspace,
                        )
                        if role_metrics is not None:
                            role_metrics["prover_writer_calls"] = int(role_metrics.get("prover_writer_calls", 0)) + 1
                            if auto_result.get("ok"):
                                if auto_result.get("draft_valid_syntax") is True:
                                    role_metrics["draft_valid_syntax_count"] = int(role_metrics.get("draft_valid_syntax_count", 0)) + 1
                                if str(auto_result.get("provenance") or "bare") != "bare":
                                    role_metrics["draft_normalized_count"] = int(role_metrics.get("draft_normalized_count", 0)) + 1
                            else:
                                role_metrics["draft_rejected_count"] = int(role_metrics.get("draft_rejected_count", 0)) + 1
                        if auto_result.get("ok") and isinstance(auto_result.get("proof"), str):
                            auto_proof = str(auto_result["proof"])
                            auto_writer_usage = auto_result.get("usage")
                            latest_draft = _normalize_proof_body(auto_proof)
                            prover_state["latest_draft"] = latest_draft
                            prover_state["write_count"] = int(prover_state.get("write_count", 0)) + 1
                            proofs = [("auto_draft_proof", auto_proof)]
                            break
                        return {
                            "ok": False,
                            "error": "strict_auto_writer_failed",
                            "stage": STAGE_WRITER,
                            "prompt_kind": "write",
                            "writer_error": auto_result.get("error"),
                            "message": (
                                "STRICT ROLE SEPARATION: the driver attempted to submit before any prover draft. "
                                "The harness ignored the driver proof and routed to the prover writer, but the writer "
                                "did not return a usable draft."
                            ),
                            "usage": auto_result.get("usage"),
                        }
                    if role_metrics is not None:
                        role_metrics["strict_submission_blocked"] = int(role_metrics.get("strict_submission_blocked", 0)) + 1
                    return {
                        "ok": False,
                        "error": "strict_role_separation_violation",
                        "message": (
                            "STRICT ROLE SEPARATION: this submission is not the most recent prover draft, so it "
                            "was not checked. You must never write or edit Lean proof bodies yourself. Call "
                            "draft_proof (mode=write for a fresh proof, mode=repair after a failure) and submit "
                            "the most recently returned proof body verbatim."
                        ),
                    }
        results: list[dict[str, object]] = []
        original_statement = " ".join(_theorem_statement(original, task.get("theorem_name")).split())
        repair_pending = bool(prover_state is not None and prover_state.get("pending_repair"))
        repair_baseline = prover_state.get("pending_repair_baseline") if prover_state is not None else None
        # draft_submitted_count / lean_check_failed_count are PROVER-specific: they
        # must only count submissions whose body is the prover's latest draft under
        # strict/draft conditions. In standalone (non-draft) mode there is no prover,
        # so a driver-authored submission must never be attributed to one.
        attribute_to_prover = STRICT_ROLE_SEPARATION or DRAFT_PROOF_ENABLED
        prover_latest_draft = None
        if prover_state is not None:
            _latest = prover_state.get("latest_draft")
            if isinstance(_latest, str) and _latest:
                prover_latest_draft = _latest

        def _grade_repair(graded: dict[str, object]) -> None:
            nonlocal repair_pending
            if not repair_pending:
                return
            repair_pending = False
            if prover_state is not None:
                prover_state["pending_repair"] = False
                prover_state["pending_repair_baseline"] = None
            valid_baseline = isinstance(repair_baseline, dict)
            outcome = _classify_repair_outcome(repair_baseline if valid_baseline else None, graded)
            graded["repair_outcome"] = outcome
            if role_metrics is not None:
                if outcome == "improved" and not valid_baseline:
                    # The repair passed, but it was authorized only by a structured
                    # pre-Lean rejection with no measured Lean failure to improve
                    # over. Record the pass separately so repair_improved never
                    # over-claims an improvement without a valid pre-repair baseline.
                    graded["repair_outcome"] = "improved_no_baseline"
                    role_metrics["repair_improved_no_baseline"] = int(role_metrics.get("repair_improved_no_baseline", 0)) + 1
                else:
                    key = {
                        "improved": "repair_improved",
                        "regressed": "repair_regressed",
                        "no_change": "repair_no_change",
                    }[outcome]
                    role_metrics[key] = int(role_metrics.get(key, 0)) + 1

        for label, proof in proofs:
            candidate = _candidate_from_response(original, proof, task.get("theorem_name"))
            candidate_statement = " ".join(_theorem_statement(candidate, task.get("theorem_name")).split())
            submitted_full_file = _looks_like_full_file(_extract_lean_file(proof))
            context_guard_failed = submitted_full_file and not _full_file_context_preserved(
                original, candidate
            )
            # Fail closed when the skeleton statement cannot be extracted:
            # proof-body patches keep the statement byte-identical by
            # construction. Whole-file submissions may add helper declarations
            # but cannot alter imports, namespace/open/end context, or target.
            statement_guard_failed = (
                candidate_statement != original_statement
                if original_statement
                else submitted_full_file
            )
            if statement_guard_failed or context_guard_failed:
                attempt = {
                    "attempt": f"tool:{name}",
                    "status": "rejected_statement_mismatch",
                    "exit_code": None,
                    "candidate_path": None,
                    "output": (
                        "the submitted file changes imports, namespace/open/end context, or the target theorem statement; "
                        "keep the benchmark context and theorem signature byte-identical; file-level helper declarations are allowed"
                    ),
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
                _grade_repair(attempt)
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
                _grade_repair(attempt)
                continue
            proof_path.write_text(candidate, encoding="utf-8")
            candidate_path = _write_attempt_artifact(attempts_dir, task, f"fair-{len(attempts) + 1}-{label}", candidate)
            # Only attribute this submission to the prover when it is prover-derived:
            # strict/draft conditions are active AND the submitted body is verbatim
            # (whitespace-normalized) the prover's latest draft. In strict mode the
            # provenance guard above already guarantees this; in draft-only mode the
            # driver could submit its own body, and in standalone mode there is no
            # prover at all, so those must not touch these prover-specific counters.
            prover_derived = (
                attribute_to_prover
                and prover_latest_draft is not None
                and _normalize_proof_body(proof) == prover_latest_draft
            )
            if role_metrics is not None and prover_derived:
                # This candidate cleared the provenance/statement/placeholder
                # guards and is actually being handed to Lean.
                role_metrics["draft_submitted_count"] = int(role_metrics.get("draft_submitted_count", 0)) + 1
            lean_start = time.time()
            code, output = _run_lean_module(workspace, target_module, file_rel=_workspace_rel(workspace, proof_path))
            failure_kind = None if code == 0 else _classify_lean_failure(output)
            if role_metrics is not None and prover_derived and code != 0:
                role_metrics["lean_check_failed_count"] = int(role_metrics.get("lean_check_failed_count", 0)) + 1
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
            _grade_repair(attempt)
            if code == 0:
                response: dict[str, object] = {"ok": True, "passed": True, "results": results}
                if isinstance(auto_writer_usage, dict):
                    response["usage"] = auto_writer_usage
                return response
        response = {"ok": True, "passed": False, "results": results}
        if isinstance(auto_writer_usage, dict):
            response["usage"] = auto_writer_usage
        return response
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


# Chat-template / tool-call sentinels that leak into content when the serving
# stack does not stop on them. Stripped before JSON parsing so a valid tool
# call followed by a leaked sentinel (e.g. `{"tool":"show_task",...}<|im_end|>`)
# is still recovered instead of being counted as a no-tool response.
_TEMPLATE_SENTINELS = (
    "<|im_end|>",
    "</|im_end|>",
    "<|im_start|>",
    "</|im_start|>",
    "<|tool_call_begin|>",
    "<|tool_call_end|>",
    "<|tool_calls_begin|>",
    "<|tool_calls_end|>",
    "<|tool_sep|>",
)


def _strip_template_sentinels(text: str) -> str:
    for sentinel in _TEMPLATE_SENTINELS:
        text = text.replace(sentinel, " ")
    return text


def _first_json_value(text: str) -> object | None:
    """Return the first balanced top-level JSON object/array in text, if any."""
    for start, opener in enumerate(text):
        if opener not in "{[":
            continue
        closer = "}" if opener == "{" else "]"
        depth = 0
        in_string = False
        escaped = False
        for index in range(start, len(text)):
            char = text[index]
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                continue
            if char == '"':
                in_string = True
            elif char == opener:
                depth += 1
            elif char == closer:
                depth -= 1
                if depth == 0:
                    try:
                        return json.loads(text[start : index + 1], strict=False)
                    except json.JSONDecodeError:
                        break
    return None


def _json_payload_from_text(text: str) -> object | None:
    stripped = _strip_thinking(text).strip()
    fenced = re.search(r"```(?:json)?\s*(.*?)```", stripped, flags=re.DOTALL | re.IGNORECASE)
    if fenced:
        stripped = fenced.group(1).strip()
    stripped = _strip_template_sentinels(stripped).strip()
    try:
        return json.loads(stripped, strict=False)
    except json.JSONDecodeError:
        return _first_json_value(stripped)


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
    draft_log_path: Path | None = None,
    native_tools: bool | None = None,
    mcp_session: LeanLspMcpSession | None = None,
) -> dict[str, object]:
    editable_files = task.get("editable_files")
    target_module = task.get("target_module")
    if not isinstance(editable_files, list) or len(editable_files) != 1 or not isinstance(target_module, str):
        return {"task_ref": task.get("task_ref"), "status": "unsupported_task_shape"}
    editable = str(editable_files[0])
    proof_path = workspace / editable
    original = proof_path.read_text(encoding="utf-8")
    attempts: list[dict[str, object]] = []
    native_tools = DEFAULT_NATIVE_TOOLS if native_tools is None else native_tools

    mcp_tools = mcp_session.tools if mcp_session is not None else None
    if mcp_session is not None:
        mcp_names = ", ".join(
            str(tool.get("function", {}).get("name"))
            for tool in mcp_tools or []
            if isinstance(tool.get("function"), dict)
        )
        system_prompt = (
            "You are an agent solving one public Lean benchmark task in an isolated Lean project. "
            "This is the builtin benchmark loop, but its Lean IDE tools come directly from lean-lsp-mcp, "
            "matching the tool names and schemas used by MCP coding agents. "
            "Call show_task first; it returns the shared TASK_SUMMARY.md and a proof_patterns guide with the Verity-specific "
            "simp/unfold recipe (contract function + storage field names + getStorage/setStorage/Verity.require/Verity.bind/Bind.bind/"
            "Verity.pure/Pure.pure/Contract.run/ContractResult.snd) that closes most goals; follow it before inventing your own approach. "
            "Then use "
            "read_file for source text and the lean_* tools for goals, diagnostics, navigation, completion, "
            "local declaration search, code actions, and non-mutating tactic experiments. "
            "lean-lsp-mcp does not edit files: submit a complete proof body with check_proof when ready; "
            "check_proof accepts either a tactic body to place under `:= by`, or a complete Lean file "
            "(with imports, namespace, helper lemmas, and the target theorem); the theorem statement must stay byte-identical. "
            "It patches only the benchmark theorem, runs Lean, and counts against max_attempts. "
            f"Available MCP tools: {mcp_names}. "
            "Use lean_local_search before guessing declaration names and lean_multi_attempt to compare small "
            "tactic snippets at a proof position. Iterate: submit, read the Lean error, fix, resubmit. "
            "Do not use sorry, "
            "admit, axiom, hidden imports, Benchmark.GeneratedPreview, or reference Proofs modules. "
            "Do not assume a hardcoded solution from the task name."
        )
        if not native_tools:
            compact_schemas = _compact_tool_schemas(_fair_tools(mcp_tools))
            system_prompt += (
                " Native tool calling is unavailable, so reply only with one JSON tool call shaped like "
                '{"tool":"show_task","arguments":{}}. '
                f"Allowed JSON tool schemas (name + parameters): {compact_schemas}"
            )
        user_prompt = (
            f"Solve the Lean task in editable file {editable}. Call show_task first, inspect the goal through "
            "lean-lsp-mcp, then submit proof bodies with check_proof until Lean passes."
        )
    elif native_tools:
        draft_tool_instruction = (
            " When enabled, draft_proof asks a separate prover model for a proof-body candidate only; "
            "you must inspect its output and submit it with check_proof or try_tactics before it counts as an attempt."
            if DRAFT_PROOF_ENABLED
            else ""
        )
        system_prompt = (
            "You are an agent solving one public Lean benchmark task through tools only. "
            "Call show_task first; it returns the shared TASK_SUMMARY.md and a proof_patterns guide with the Verity-specific "
            "simp/unfold recipe (contract function + storage field names + getStorage/setStorage/Verity.require/Verity.bind/Bind.bind/"
            "Verity.pure/Pure.pure/Contract.run/ContractResult.snd) that closes most goals; follow it before inventing your own approach. "
            "Then inspect files with read_file, show_goal, definition_outline, and search_declarations. "
            "Use tactic_sandbox for exploratory tactic prefixes (it shows the resulting goal and does not count as a proof attempt), "
            "show_goal to see the current goal state, and check_proof or try_tactics for proof attempts. "
            f"{draft_tool_instruction} "
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
        draft_tool_instruction = (
            " draft_proof {task_context,goal,errors} asks a separate prover for an unchecked proof-body draft;"
            if DRAFT_PROOF_ENABLED
            else ""
        )
        system_prompt = (
            "Solve one Lean task by JSON tool calls only. "
            "Allowed tools: show_task {}, read_file {path}, show_goal {}, "
            "definition_outline {query,limit}, search_declarations {query,limit}, "
            f"tactic_sandbox {{prefix}},{draft_tool_instruction} try_tactics {{tactics}}, check_proof {{proof}}. "
            "Non-proof tools are capped; reserve budget for try_tactics/check_proof. "
            "No sorry/admit/axiom/hidden imports/reference Proofs. "
            "Reply only as JSON, e.g. {\"tool\":\"show_task\",\"arguments\":{}}."
        )
        user_prompt = f"Task file: {editable}. First call show_task."
    continuation_prompt = (
        f"Task file: {editable}. show_task was already called. Continue from the tool result below; "
        "do not restart task discovery or repeat an unchanged tool call."
    )

    if STRICT_ROLE_SEPARATION:
        system_prompt += (
            " STRICT ROLE SEPARATION: you are the orchestrator only and must never write or edit Lean proof "
            "bodies yourself. Get the initial proof from draft_proof with {\"mode\":\"write\"} and submit it "
            "verbatim with check_proof; pass only declarative context (definitions, goals, constraints, "
            "declaration names) to draft_proof, never Lean proof scripts. After a failed Lean check, call "
            "draft_proof with {\"mode\":\"repair\"} to "
            "obtain a minimal repair of the current proof, then submit that body verbatim. Submissions that "
            "are not verbatim the most recent prover draft are rejected without being checked. At most "
            f"{PROVER_REPAIR_ATTEMPTS} prover repair(s) are allowed per task."
        )

    messages: list[dict[str, Any]] = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_prompt},
    ]
    pending_repetition_warning: str | None = None

    def set_compact_user_context(content: str) -> None:
        nonlocal pending_repetition_warning
        if pending_repetition_warning:
            content = f"{content}\n\n{pending_repetition_warning}"
            pending_repetition_warning = None
        messages[:] = [
            {"role": "system", "content": system_prompt},
            {
                "role": "user",
                "content": f"{continuation_prompt}\n{content}\nReply with the next JSON tool call.",
            },
        ]

    def flush_pending_repetition_warning() -> None:
        nonlocal pending_repetition_warning
        if pending_repetition_warning:
            messages.append({"role": "user", "content": pending_repetition_warning})
            pending_repetition_warning = None

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
    prover_state: dict[str, object] = {
        "write_count": 0,
        "repair_count": 0,
        "repair_limit": PROVER_REPAIR_ATTEMPTS,
        "pending_repair": False,
        "pending_repair_baseline": None,
    }
    role_metrics: dict[str, object] = {
        "role_config": _role_config(),
        "prover_writer_calls": 0,
        "prover_repair_calls": 0,
        "draft_valid_syntax_count": 0,
        "draft_rejected_count": 0,
        "draft_normalized_count": 0,
        "draft_submitted_count": 0,
        "lean_check_failed_count": 0,
        "repair_no_submission": 0,
        "repair_blocked_no_failure": 0,
        "repair_improved": 0,
        "repair_improved_no_baseline": 0,
        "repair_regressed": 0,
        "repair_no_change": 0,
        "strict_submission_blocked": 0,
        "strict_context_blocked": 0,
    }
    usage_totals = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0}
    corrective_protocol_sent = False
    repeated_signatures: dict[str, int] = {}

    def protocol_failure(status: str, request_index: int, detail: dict[str, object]) -> dict[str, object] | None:
        nonlocal corrective_protocol_sent
        _append_jsonl(
            conversation_log_path,
            {
                "task_ref": task.get("task_ref"),
                "request_index": request_index,
                "status": status,
                **detail,
            },
        )
        if not corrective_protocol_sent:
            corrective_protocol_sent = True
            corrective = (
                "Your previous tool call was malformed. Reply with exactly one allowed tool call. "
                "For JSON fallback use {\"tool\":\"show_task\",\"arguments\":{}} or the same shape with valid arguments."
            )
            tool_call_id = detail.get("tool_call_id")
            tool_name = detail.get("tool")
            if isinstance(tool_call_id, str) and isinstance(tool_name, str):
                messages.append({"role": "tool", "tool_call_id": tool_call_id, "name": tool_name, "content": corrective})
            else:
                messages.append({"role": "user", "content": corrective})
            return None
        return {
            "task_ref": task.get("task_ref"),
            "status": status,
            "failure_class": _failure_taxonomy(status, attempts, tool_calls=tool_calls_executed, no_tool_responses=no_tool_responses),
            "error": detail,
            "usage": usage_totals,
            "attempts": attempts,
            "tool_calls_executed": tool_calls_executed,
            "non_proof_tool_calls": non_proof_tool_calls,
            "non_proof_tool_limit": non_proof_tool_limit,
            "tool_log": str(tool_log_path),
            "conversation_log": str(conversation_log_path),
            "role_metrics": role_metrics,
        }

    def repetition_failure(signature: str) -> dict[str, object] | None:
        nonlocal pending_repetition_warning
        count = repeated_signatures.get(signature, 0) + 1
        repeated_signatures[signature] = count
        if count == 2:
            pending_repetition_warning = (
                "You repeated the same unproductive action. Change strategy: inspect a different goal/file or submit a materially different proof attempt."
            )
            return None
        if count >= 3:
            return {
                "task_ref": task.get("task_ref"),
                "status": "repetition_loop",
                "failure_class": _failure_taxonomy("repetition_loop", attempts, tool_calls=tool_calls_executed, no_tool_responses=no_tool_responses),
                "usage": usage_totals,
                "attempts": attempts,
                "tool_calls_executed": tool_calls_executed,
                "non_proof_tool_calls": non_proof_tool_calls,
                "non_proof_tool_limit": non_proof_tool_limit,
                "no_tool_responses": no_tool_responses,
                "tool_log": str(tool_log_path),
                "conversation_log": str(conversation_log_path),
                "loop_signature": signature,
                "role_metrics": role_metrics,
            }
        return None

    context_limit = 0
    if transport.DEFAULT_CONTEXT_TOKENS:
        try:
            context_limit = int(transport.DEFAULT_CONTEXT_TOKENS)
        except ValueError:
            context_limit = 0

    def _accumulate_usage(response: dict[str, object]) -> None:
        usage = response.get("usage") if isinstance(response, dict) else None
        if isinstance(usage, dict):
            usage_totals["requests"] += 1
            for key in ("prompt_tokens", "completion_tokens", "total_tokens"):
                value = usage.get(key)
                if isinstance(value, (int, float)):
                    usage_totals[key] += int(value)

    token_budget_exhausted = False
    context_budget_exhausted = False
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
                model=DEFAULT_DRIVER_MODEL,
                tools=_fair_tools(mcp_tools) if native_tools else None,
                tool_choice="auto" if native_tools else None,
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
                "role_metrics": role_metrics,
            }
        _accumulate_usage(response)
        usage = response.get("usage") if isinstance(response, dict) else None
        prompt_tokens = usage.get("prompt_tokens") if isinstance(usage, dict) else None
        if (
            context_limit > 0
            and isinstance(prompt_tokens, (int, float))
            and prompt_tokens >= int(context_limit * DEFAULT_CONTEXT_STOP_FRACTION)
        ):
            context_budget_exhausted = True
            _append_jsonl(
                conversation_log_path,
                {
                    "task_ref": task.get("task_ref"),
                    "request_index": request_index,
                    "status": "context_budget_exhausted",
                    "prompt_tokens": int(prompt_tokens),
                    "context_limit": context_limit,
                    "context_stop_fraction": DEFAULT_CONTEXT_STOP_FRACTION,
                },
            )
            break
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
                "transport_mode": _transport_mode(),
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
            no_tool_responses += 1
            if text.strip():
                repeated = repetition_failure("no-tool:" + re.sub(r"\s+", " ", text.strip())[:300])
                if repeated is not None:
                    return repeated
            if no_tool_responses >= no_tool_response_limit:
                _append_jsonl(
                    conversation_log_path,
                    {
                        "task_ref": task.get("task_ref"),
                        "request_index": request_index,
                        "status": "no_tool_response_limit_exceeded",
                        "no_tool_responses": no_tool_responses,
                        "empty_content": not bool(text.strip()),
                    },
                )
                break
            messages.append(
                {
                    "role": "user",
                    "content": "Tool call required. Reply only with compact JSON for one allowed tool.",
                }
            )
            _compact_fair_messages(messages, system_prompt=system_prompt, user_prompt=user_prompt)
            continue
        for tool_call in tool_calls:
            if not isinstance(tool_call, dict):
                failure = protocol_failure("invalid_tool_call", request_index, {"error": "tool call is not an object", "raw_type": type(tool_call).__name__})
                if failure is not None:
                    return failure
                continue
            function = tool_call.get("function")
            if not isinstance(function, dict):
                failure = protocol_failure("invalid_tool_call", request_index, {"error": "tool call missing function object", "tool_call": _shrink_strings(tool_call, 300)})
                if failure is not None:
                    return failure
                continue
            name = function.get("name")
            raw_args = function.get("arguments") or "{}"
            try:
                args = json.loads(raw_args) if isinstance(raw_args, str) else raw_args
            except json.JSONDecodeError as exc:
                failure = protocol_failure(
                    "malformed_tool_call",
                    request_index,
                    {
                        "error": "malformed_tool_arguments",
                        "tool": name if isinstance(name, str) else None,
                        "tool_call_id": tool_call.get("id") if isinstance(tool_call.get("id"), str) else None,
                        "message": str(exc),
                        "arguments_preview": str(raw_args)[:500],
                    },
                )
                if failure is not None:
                    return failure
                continue
            if not isinstance(args, dict):
                failure = protocol_failure(
                    "malformed_tool_call",
                    request_index,
                    {
                        "error": "malformed_tool_arguments",
                        "tool": name if isinstance(name, str) else None,
                        "tool_call_id": tool_call.get("id") if isinstance(tool_call.get("id"), str) else None,
                        "message": "tool arguments must decode to an object",
                    },
                )
                if failure is not None:
                    return failure
                continue
            if not isinstance(name, str):
                failure = protocol_failure("invalid_tool_call", request_index, {"error": "tool call missing function name", "tool_call": _shrink_strings(tool_call, 300)})
                if failure is not None:
                    return failure
                continue
            repeated = repetition_failure("tool:" + name + ":" + json.dumps(args, sort_keys=True, default=str)[:500])
            if repeated is not None:
                return repeated
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
                    if native_tools:
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
                flush_pending_repetition_warning()
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
                    if native_tools:
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
                flush_pending_repetition_warning()
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
                    if native_tools:
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
                flush_pending_repetition_warning()
                continue
            if name == "try_tactics":
                remaining = max(0, max_attempts - _proof_attempt_count(attempts))
                raw_tactics = args.get("tactics")
                if isinstance(raw_tactics, list):
                    args["tactics"] = raw_tactics[:remaining]
            tool_start = time.time()
            if mcp_session is not None and name.startswith("lean_"):
                try:
                    result = mcp_session.call_tool(name, args)
                except LeanLspMcpTransportError as exc:
                    result = {
                        "ok": False,
                        "error": str(exc),
                        "failure_kind": "lean_lsp_mcp_transport_error",
                        "terminal_transport_error": True,
                    }
                except LeanLspMcpError as exc:
                    result = {
                        "ok": False,
                        "error": str(exc),
                        "failure_kind": "lean_lsp_mcp_error",
                    }
            else:
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
                    base_url=base_url,
                    draft_log_path=draft_log_path,
                    prover_state=prover_state,
                    role_metrics=role_metrics,
                )
                if (
                    mcp_session is not None
                    and name in {"check_proof", "try_tactics"}
                ):
                    mcp_session.mark_workspace_files_changed()
            _accumulate_usage(result)
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
                if native_tools:
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
            flush_pending_repetition_warning()
            if result.get("terminal_transport_error") is True:
                return {
                    "task_ref": task.get("task_ref"),
                    "status": "request_failed",
                    "failure_class": "transport_error",
                    "error": {"kind": "transport_error", "message": result.get("error")},
                    "usage": usage_totals,
                    "attempts": attempts,
                    "tool_calls_executed": tool_calls_executed,
                    "non_proof_tool_calls": non_proof_tool_calls,
                    "non_proof_tool_limit": non_proof_tool_limit,
                    "tactic_sandbox_calls": sandbox_state["count"],
                    "role_metrics": role_metrics,
                    "tool_log": str(tool_log_path),
                    "conversation_log": str(conversation_log_path),
                }
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
                    "role_metrics": role_metrics,
                    "tool_log": str(tool_log_path),
                    "conversation_log": str(conversation_log_path),
                }
            repaired = False
            if STRICT_ROLE_SEPARATION and name in {"check_proof", "try_tactics"}:
                # The driver must not edit the proof itself; route the repair to
                # the prover via draft_proof(mode=repair) while budget remains.
                failed_attempt = _last_failed_proof_attempt(result)
                if failed_attempt is not None and int(prover_state["repair_count"]) < int(prover_state["repair_limit"]):
                    messages.append({"role": "user", "content": STRICT_DRIVER_REPAIR_NUDGE})
                    _compact_fair_messages(
                        messages,
                        system_prompt=system_prompt,
                        user_prompt=continuation_prompt,
                    )
                    repaired = True
            elif DIAGNOSTIC_RETRY_ENABLED and name in {"check_proof", "try_tactics"}:
                failed_attempt = _last_failed_proof_attempt(result)
                if failed_attempt is not None:
                    candidate_source = failed_attempt.get("candidate_path")
                    current_candidate: str | None = None
                    if isinstance(candidate_source, str) and candidate_source:
                        try:
                            current_candidate = Path(candidate_source).read_text(encoding="utf-8")
                        except (OSError, UnicodeDecodeError):
                            current_candidate = None
                    if current_candidate is None:
                        try:
                            current_candidate = proof_path.read_text(encoding="utf-8")
                        except (OSError, UnicodeDecodeError):
                            current_candidate = original
                    messages[:] = _diagnostic_repair_messages(
                        system_prompt=system_prompt,
                        task=task,
                        editable=editable,
                        candidate=current_candidate,
                        attempt=failed_attempt,
                    )
                    repaired = True
            if not repaired:
                _compact_fair_messages(
                    messages,
                    system_prompt=system_prompt,
                    user_prompt=continuation_prompt,
                )
    if not attempts:
        proof_path.write_text(original, encoding="utf-8")
    if context_budget_exhausted:
        final_status = "context_budget_exhausted"
    elif tool_calls_executed >= max_tool_calls:
        final_status = "max_tool_calls_exceeded"
    elif _proof_attempt_count(attempts) >= max_attempts:
        final_status = "max_attempts_exceeded"
    elif no_tool_responses >= no_tool_response_limit:
        final_status = "failed_no_tool_calls"
    else:
        final_status = "failed_submitted" if attempts else "failed_no_attempt"
    return {
        "task_ref": task.get("task_ref"),
        "status": final_status,
        "failure_class": _failure_taxonomy(final_status, attempts, tool_calls=tool_calls_executed, no_tool_responses=no_tool_responses),
        "usage": usage_totals,
        "token_budget_exhausted": token_budget_exhausted,
        "context_budget_exhausted": context_budget_exhausted,
        "attempts": attempts,
        "tool_calls_executed": tool_calls_executed,
        "non_proof_tool_calls": non_proof_tool_calls,
        "non_proof_tool_limit": non_proof_tool_limit,
        "no_tool_responses": no_tool_responses,
        "tactic_sandbox_calls": sandbox_state["count"],
        "role_metrics": role_metrics,
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
    harness_id: str = HARNESS_ID,
    run_slug: str = RUN_SLUG,
    track: str = "group/lean_tools_mcp",
    tool_backend: str = "lean-lsp-mcp",
) -> tuple[int, Path]:
    if max_attempts < 0:
        raise ValueError("max_attempts must be non-negative")
    if max_tool_calls < 0:
        raise ValueError("max_tool_calls must be non-negative")
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_subject = task_ref or group_id
    model_slug = "".join(ch if ch.isalnum() else "-" for ch in DEFAULT_DRIVER_MODEL).strip("-").lower()
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{run_slug}-fair-{model_slug}-{run_subject.replace('/', '__')}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    start = time.time()
    group = load_group(group_id, suite)
    if task_ref:
        group = filter_group_to_task(group, task_ref)
    base_url = DEFAULT_BASE_URL
    credentials_available = bool(_api_key()) or _local_no_auth_endpoint(base_url)
    dependency_warm_builds: list[dict[str, object]] = []
    if not dry_run and credentials_available:
        dependency_warm_builds = warm_public_dependencies(
            group,
            timeout_seconds=dependency_warm_timeout_seconds(),
            log_path=run_dir / "dependency-warm.log",
        )
    built = build_group_workspace(group, run_id=run_id)
    assert_workspace_isolated(built.path)
    response: dict[str, object]
    role_config = _role_config()
    benchmark_budget = {
        "max_attempts": max_attempts,
        "max_tool_calls": max_tool_calls,
        "max_turns": None,
        "completion_token_budget": DEFAULT_TOKEN_BUDGET,
    }
    if tool_backend not in {"lean-lsp-mcp"}:
        raise ValueError(f"unsupported non-MCP tool backend: {tool_backend}")
    op_budget = operational_budget()
    budgets = {
        "benchmark_budget": benchmark_budget,
        "operational_budget": {
            "provider_retries": op_budget.provider_retries,
            "infra_restarts": op_budget.infra_restarts,
            "request_timeout_seconds": op_budget.request_timeout_seconds,
            "stream_idle_timeout_seconds": op_budget.stream_idle_timeout_seconds,
            "warm_build_timeout_seconds": op_budget.warm_build_timeout_seconds,
        },
    }
    target_warm_builds: list[dict[str, object]] = []
    if (
        not dry_run
        and credentials_available
        and not any(warm_result_failed(item) for item in dependency_warm_builds)
    ):
        tasks_payload = json.loads(
            (built.path / "harness" / "TASKS.json").read_text(encoding="utf-8")
        )
        warm_timeout = int(os.environ.get("DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS", "1800"))
        target_warm_builds = _warm_target_modules(
            workspace=built.path,
            run_dir=run_dir,
            tasks=tasks_payload.get("tasks", []),
            timeout_seconds=warm_timeout,
        )
    dependency_warm_failed = any(warm_result_failed(item) for item in dependency_warm_builds)
    target_warm_timed_out = any(item.get("exit_code") == 124 for item in target_warm_builds)
    setup_failure_class = (
        "infra_dependency_warm_failed"
        if dependency_warm_failed
        else "infra_target_warm_timeout"
        if target_warm_timed_out
        else None
    )
    pre_mcp_reason = (
        "dry_run"
        if dry_run
        else "missing_credentials"
        if not credentials_available
        else "dependency_warm_failed"
        if dependency_warm_failed
        else "target_warm_failed"
        if target_warm_timed_out
        else None
    )
    # This is an execution contract, rather than an inference from terminal
    # status: only these four paths may finish before an MCP launch is tried.
    mcp_lifecycle: dict[str, object] = (
        {"status": "not_attempted", "reason": pre_mcp_reason}
        if pre_mcp_reason is not None
        else {"status": "started"}
    )
    if dry_run:
        response = {
            "status": "dry_run",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_DRIVER_MODEL,
            "driver_model": DEFAULT_DRIVER_MODEL,
            "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
            "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
            "prover_base_url": (DEFAULT_PROVER_BASE_URL or base_url) if DRAFT_PROOF_ENABLED else None,
            "strict_role_separation": STRICT_ROLE_SEPARATION,
            "prover_repair_attempts": PROVER_REPAIR_ATTEMPTS if STRICT_ROLE_SEPARATION else 0,
            "role_config": role_config,
            "transport_mode": _transport_mode(),
            "mode": "fair",
            "tool_backend": tool_backend,
            "max_attempts": max_attempts,
            "max_tool_calls": max_tool_calls,
            **budgets,
        }
    elif not _api_key() and not _local_no_auth_endpoint(base_url):
        provider_key_hint = f", DEFAULT_HARNESS_{DEFAULT_PROVIDER.upper()}_API_KEY" if DEFAULT_PROVIDER else ""
        response = {
            "status": "missing_credentials",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_DRIVER_MODEL,
            "driver_model": DEFAULT_DRIVER_MODEL,
            "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
            "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
            "transport_mode": _transport_mode(),
            "mode": "fair",
            "tool_backend": tool_backend,
            "error": f"fair mode requires DEFAULT_HARNESS_API_KEY{provider_key_hint}, GAZELLA_API_KEY, OPENAI_API_KEY, or a localhost-compatible no-auth endpoint",
            "tasks": [],
            "provider_setup_error": True,
            "failure_class": "provider_setup_error",
            **budgets,
        }
    elif setup_failure_class is not None:
        warm_failure_tasks = [
            {
                "task_ref": task.task_ref,
                "status": "request_failed",
                "failure_class": setup_failure_class,
                "error": {
                    "kind": "transport_error",
                    "message": "Lean setup failed before provider preflight",
                },
                "attempts": [],
                "benchmark_budget": benchmark_budget,
                "usage": {
                    "prompt_tokens": 0,
                    "completion_tokens": 0,
                    "total_tokens": 0,
                    "requests": 0,
                },
            }
            for task in group.tasks
        ]
        response = {
            "status": "completed_with_failures",
            "error": "Lean setup failed; no model request attempted",
            "provider": _active_provider(),
            "base_url": base_url,
            "model": DEFAULT_DRIVER_MODEL,
            "driver_model": DEFAULT_DRIVER_MODEL,
            "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
            "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
            "strict_role_separation": STRICT_ROLE_SEPARATION,
            "role_config": role_config,
            "transport_mode": _transport_mode(),
            "mode": "fair",
            "tool_backend": tool_backend,
            "provider_setup_error": False,
            "failure_class": setup_failure_class,
            "dependency_warm_builds": dependency_warm_builds,
            "warm_builds": target_warm_builds,
            "tasks": warm_failure_tasks,
            "failure_counts": {setup_failure_class: len(group.tasks)},
            **budgets,
        }
    else:
        task_results: list[dict[str, object]] = []
        warm_builds = target_warm_builds
        preflight_passed = False
        preflight: dict[str, object] | None = None
        mcp_session: LeanLspMcpSession | None = None
        mcp_metadata: dict[str, object] | None = None
        mcp_started = False
        mcp_preflight_passed = tool_backend != "lean-lsp-mcp"
        try:
            if tool_backend == "lean-lsp-mcp":
                mcp_session = LeanLspMcpSession(built.path)
                mcp_session.start()
                mcp_started = True
                mcp_metadata = mcp_session.metadata()
                mcp_preflight_passed = True
            preflight = _role_provider_preflight(base_url)
            if preflight.get("status") != "passed":
                raise RuntimeError(f"provider preflight failed: {preflight.get('error') or preflight}")
            preflight_passed = True
            native_tools = _native_tools_for_preflight(preflight)
            preflight["selected_tool_protocol"] = "native" if native_tools else "json_text_fallback"
            tasks_payload = json.loads(
                (built.path / "harness" / "TASKS.json").read_text(encoding="utf-8")
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
                            draft_log_path=run_dir / "draft-proofs" / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}.jsonl",
                            native_tools=native_tools,
                            mcp_session=mcp_session,
                        )
                    )
                    task_results[-1]["benchmark_budget"] = benchmark_budget
                    task_results[-1]["validity"] = row_validity(task_results[-1], expected_budget=benchmark_budget)
            aggregate_usage = {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0}
            for task_result in task_results:
                task_usage = task_result.get("usage")
                if isinstance(task_usage, dict):
                    for key in aggregate_usage:
                        value = task_usage.get(key)
                        if isinstance(value, (int, float)):
                            aggregate_usage[key] += int(value)
            aggregate_role_metrics = _aggregate_role_metrics(task_results)
            response = {
                "status": "completed",
                "provider": _active_provider(),
                "base_url": base_url,
                "model": DEFAULT_DRIVER_MODEL,
                "driver_model": DEFAULT_DRIVER_MODEL,
                "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
                "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
                "strict_role_separation": STRICT_ROLE_SEPARATION,
                "prover_repair_attempts": PROVER_REPAIR_ATTEMPTS if STRICT_ROLE_SEPARATION else 0,
                "role_config": role_config,
                "role_metrics_totals": aggregate_role_metrics,
                "transport_mode": _transport_mode(),
                "tool_protocol": "native" if native_tools else "json_text_fallback",
                "streaming_fallback_reason": _streaming_fallback_reason(),
                "mode": "fair",
                "tool_backend": tool_backend,
                "lean_lsp_mcp": mcp_metadata,
                "mcp_setup_error": False,
                "mcp_preflight": {"status": "passed"}
                if tool_backend == "lean-lsp-mcp"
                else None,
                "usage": aggregate_usage,
                "preflight": preflight,
                "dependency_warm_builds": dependency_warm_builds,
                "warm_builds": warm_builds,
                "tasks": task_results,
                "failure_counts": failure_counts_from_tasks(task_results),
                **budgets,
            }
        except Exception as exc:
            mcp_setup_error = (
                isinstance(exc, LeanLspMcpError)
                and tool_backend == "lean-lsp-mcp"
                and not mcp_preflight_passed
            )
            status = (
                # Keep the setup failure details in mcp_preflight and failure_class,
                # but persist an aggregatable terminal status for group runs.
                "completed_with_failures"
                if mcp_setup_error
                else "harness_error"
                if preflight_passed
                else "preflight_failed"
            )
            if mcp_setup_error:
                task_results = [
                    {
                        "task_ref": task.task_ref,
                        "status": "request_failed",
                        "failure_class": "mcp_setup_error",
                        "error": {"kind": "mcp_setup_error", "message": str(exc)},
                        "attempts": [],
                        "usage": {
                            "prompt_tokens": 0,
                            "completion_tokens": 0,
                            "total_tokens": 0,
                            "requests": 0,
                        },
                        "benchmark_budget": benchmark_budget,
                    }
                    for task in group.tasks
                ]
            response = {
                "status": status,
                "error": str(exc),
                "provider": _active_provider(),
                "base_url": base_url,
                "model": DEFAULT_DRIVER_MODEL,
                "driver_model": DEFAULT_DRIVER_MODEL,
                "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
                "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
                "strict_role_separation": STRICT_ROLE_SEPARATION,
                "role_config": role_config,
                "transport_mode": _transport_mode(),
                "streaming_fallback_reason": _streaming_fallback_reason(),
                "mode": "fair",
                "tool_backend": tool_backend,
                "lean_lsp_mcp": mcp_metadata,
                "provider_setup_error": status == "preflight_failed",
                "failure_class": (
                    "mcp_setup_error"
                    if mcp_setup_error
                    else "provider_setup_error"
                    if status == "preflight_failed"
                    else None
                ),
                "mcp_setup_error": mcp_setup_error,
                "mcp_preflight": {
                    "status": "failed" if mcp_setup_error else "passed",
                    "error": str(exc) if mcp_setup_error else None,
                }
                if tool_backend == "lean-lsp-mcp"
                else None,
                "setup_failure_class": "infra_agent_preflight_failed" if mcp_setup_error else None,
                "preflight": preflight,
                "dependency_warm_builds": dependency_warm_builds,
                "warm_builds": warm_builds,
                "tasks": task_results,
                "failure_counts": failure_counts_from_tasks(task_results),
                **budgets,
            }
        finally:
            if mcp_session is not None:
                mcp_session.close()
                mcp_metadata = mcp_session.metadata()
            if mcp_started:
                mcp_lifecycle["status"] = "completed"
        if mcp_metadata is not None:
            response["lean_lsp_mcp"] = mcp_metadata

    response["mcp_lifecycle"] = mcp_lifecycle

    if response.get("provider_setup_error") and not response.get("tasks"):
        provider_error = str(response.get("error") or "provider setup failed before model execution")
        response["tasks"] = _provider_setup_task_rows(group, benchmark_budget, provider_error)
        response["failure_counts"] = {"provider_setup_error": len(group.tasks)}

    (run_dir / "workspace-manifest.json").write_text((built.path / "workspace-manifest.json").read_text(encoding="utf-8"), encoding="utf-8")
    shutil.copy2(built.path / "harness" / "TASK_SUMMARY.md", run_dir / "TASK_SUMMARY.md")
    (run_dir / "harness-request.json").write_text(
        json.dumps(
            {
                "group": agent_group_to_json(group),
                "provider": _active_provider(),
                "base_url": base_url,
                "model": DEFAULT_DRIVER_MODEL,
                "driver_model": DEFAULT_DRIVER_MODEL,
                "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
                "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
                "strict_role_separation": STRICT_ROLE_SEPARATION,
                "prover_repair_attempts": PROVER_REPAIR_ATTEMPTS if STRICT_ROLE_SEPARATION else 0,
                "role_config": role_config,
                "dependency_warm_builds": dependency_warm_builds,
                "transport_mode": _transport_mode(),
                "streaming_fallback_reason": _streaming_fallback_reason(),
                "mode": "fair",
                "tool_backend": tool_backend,
                "max_attempts": max_attempts,
                "max_tool_calls": max_tool_calls,
                **budgets,
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
    artifact_setup_failure_class = setup_failure_class
    if isinstance(response.get("setup_failure_class"), str):
        artifact_setup_failure_class = str(response["setup_failure_class"])
    if response.get("provider_setup_error"):
        artifact_setup_failure_class = "provider_setup_error"
    verifier_result = (
        setup_failure_verifier_result(
            group,
            built.path,
            failure_class=artifact_setup_failure_class,
            artifact_dir=run_dir / "verifier",
        )
        if artifact_setup_failure_class is not None
        else verify_group(group, built.path, artifact_dir=run_dir / "verifier")
    )
    classification = classify_run(verifier_result, response.get("tasks") if isinstance(response.get("tasks"), list) else [])
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": harness_id,
        "provider": _active_provider(),
        "model": DEFAULT_DRIVER_MODEL,
        "driver_model": DEFAULT_DRIVER_MODEL,
        "prover_model": DEFAULT_PROVER_MODEL if DRAFT_PROOF_ENABLED else None,
        "prover_mode": DEFAULT_PROVER_MODE if DRAFT_PROOF_ENABLED else None,
        "prover_base_url": (DEFAULT_PROVER_BASE_URL or base_url) if DRAFT_PROOF_ENABLED else None,
        "strict_role_separation": STRICT_ROLE_SEPARATION,
        "prover_repair_attempts": PROVER_REPAIR_ATTEMPTS if STRICT_ROLE_SEPARATION else 0,
        "role_config": role_config,
        "role_metrics_totals": response.get("role_metrics_totals"),
        "dependency_warm_builds": response.get("dependency_warm_builds", dependency_warm_builds),
        "track": track,
        "mode": "fair",
        "tool_backend": tool_backend,
        "mcp_lifecycle": response.get("mcp_lifecycle"),
        "lean_lsp_mcp": response.get("lean_lsp_mcp"),
        "run_mode": "task" if task_ref else "group",
        "group_id": group_id,
        "task_ref": task_ref,
        "suite": suite,
        "started_at": started_at,
        "base_url": base_url,
        "transport_mode": _transport_mode(),
        "streaming_fallback_reason": _streaming_fallback_reason(),
        "auth_mode": "env" if _api_key() else "none",
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": response["status"],
        "failure_class": response.get("failure_class"),
        "provider_setup_error": bool(response.get("provider_setup_error")),
        "mcp_setup_error": bool(response.get("mcp_setup_error")),
        "mcp_preflight": response.get("mcp_preflight"),
        "provider_preflight": response.get("preflight"),
        "usage": response.get("usage"),
        "benchmark_budget": benchmark_budget,
        "operational_budget": budgets["operational_budget"],
        "failure_counts": response.get("failure_counts") or ({str(response.get("failure_class")): 1} if response.get("failure_class") else {}),
        "classification": classification,
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
        print(json.dumps(endpoint_smoke(DEFAULT_BASE_URL, DEFAULT_DRIVER_MODEL), indent=2))
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
