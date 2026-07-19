from __future__ import annotations

from collections import Counter
from typing import Any


ALLOWED_TERMINAL_STATUSES = {
    "lean_passed",
    "completed_with_failures",
    "failed_submitted",
    "failed_no_attempt",
    "failed_no_tool_calls",
    "malformed_tool_call",
    "invalid_tool_call",
    "request_timeout",
    "request_failed",
    "strict_writer_exhausted",
    "context_budget_exhausted",
    "context_length_exceeded",
    "max_attempts_exceeded",
    "max_turns_exceeded",
    "max_tool_calls_exceeded",
    "repetition_loop",
}

PROVIDER_SETUP_STATUSES = {"missing_credentials", "provider_setup_error", "preflight_failed"}


def failure_taxonomy(status: str, attempts: list[dict[str, object]], *, tool_calls: int = 0, no_tool_responses: int = 0) -> str:
    if status in {"missing_credentials", "provider_setup_error", "preflight_failed"}:
        return "provider_setup_error"
    if status in {"request_timeout", "request_failed", "context_budget_exhausted", "context_length_exceeded"}:
        return status
    if status in {"malformed_tool_call", "invalid_tool_call"}:
        return "malformed_tool_call"
    if status in {"max_attempts_exceeded", "max_turns_exceeded", "max_tool_calls_exceeded", "repetition_loop"}:
        return status
    if status == "failed_no_tool_calls" or (tool_calls == 0 and not attempts):
        return "no_tool_calls"
    outputs = "\n".join(str(attempt.get("output", "")) for attempt in attempts)
    kinds = [str(attempt.get("failure_kind")) for attempt in attempts if attempt.get("failure_kind")]
    if "forbidden_placeholder" in kinds:
        return "forbidden_placeholder"
    if "lean_unknown_name" in kinds or "unknown identifier" in outputs.lower() or "unknown constant" in outputs.lower():
        return "unknown_identifier"
    if "lean_unsolved_goals" in kinds or "unsolved goals" in outputs.lower():
        return "lean_unsolved_goal"
    if no_tool_responses:
        return "no_tool_calls"
    return "lean_unsolved_goal" if attempts else "no_tool_calls"


def failure_counts_from_tasks(tasks: list[dict[str, Any]]) -> dict[str, int]:
    counts = Counter(str(task.get("failure_class")) for task in tasks if task.get("failure_class"))
    return dict(sorted(counts.items()))


def row_validity(row: dict[str, Any], *, expected_budget: dict[str, Any] | None = None) -> dict[str, object]:
    status = str(row.get("status") or row.get("harness_status") or "")
    errors: list[str] = []
    if status not in ALLOWED_TERMINAL_STATUSES and status != "completed":
        errors.append(f"terminal status {status!r} is not allowed")
    if status in PROVIDER_SETUP_STATUSES or row.get("provider_setup_error"):
        errors.append("provider setup error")
    if status == "strict_writer_exhausted" and row.get("failure_class") != "provider_or_context_failure":
        errors.append("strict writer exhaustion is not a provider or context failure")
    usage = row.get("usage")
    requests = None
    total_tokens = None
    if isinstance(usage, dict):
        requests = usage.get("requests")
        total_tokens = usage.get("total_tokens")
    tool_calls = row.get("tool_calls_executed", row.get("tool_calls"))
    attempts = row.get("attempts")
    has_request_activity = bool(
        (isinstance(requests, (int, float)) and requests > 0)
        or (isinstance(tool_calls, (int, float)) and tool_calls > 0)
        or (isinstance(attempts, list) and attempts)
    )
    if status == "lean_passed" and not has_request_activity and not row.get("verifier_confirmed"):
        errors.append("completed model row has no request activity")
    if status == "lean_passed" and isinstance(usage, dict) and requests not in {None, 0}:
        if not isinstance(total_tokens, (int, float)) or total_tokens <= 0:
            errors.append("provider reported usage but completed row has zero total tokens")
    role_metrics = row.get("role_metrics")
    role_config = role_metrics.get("role_config") if isinstance(role_metrics, dict) else None
    strict_hybrid = bool(
        row.get("strict_role_separation") is True
        or isinstance(role_config, dict) and role_config.get("strict_role_separation") is True
    )
    if strict_hybrid:
        writer_calls = role_metrics.get("prover_writer_calls", 0) if isinstance(role_metrics, dict) else 0
        if not isinstance(writer_calls, (int, float)) or writer_calls <= 0:
            errors.append("strict-hybrid row has no prover writer routing")
        prover_submission = any(
            isinstance(attempt, dict)
            and attempt.get("prover_derived") is True
            and attempt.get("status") in {"lean_passed", "lean_failed"}
            for attempt in attempts
        ) if isinstance(attempts, list) else False
        writer_exhausted = (
            status == "strict_writer_exhausted"
            and row.get("failure_class") == "provider_or_context_failure"
        )
        if not prover_submission and not writer_exhausted:
            errors.append("strict-hybrid row has no prover-derived accepted submission")
    if expected_budget is not None:
        observed_budget = row.get("benchmark_budget")
        if observed_budget != expected_budget:
            errors.append("benchmark budget does not match manifest")
    return {"valid": not errors, "errors": errors}
