from __future__ import annotations

from collections import Counter
from typing import Any


INFRA_FAILURE_KINDS = {
    "context_budget_exhausted",
    "context_length_exceeded",
    "http_error",
    "http_transient",
    "provider_or_context_failure",
    "request_failed",
    "request_timeout",
    "transport_error",
}

TERMINAL_REQUEST_STATUSES = {
    "context_budget_exhausted",
    "request_failed",
    "request_timeout",
}

# Terminal statuses where the provider/model never produced a usable tool call
# at all: `failed_no_tool_calls` is the no-tool-response limit (chat-template
# degeneration — the model emits template sentinels instead of tool calls);
# `malformed_tool_call`/`invalid_tool_call` mean it could not form a valid call
# even after a corrective reprompt. With no gradeable submission these are
# provider/tool-protocol breakdowns, not proof failures by the model, so they
# must not count as GENUINE_FAIL evidence. Note this is deliberately narrow:
# `failed_no_attempt` (the model made real tool calls but never submitted a
# proof) is a genuine give-up and stays GENUINE_FAIL.
TOOL_PROTOCOL_BREAKDOWN_STATUSES = {
    "failed_no_tool_calls",
    "malformed_tool_call",
    "invalid_tool_call",
}

NON_GRADEABLE_ATTEMPT_STATUSES = {
    "rejected_candidate",
    "rejected_forbidden_placeholder",
    "rejected_statement_mismatch",
}

# Attempt statuses where the model produced a submission the harness declined to
# run against Lean (placeholder/forbidden token, or a statement that no longer
# matches the target theorem). These are real model output, but never a graded
# proof, so they read as "placeholder" rather than "no submission".
PLACEHOLDER_ATTEMPT_STATUSES = {
    "rejected_forbidden_placeholder",
    "rejected_statement_mismatch",
}

# Coarse, model-agnostic description of how far the model got before the
# verifier ran. Orthogonal to final_class: it summarizes the in-loop submission
# funnel (did the model submit anything, was it a placeholder, did check_proof
# actually run, and did it pass) so genuine proof failures can be told apart
# from give-ups and provider/tool breakdowns without reading raw transcripts.
SUBMISSION_STATE_NO_SUBMISSION = "no_submission"
SUBMISSION_STATE_PLACEHOLDER = "placeholder_submission"
SUBMISSION_STATE_CHECK_FAILED = "check_proof_failed"
SUBMISSION_STATE_CHECK_PASSED = "check_proof_passed"
SUBMISSION_STATE_UNKNOWN = "unknown"

# Verifier build statuses that can be caused by a shared *support* module (one
# the agent never edits) failing to build, rather than by the submitted proof.
SUPPORT_MODULE_FAILURE_STATUSES = {
    "lean_check_failed",
    "timeout",
}

# Prefixes of Lean modules that are shipped read-only to every workspace. When
# the verifier build dies inside one of these, no submitted proof was ever
# elaborated, so the target is not model evidence regardless of any attempts.
SUPPORT_MODULE_PREFIXES = (
    "Benchmark.Grindset",
    "Verity.",
)


def _is_support_module(module: str) -> bool:
    return any(
        module == prefix or module.startswith(prefix if prefix.endswith(".") else prefix + ".")
        for prefix in SUPPORT_MODULE_PREFIXES
    )


LAKE_FAILURE_HEADER = "Some required builds logged failures:"


def _failed_build_modules(output: str) -> list[str]:
    """Modules named under Lake's ``Some required builds logged failures:``.

    Only bullets inside that footer count: stray ``- `` bullets elsewhere in a
    Lean diagnostic must not feed the support-module guard.
    """
    modules: list[str] = []
    in_footer = False
    for line in output.splitlines():
        stripped = line.strip()
        if stripped == LAKE_FAILURE_HEADER:
            in_footer = True
            continue
        if not in_footer:
            continue
        if stripped.startswith("- "):
            candidate = stripped[2:].strip()
            if candidate and all(part.isidentifier() for part in candidate.split(".")):
                modules.append(candidate)
        else:
            in_footer = False
    return modules


def _support_module_build_failure(verifier_target: dict[str, Any] | None) -> str | None:
    """Return the offending support module if a target failed because a shared,
    non-editable module failed to build; otherwise ``None``.

    Guards against a support-layer build break (e.g. the ``Benchmark.Grindset``
    umbrella failing to import) being misread as a genuine proof failure. The
    check is deliberately conservative: it only fires when *every* module Lake
    reported as failed is a support module, so a real error in the submitted
    task module never gets excused.
    """
    if not isinstance(verifier_target, dict):
        return None
    if _target_status(verifier_target) not in SUPPORT_MODULE_FAILURE_STATUSES:
        return None
    output = verifier_target.get("output")
    if not isinstance(output, str) or not output:
        return None
    modules = _failed_build_modules(output)
    if not modules or not all(_is_support_module(module) for module in modules):
        return None
    return modules[0]


def _target_status(target: dict[str, Any] | None) -> str | None:
    status = target.get("status") if isinstance(target, dict) else None
    return str(status) if status is not None else None


def _score_passed(verifier: dict[str, Any]) -> bool:
    score = verifier.get("score")
    if not isinstance(score, dict):
        return False
    total = score.get("total_targets")
    passed = score.get("passed_targets")
    return isinstance(total, int) and total > 0 and passed == total


def _is_terminal_request_failure(task_result: dict[str, Any] | None) -> bool:
    if not isinstance(task_result, dict):
        return False
    status = str(task_result.get("status") or "")
    failure_class = str(task_result.get("failure_class") or "")
    error = task_result.get("error")
    error_kind = str(error.get("kind") or "") if isinstance(error, dict) else ""
    return (
        status in TERMINAL_REQUEST_STATUSES
        or failure_class in INFRA_FAILURE_KINDS
        or error_kind in INFRA_FAILURE_KINDS
    )


def _is_tool_protocol_breakdown(task_result: dict[str, Any] | None) -> bool:
    if not isinstance(task_result, dict):
        return False
    return str(task_result.get("status") or "") in TOOL_PROTOCOL_BREAKDOWN_STATUSES


def _tool_protocol_breakdown_reason(task_result: dict[str, Any] | None) -> str:
    if not isinstance(task_result, dict):
        return "provider_invalid_tool_protocol"
    marker = task_result.get("failure_class") or task_result.get("status")
    return f"provider_invalid_tool_protocol:{marker}"


def _request_failure_reason(task_result: dict[str, Any] | None) -> str | None:
    if not isinstance(task_result, dict):
        return None
    error = task_result.get("error")
    if isinstance(error, dict):
        kind = error.get("kind") or task_result.get("failure_class") or task_result.get("status")
        last_status = error.get("last_status")
        return f"terminal_request_failed:{kind}:{last_status}"
    status = task_result.get("status")
    failure_class = task_result.get("failure_class")
    if status or failure_class:
        return f"terminal_request_failed:{failure_class or status}:None"
    return None


def _has_gradeable_submission(task_result: dict[str, Any] | None) -> bool:
    if not isinstance(task_result, dict):
        return False
    if task_result.get("status") in {"lean_passed", "failed_submitted"}:
        return True
    attempts = task_result.get("attempts")
    if not isinstance(attempts, list):
        return False
    for attempt in attempts:
        if not isinstance(attempt, dict):
            continue
        status = str(attempt.get("status") or "")
        if status and status not in NON_GRADEABLE_ATTEMPT_STATUSES:
            return True
        if attempt.get("candidate_path"):
            return True
    return False


def submission_state(task_result: dict[str, Any] | None) -> str:
    """Summarize how far the model's proof funnel got, independent of the verifier.

    Distinguishes: never submitted a proof, only placeholder/rejected
    submissions, submitted a proof that ``check_proof`` ran and failed, or one
    that passed. Provider/tool breakdowns that never yield an attempt read as
    ``no_submission``; the verifier + ``final_class`` still capture the infra
    reason separately.
    """
    if not isinstance(task_result, dict):
        return SUBMISSION_STATE_UNKNOWN
    status = str(task_result.get("status") or "")
    attempts = task_result.get("attempts")
    attempts = attempts if isinstance(attempts, list) else []

    saw_lean_pass = status == "lean_passed"
    saw_lean_fail = False
    saw_placeholder = False
    for attempt in attempts:
        if not isinstance(attempt, dict):
            continue
        attempt_status = str(attempt.get("status") or "")
        if attempt_status == "lean_passed":
            saw_lean_pass = True
        elif attempt_status == "lean_failed":
            saw_lean_fail = True
        elif attempt_status in PLACEHOLDER_ATTEMPT_STATUSES:
            saw_placeholder = True
        elif attempt_status not in NON_GRADEABLE_ATTEMPT_STATUSES and (
            attempt_status or attempt.get("candidate_path")
        ):
            # An attempt the harness graded but whose status label we do not
            # recognize: treat a non-zero exit code as a failed check, else a
            # pass. Falls back to "failed" so we never over-report success.
            if attempt.get("exit_code") in (0, None) and attempt_status == "lean_passed":
                saw_lean_pass = True
            else:
                saw_lean_fail = True

    if saw_lean_pass:
        return SUBMISSION_STATE_CHECK_PASSED
    if saw_lean_fail:
        return SUBMISSION_STATE_CHECK_FAILED
    if saw_placeholder:
        return SUBMISSION_STATE_PLACEHOLDER
    return SUBMISSION_STATE_NO_SUBMISSION


def classify_target(
    verifier_target: dict[str, Any],
    task_result: dict[str, Any] | None,
) -> dict[str, Any]:
    """Publication-safety classification for one verifier target.

    The independent verifier remains the proof authority. This layer only says
    whether a failed verifier label is reusable as model evidence when the
    provider/tool loop failed before producing a gradeable submission.
    """

    raw_status = _target_status(verifier_target)
    state = submission_state(task_result)
    if raw_status == "passed":
        return {
            "final_class": "SOLVED",
            "final_reason": "verifier_passed",
            "reusable": True,
            "raw_verifier_status": raw_status,
            "submission_state": state,
            "verifier_outcome": "passed",
        }

    terminal_request_failure = _is_terminal_request_failure(task_result)
    gradeable_submission = _has_gradeable_submission(task_result)
    if terminal_request_failure and not gradeable_submission:
        return {
            "final_class": "INFRA_INVALID",
            "final_reason": _request_failure_reason(task_result) or "terminal_request_failed",
            "reusable": False,
            "raw_verifier_status": raw_status,
            "submission_state": state,
            "verifier_outcome": "not_run_terminal_request_failure",
        }

    if _is_tool_protocol_breakdown(task_result) and not gradeable_submission:
        return {
            "final_class": "INFRA_INVALID",
            "final_reason": _tool_protocol_breakdown_reason(task_result),
            "reusable": False,
            "raw_verifier_status": raw_status,
            "submission_state": state,
            "verifier_outcome": "not_run_tool_protocol_breakdown",
        }

    support_module = _support_module_build_failure(verifier_target)
    if support_module is not None:
        return {
            "final_class": "INFRA_INVALID",
            "final_reason": f"support_module_build_failure:{support_module}",
            "reusable": False,
            "raw_verifier_status": raw_status,
            "submission_state": state,
            "verifier_outcome": "support_module_failure",
        }

    return {
        "final_class": "GENUINE_FAIL",
        "final_reason": raw_status or "verifier_failed",
        "reusable": True,
        "raw_verifier_status": raw_status,
        "submission_state": state,
        "verifier_outcome": "task_failure",
    }


def classify_run(verifier: dict[str, Any], task_results: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    tasks_by_ref = {
        str(task.get("task_ref")): task
        for task in (task_results or [])
        if isinstance(task, dict) and task.get("task_ref") is not None
    }
    targets = verifier.get("targets") if isinstance(verifier, dict) else None
    target_classes: list[dict[str, Any]] = []
    if isinstance(targets, list):
        for target in targets:
            if not isinstance(target, dict):
                continue
            task_ref = target.get("task_ref")
            task_result = tasks_by_ref.get(str(task_ref)) if task_ref is not None else None
            entry = {"task_ref": task_ref, **classify_target(target, task_result)}
            target_classes.append(entry)

    counts = Counter(str(item["final_class"]) for item in target_classes)
    submission_state_counts = Counter(
        str(item.get("submission_state") or SUBMISSION_STATE_UNKNOWN) for item in target_classes
    )
    verifier_outcome_counts = Counter(
        str(item.get("verifier_outcome")) for item in target_classes if item.get("verifier_outcome")
    )
    reusable_targets = [item for item in target_classes if item.get("reusable")]
    if target_classes and counts.get("INFRA_INVALID", 0) == len(target_classes):
        run_class = "INFRA_INVALID"
    elif _score_passed(verifier):
        run_class = "SOLVED"
    elif counts.get("INFRA_INVALID", 0):
        run_class = "MIXED_INFRA_INVALID"
    else:
        run_class = "GENUINE_FAIL"

    return {
        "schema_version": 1,
        "policy": (
            "Verifier-passing targets remain solved. Terminal provider/context/"
            "transport/request failures before a gradeable submission are "
            "INFRA_INVALID and non-reusable; verifier failures after gradeable "
            "submissions remain genuine proof failures."
        ),
        "run_class": run_class,
        "reusable": bool(target_classes) and all(bool(item.get("reusable")) for item in target_classes),
        "final_class_counts": dict(sorted(counts.items())),
        "submission_state_counts": dict(sorted(submission_state_counts.items())),
        "verifier_outcome_counts": dict(sorted(verifier_outcome_counts.items())),
        "reusable_target_count": len(reusable_targets),
        "non_reusable_target_count": len(target_classes) - len(reusable_targets),
        "targets": target_classes,
    }
