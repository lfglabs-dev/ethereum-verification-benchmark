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

NON_GRADEABLE_ATTEMPT_STATUSES = {
    "rejected_candidate",
    "rejected_forbidden_placeholder",
}


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
    if raw_status == "passed":
        return {
            "final_class": "SOLVED",
            "final_reason": "verifier_passed",
            "reusable": True,
            "raw_verifier_status": raw_status,
        }

    terminal_request_failure = _is_terminal_request_failure(task_result)
    gradeable_submission = _has_gradeable_submission(task_result)
    if terminal_request_failure and not gradeable_submission:
        return {
            "final_class": "INFRA_INVALID",
            "final_reason": _request_failure_reason(task_result) or "terminal_request_failed",
            "reusable": False,
            "raw_verifier_status": raw_status,
        }

    return {
        "final_class": "GENUINE_FAIL",
        "final_reason": raw_status or "verifier_failed",
        "reusable": True,
        "raw_verifier_status": raw_status,
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
        "reusable_target_count": len(reusable_targets),
        "non_reusable_target_count": len(target_classes) - len(reusable_targets),
        "targets": target_classes,
    }
