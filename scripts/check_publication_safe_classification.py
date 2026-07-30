#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.classification import classify_run
from scripts.aggregate_runs import _model_summary


def _verifier(status: str) -> dict[str, object]:
    passed = 1 if status == "passed" else 0
    return {
        "score": {
            "points_earned": passed,
            "points_possible": 1,
            "passed_targets": passed,
            "total_targets": 1,
        },
        "targets": [{"task_ref": "sample/group/task", "status": status, "points": 1}],
    }


def _request_failed(kind: str, status: int | None = None) -> dict[str, object]:
    return {
        "task_ref": "sample/group/task",
        "status": "request_failed",
        "error": {
            "message": f"synthetic {kind}",
            "kind": kind,
            "attempts": 1,
            "timeout_seconds": 180,
            "transient": kind != "context_length_exceeded",
            "last_status": status,
        },
        "attempts": [],
        "failure_class": "provider_or_context_failure",
    }


def _single_class(result: dict[str, object]) -> str:
    targets = result.get("targets")
    if not isinstance(targets, list) or not targets:
        raise AssertionError("classification missing targets")
    first = targets[0]
    if not isinstance(first, dict):
        raise AssertionError("classification target is not an object")
    return str(first.get("final_class"))


def main() -> int:
    errors: list[str] = []

    context_before_submission = classify_run(
        _verifier("forbidden_placeholder"),
        [_request_failed("context_length_exceeded", 400)],
    )
    if _single_class(context_before_submission) != "INFRA_INVALID":
        errors.append("context_length_exceeded before submission should be INFRA_INVALID")
    if context_before_submission.get("reusable") is not False:
        errors.append("context_length_exceeded before submission should be non-reusable")

    transient_502 = classify_run(
        _verifier("theorem_missing"),
        [_request_failed("http_transient", 502)],
    )
    if _single_class(transient_502) != "INFRA_INVALID":
        errors.append("HTTP 502 before submission should be INFRA_INVALID")

    placeholder_after_request_failure = classify_run(
        _verifier("forbidden_placeholder"),
        [_request_failed("transport_error", None)],
    )
    if _single_class(placeholder_after_request_failure) != "INFRA_INVALID":
        errors.append("raw forbidden_placeholder after request failure should not be a model proof failure")

    genuine_placeholder = classify_run(
        _verifier("forbidden_placeholder"),
        [{"task_ref": "sample/group/task", "status": "failed_no_attempt", "attempts": []}],
    )
    if _single_class(genuine_placeholder) != "GENUINE_FAIL":
        errors.append("forbidden_placeholder without terminal request failure should remain a genuine verifier failure")
    if genuine_placeholder.get("reusable") is not True:
        errors.append("genuine verifier failure should remain reusable")

    passed_after_transport_noise = classify_run(
        _verifier("passed"),
        [_request_failed("http_transient", 502)],
    )
    if _single_class(passed_after_transport_noise) != "SOLVED":
        errors.append("passed verifier result should remain solved even with late transport noise")

    gradeable_then_request_failure = classify_run(
        _verifier("timeout"),
        [
            {
                **_request_failed("http_transient", 500),
                "attempts": [{"status": "lean_failed", "candidate_path": "attempts/sample.lean"}],
            }
        ],
    )
    if _single_class(gradeable_then_request_failure) != "INFRA_INVALID":
        errors.append("verifier timeout after a gradeable submission should fail closed as INFRA_INVALID")

    tool_call_degeneration = classify_run(
        _verifier("no_submission"),
        [
            {
                "task_ref": "sample/group/task",
                "status": "failed_no_tool_calls",
                "failure_class": "no_tool_calls",
                "no_tool_responses": 7,
                "attempts": [],
            }
        ],
    )
    if _single_class(tool_call_degeneration) != "INFRA_INVALID":
        errors.append("tool-call degeneration with no gradeable submission should be INFRA_INVALID")
    if tool_call_degeneration.get("reusable") is not False:
        errors.append("tool-call degeneration should be non-reusable")

    degeneration_after_submission = classify_run(
        _verifier("lean_check_failed"),
        [
            {
                "task_ref": "sample/group/task",
                "status": "failed_no_tool_calls",
                "failure_class": "no_tool_calls",
                "no_tool_responses": 3,
                "attempts": [{"status": "lean_failed", "candidate_path": "attempts/sample.lean"}],
            }
        ],
    )
    if _single_class(degeneration_after_submission) != "GENUINE_FAIL":
        errors.append("a late no-tool turn must not launder a gradeable failure into infra-invalid")

    summary = _model_summary(
        [
            {
                "valid": True,
                "reusable": False,
                "passed": False,
                "cost_usd": 1.0,
                "completion_tokens": 100,
                "prompt_tokens": 100,
                "attempts": 1,
            },
            {
                "valid": True,
                "reusable": True,
                "passed": True,
                "cost_usd": 0.5,
                "completion_tokens": 10,
                "prompt_tokens": 20,
                "attempts": 1,
            },
        ]
    )
    if summary.get("reusable_tasks") != 1 or summary.get("passed") != 1 or summary.get("infra_invalid") != 1:
        errors.append("aggregate summaries should exclude infra-invalid rows from reusable pass-rate denominators")

    if errors:
        print("\n".join(errors))
        return 1
    print("publication-safe classification checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
