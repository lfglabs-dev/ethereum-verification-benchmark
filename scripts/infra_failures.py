#!/usr/bin/env python3
"""Detect provider/transport infrastructure failures in benchmark run artifacts.

A benchmark verdict is only meaningful if the model was actually given a fair
chance to answer. When the provider transport fails terminally mid-run -- an
HTTP 402 credit outage, a Cloudflare ``524`` origin timeout, a client request
timeout, or missing credentials -- the harness still finalizes the run and the
verifier still emits a verdict (usually ``no_submission`` or a stale partial
proof). Scoring that verdict as a *genuine model failure* is wrong: it measures
the provider's availability, not the model's capability.

This module is the single, deterministic source of truth for classifying a run
as *infrastructure-invalid*. It is intentionally offline (reads artifacts only,
never calls a provider) and conservative: a transient error that the transport
*retried and recovered from* does not invalidate the verdict -- only a terminal
failure that actually cost the model a turn does.

Signals, in order of preference:

1. ``harness-response.json`` -- the runner records a per-task ``status`` and
   ``failure_class``. ``provider_or_context_failure`` (emitted for
   ``request_failed`` / ``request_timeout`` / ``missing_credentials``) is the
   authoritative marker.
2. ``conversations/*.jsonl`` -- a fallback for archives that predate the
   harness-response artifact. A record with ``status == "request_failed"`` is a
   terminal transport failure (all retries exhausted). ``request_retry`` records
   that are followed by ``request_retry_succeeded`` are *not* terminal and never
   invalidate the run.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable

# Verifier verdicts that reflect a real, graded model result: the model submitted work
# and the verifier reached a genuine verdict about it. These are *never* infrastructure-
# invalid, even when a later turn hit transport noise after the gradeable work was
# produced -- the model already had, and used, a fair turn. Trusting a terminal transport
# status over one of these verdicts over-counts genuine model failures as infra outages.
GENUINE_VERDICT_STATUSES = frozenset(
    {
        "passed",
        "lean_check_failed",
        "failed",
        "forbidden_placeholder",
        "rejected_forbidden_placeholder",
        "theorem_statement_mismatch",
        "hidden_import",
        "timeout",
        "deterministic_timeout",
    }
)

# Non-gradeable verdicts: the model produced nothing the verifier could grade. Only these
# are eligible for infra-invalidation, and only when a terminal transport failure denied a
# model that had not already completed genuine work (see ``_has_genuine_work``).
NON_GRADEABLE_VERDICT_STATUSES = frozenset(
    {"no_submission", "not_runnable", "missing_candidate", "theorem_missing", "reference_declaration_missing"}
)

# Per-task harness statuses that mean the model never got a fair, completed turn.
INFRA_TASK_STATUSES = frozenset({"request_failed", "request_timeout", "missing_credentials"})

# The runner's failure_class bucket for the statuses above (harness/runners/lean_tools.py).
INFRA_FAILURE_CLASSES = frozenset({"provider_or_context_failure"})

# transport_request.py error ``kind`` values that denote a provider/transport fault.
TRANSPORT_FAILURE_KINDS = frozenset(
    {"http_transient", "http_error", "request_timeout", "transport_error", "context_length_exceeded"}
)

# Terminal transport record marker written by transport_request.py once retries are exhausted.
_TERMINAL_RECORD_STATUS = "request_failed"


def _load_json(path: Path) -> Any | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def _harness_response_reason(run_dir: Path) -> str | None:
    response = _load_json(run_dir / "harness-response.json")
    if not isinstance(response, dict):
        return None
    tasks = response.get("tasks")
    if not isinstance(tasks, list):
        return None
    for task in tasks:
        if not isinstance(task, dict):
            continue
        status = str(task.get("status") or "").strip().lower()
        failure_class = str(task.get("failure_class") or "").strip().lower()
        if status in INFRA_TASK_STATUSES:
            return f"harness task status={status}"
        if failure_class in INFRA_FAILURE_CLASSES:
            return f"harness failure_class={failure_class}"
    return None


def _conversation_reason(run_dir: Path) -> str | None:
    conversations = run_dir / "conversations"
    if not conversations.is_dir():
        return None
    for jsonl in sorted(conversations.glob("*.jsonl")):
        try:
            lines = jsonl.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for line in lines:
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(record, dict):
                continue
            if str(record.get("status") or "").strip().lower() != _TERMINAL_RECORD_STATUS:
                continue
            error = record.get("error") if isinstance(record.get("error"), dict) else {}
            kind = str(error.get("kind") or "").strip().lower()
            last_status = error.get("last_status")
            return f"terminal transport failure: kind={kind or 'unknown'} last_status={last_status}"
    return None


def _verdict_statuses(run: dict[str, Any]) -> list[str]:
    """Return the lower-cased verifier target statuses recorded in ``run.json``."""
    verifier = run.get("verifier") if isinstance(run.get("verifier"), dict) else None
    if not isinstance(verifier, dict):
        return []
    targets = verifier.get("targets")
    statuses: list[str] = []
    if isinstance(targets, list):
        for target in targets:
            if isinstance(target, dict):
                statuses.append(str(target.get("status") or "").strip().lower())
    return statuses


def _has_genuine_work(run_dir: Path | None) -> bool:
    """True if the run produced a gradeable candidate (a verifier attempt actually ran).

    A non-gradeable *verdict* (``no_submission`` / ``theorem_missing``) can still sit on
    top of genuine model work: the model may have submitted candidates that the verifier
    checked (``attempts`` with a Lean status / candidate path) before a tail-turn transport
    failure. Such a run reflects real capability, so it must not be scored as infra-invalid
    even though the *final* verdict is non-gradeable.
    """
    if run_dir is None:
        return False
    response = _load_json(run_dir / "harness-response.json")
    if not isinstance(response, dict):
        return False
    tasks = response.get("tasks")
    if not isinstance(tasks, list):
        return False
    for task in tasks:
        if not isinstance(task, dict):
            continue
        attempts = task.get("attempts")
        if not isinstance(attempts, list):
            continue
        for attempt in attempts:
            if isinstance(attempt, dict) and (attempt.get("status") or attempt.get("candidate_path")):
                return True
    return False


def provider_failure_reason(run: dict[str, Any], run_dir: Path | None) -> str | None:
    """Return a human-readable reason when a run's verdict is infrastructure-invalid, else ``None``.

    ``run`` is the parsed ``run.json`` (used for the verifier verdict); ``run_dir`` is the
    artifact directory holding ``harness-response.json`` and ``conversations/`` (may be
    ``None`` when only the manifest row is available).

    The classification is verdict- and work-aware, never transport-blind:

    * A genuine graded verdict (``passed`` / ``lean_check_failed`` / ``forbidden_placeholder``
      / statement mismatch / verifier ``timeout`` / ...) means the model got and used a fair
      turn. It is genuine regardless of tail-turn transport noise -- return ``None``.
    * A non-gradeable verdict (``no_submission`` / ``theorem_missing``) is infra-invalid only
      when the model had *not* already completed genuine work; if a verifier attempt ran on a
      submitted candidate, the run is genuine -- return ``None``.
    * Otherwise, a terminal transport failure that actually cost the model its turn makes the
      non-gradeable verdict infrastructure-invalid.
    """
    verdicts = _verdict_statuses(run)
    if any(status in GENUINE_VERDICT_STATUSES for status in verdicts):
        return None
    if _has_genuine_work(run_dir):
        return None
    if run_dir is not None:
        reason = _harness_response_reason(run_dir)
        if reason:
            return reason
        reason = _conversation_reason(run_dir)
        if reason:
            return reason
    return None


def transport_failure_summary(run_dir: Path | None) -> dict[str, int]:
    """Count transport error records (``retry`` / ``recovered`` / ``terminal``) for reporting."""
    summary = {"retries": 0, "recovered": 0, "terminal": 0}
    if run_dir is None:
        return summary
    conversations = run_dir / "conversations"
    if not conversations.is_dir():
        return summary
    for jsonl in sorted(conversations.glob("*.jsonl")):
        try:
            lines = jsonl.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for record in _iter_json_lines(lines):
            status = str(record.get("status") or "").strip().lower()
            if status == "request_retry":
                summary["retries"] += 1
            elif status == "request_retry_succeeded":
                summary["recovered"] += 1
            elif status == _TERMINAL_RECORD_STATUS:
                summary["terminal"] += 1
    return summary


def _iter_json_lines(lines: Iterable[str]) -> Iterable[dict[str, Any]]:
    for line in lines:
        line = line.strip()
        if not line:
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(record, dict):
            yield record
