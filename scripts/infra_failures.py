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


def provider_failure_reason(run: dict[str, Any], run_dir: Path | None) -> str | None:
    """Return a human-readable reason when a run's verdict is infrastructure-invalid, else ``None``.

    ``run`` is the parsed ``run.json`` (used for lightweight, path-free signals);
    ``run_dir`` is the artifact directory holding ``harness-response.json`` and
    ``conversations/`` (may be ``None`` when only the manifest row is available).
    """
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
