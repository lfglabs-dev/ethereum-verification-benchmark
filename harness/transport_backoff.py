"""Retry and backoff helpers for chat transport."""

from __future__ import annotations

TRANSIENT_HTTP_STATUS = {408, 409, 425, 429, 500, 502, 503, 504, 520, 521, 522, 523, 524}


def is_transient_http_status(status: int) -> bool:
    return status in TRANSIENT_HTTP_STATUS


def retry_delay_seconds(
    *,
    attempt: int,
    base_delay_seconds: float,
    retry_after_seconds: float | None,
    max_delay_seconds: float = 120.0,
    max_retry_after_seconds: float = 300.0,
) -> float:
    delay = min(max_delay_seconds, base_delay_seconds * (2 ** (attempt - 1)))
    if retry_after_seconds is not None:
        delay = min(max_retry_after_seconds, max(delay, retry_after_seconds))
    return delay

