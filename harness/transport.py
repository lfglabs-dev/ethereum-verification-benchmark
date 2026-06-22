"""OpenAI-compatible chat transport for the default harness.

Provider/env resolution, retrying chat completions, and response parsing.
Extracted from runners/lean_tools.py."""

from __future__ import annotations

import json
import os
import socket
import time
import urllib.request
import urllib.error
from urllib.parse import urlparse
from pathlib import Path
from typing import Any

DEFAULT_TOOL_RESULT_CHARS = int(os.environ.get("DEFAULT_HARNESS_TOOL_RESULT_CHARS", "6000"))


def _append_jsonl(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload) + "\n")


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

REQUEST_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS", os.environ.get("GAZELLA_REQUEST_TIMEOUT_SECONDS", "180")))

REQUEST_RETRIES = int(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRIES", os.environ.get("GAZELLA_REQUEST_RETRIES", "5")))

REQUEST_RETRY_BACKOFF_SECONDS = float(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS", os.environ.get("GAZELLA_REQUEST_RETRY_BACKOFF_SECONDS", "2")))

DEFAULT_CONTEXT_TOKENS = os.environ.get("DEFAULT_HARNESS_CONTEXT_TOKENS", os.environ.get("GAZELLA_N_CTX"))

DEFAULT_MAX_RESPONSE_TOKENS = int(os.environ.get("DEFAULT_HARNESS_MAX_RESPONSE_TOKENS", "8192"))

HTTP_USER_AGENT = os.environ.get("DEFAULT_HARNESS_HTTP_USER_AGENT", "ethereum-verification-benchmark-harness/1.0")

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

def _local_no_auth_endpoint(base_url: str) -> bool:
    host = urlparse(base_url).hostname
    return host in {"127.0.0.1", "localhost", "::1"}
