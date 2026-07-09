"""OpenAI-compatible request execution for the default harness."""

from __future__ import annotations

import json
import os
import socket
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from harness.identity import HARNESS_USER_AGENT
from harness.transport_backoff import is_transient_http_status, retry_delay_seconds
from harness.transport_errors import ChatCompletionError

DEFAULT_TOOL_RESULT_CHARS = int(os.environ.get("DEFAULT_HARNESS_TOOL_RESULT_CHARS", "6000"))


def append_jsonl(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload) + "\n")


def _sanitize_tool_message_order(messages: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Reorder messages so every assistant ``tool_calls`` turn is immediately
    followed by the ``tool`` replies answering each call id.

    The fair tool loop can interleave a corrective ``user`` message (e.g. the
    repetition warning) between an assistant ``tool_calls`` message and the
    ``tool`` result that follows. Lenient OpenAI-compatible/local endpoints
    accept that, but the official Mistral API rejects it with
    ``HTTP 400 invalid_request_message_order`` ("Unexpected role 'tool' after
    role 'user'"). We move the tool replies back next to their assistant turn
    and defer any interleaved non-tool message to just after them, and we
    synthesize an empty stub reply for any tool_call id that never got one so
    the call/response counts always match.

    Some endpoints omit ``tool_call.id``; the fair loop then records the real
    result under a fallback ``tool_call_id`` (``call-{request_index}``), so an
    unanswered call first consumes the next orphan tool reply (one whose id
    matches no assistant call) before falling back to an empty stub.
    """
    tool_slots: dict[str, list[int]] = {}
    for idx, message in enumerate(messages):
        if message.get("role") == "tool":
            tool_slots.setdefault(str(message.get("tool_call_id")), []).append(idx)

    known_call_ids = {
        str(call.get("id"))
        for message in messages
        if message.get("role") == "assistant" and isinstance(message.get("tool_calls"), list)
        for call in message["tool_calls"]
        if isinstance(call, dict)
    }

    used: set[int] = set()
    result: list[dict[str, Any]] = []
    for current_idx, message in enumerate(messages):
        if message.get("role") == "tool":
            continue  # emitted next to its originating assistant turn
        result.append(message)
        if message.get("role") != "assistant":
            continue
        tool_calls = message.get("tool_calls")
        if not isinstance(tool_calls, list):
            continue

        # Only fallback/orphan tool replies from this assistant turn's segment
        # may answer this assistant. A later assistant with a missing id can also
        # produce a fallback ``call-{request_index}`` reply; consuming that
        # globally for an earlier unanswered call would attach real tool output
        # to the wrong turn and hide the result that should guide the next
        # request.
        next_assistant_idx = next(
            (
                idx
                for idx in range(current_idx + 1, len(messages))
                if messages[idx].get("role") == "assistant"
            ),
            len(messages),
        )
        current_orphan_reply_indices = [
            idx
            for idx in range(current_idx + 1, next_assistant_idx)
            if messages[idx].get("role") == "tool"
            and str(messages[idx].get("tool_call_id")) not in known_call_ids
        ]
        for call in tool_calls:
            if not isinstance(call, dict):
                continue
            call_id = call.get("id")
            reply_idx = next(
                (i for i in tool_slots.get(str(call_id), []) if i not in used),
                None,
            )
            if reply_idx is None:
                reply_idx = next((i for i in current_orphan_reply_indices if i not in used), None)
            if reply_idx is not None:
                used.add(reply_idx)
                result.append(messages[reply_idx])
            else:
                function = call.get("function") if isinstance(call.get("function"), dict) else {}
                result.append(
                    {
                        "role": "tool",
                        "tool_call_id": call_id if isinstance(call_id, str) else "unknown",
                        "name": function.get("name", ""),
                        "content": "",
                    }
                )
    return result


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


def provider_env(name: str) -> str | None:
    if not DEFAULT_PROVIDER:
        return None
    value = os.environ.get(f"DEFAULT_HARNESS_{DEFAULT_PROVIDER.upper()}_{name}")
    return value if value not in {None, ""} else None


def provider_default(name: str, fallback: str) -> str:
    if not DEFAULT_PROVIDER:
        return fallback
    provider_defaults = PROVIDER_DEFAULTS.get(DEFAULT_PROVIDER, {})
    value = provider_defaults.get(name.lower())
    return str(value) if value else fallback


def harness_env(name: str, fallback: str, *, legacy_name: str | None = None) -> str:
    profile_value = provider_env(name)
    if profile_value is not None:
        return profile_value
    direct_value = os.environ.get(f"DEFAULT_HARNESS_{name}")
    if direct_value not in {None, ""}:
        return str(direct_value)
    if legacy_name:
        legacy_value = os.environ.get(legacy_name)
        if legacy_value not in {None, ""}:
            return str(legacy_value)
    return provider_default(name, fallback)


DEFAULT_BASE_URL = harness_env("BASE_URL", "https://spark-de79.gazella-vector.ts.net/v1", legacy_name="GAZELLA_BASE_URL")
DEFAULT_MODEL = harness_env("MODEL", "qwen3.5-397b", legacy_name="GAZELLA_MODEL")
REQUEST_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS", os.environ.get("GAZELLA_REQUEST_TIMEOUT_SECONDS", "180")))
STREAM_IDLE_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_STREAM_IDLE_TIMEOUT_SECONDS", os.environ.get("DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS", os.environ.get("GAZELLA_REQUEST_TIMEOUT_SECONDS", "180"))))
REQUEST_RETRIES = int(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRIES", os.environ.get("GAZELLA_REQUEST_RETRIES", "5")))
REQUEST_RETRY_BACKOFF_SECONDS = float(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS", os.environ.get("GAZELLA_REQUEST_RETRY_BACKOFF_SECONDS", "2")))
DEFAULT_CONTEXT_TOKENS = os.environ.get("DEFAULT_HARNESS_CONTEXT_TOKENS", os.environ.get("GAZELLA_N_CTX"))
DEFAULT_MAX_RESPONSE_TOKENS = int(os.environ.get("DEFAULT_HARNESS_MAX_RESPONSE_TOKENS", "8192"))
HTTP_USER_AGENT = os.environ.get("DEFAULT_HARNESS_HTTP_USER_AGENT", HARNESS_USER_AGENT)
DEFAULT_STREAMING_ENABLED = os.environ.get("DEFAULT_HARNESS_STREAMING", "1").strip().lower() not in {"0", "false", "no"}

# Chat-template sentinels that some GGUF servers (e.g. llama.cpp serving a
# ChatML fine-tune whose <|im_end|> is not registered as an EOG stop token)
# leak into the OpenAI `content` stream. Without them as explicit stop strings
# the model runs past its turn boundary and degenerates into generating the
# whole fake conversation. Sending them as `stop` halts generation at the turn
# boundary regardless of server-side template/EOG configuration.
_DEFAULT_STOP_SEQUENCES = (
    "<|im_end|>",
    "<|im_start|>",
    "<|tool_call_begin|>",
    "<|tool_call_end|>",
)


def _configured_stop_sequences() -> list[str]:
    raw = os.environ.get("DEFAULT_HARNESS_STOP_SEQUENCES")
    if raw is None:
        return list(_DEFAULT_STOP_SEQUENCES)
    # Newline-separated so sentinels containing commas/pipes survive intact;
    # empty value disables the default stop list entirely.
    return [line for line in (segment.strip() for segment in raw.split("\n")) if line]


DEFAULT_STOP_SEQUENCES = _configured_stop_sequences()
_streaming_fallback_reason: str | None = None


def api_key() -> str | None:
    return (
        provider_env("API_KEY")
        or os.environ.get("DEFAULT_HARNESS_API_KEY")
        or os.environ.get("GAZELLA_API_KEY")
        or os.environ.get("OPENAI_API_KEY")
    )


def active_provider() -> str:
    return DEFAULT_PROVIDER or "custom"


def build_chat_request(base_url: str, body: bytes, *, api_key_override: str | None = None) -> urllib.request.Request:
    request = urllib.request.Request(
        f"{base_url.rstrip('/')}/chat/completions",
        data=body,
        headers={"Content-Type": "application/json", "User-Agent": HTTP_USER_AGENT},
        method="POST",
    )
    key = api_key_override if api_key_override is not None else api_key()
    if key:
        request.add_header("Authorization", f"Bearer {key}")
    return request


def reset_transport_fallback() -> None:
    global _streaming_fallback_reason
    _streaming_fallback_reason = None


def disable_streaming_fallback(reason: str) -> None:
    global _streaming_fallback_reason
    _streaming_fallback_reason = reason


def streaming_fallback_reason() -> str | None:
    return _streaming_fallback_reason


def transport_mode() -> str:
    if not DEFAULT_STREAMING_ENABLED:
        return "non_streaming"
    if _streaming_fallback_reason:
        return "fallback_non_streaming"
    return "streaming"


def _streaming_allowed() -> bool:
    return DEFAULT_STREAMING_ENABLED and not _streaming_fallback_reason


def parse_retry_after(headers: Any) -> float | None:
    try:
        value = headers.get("Retry-After")
        return float(value) if value else None
    except (TypeError, ValueError):
        return None


def _is_streaming_rejection(status: int, detail: str) -> bool:
    lowered = detail.lower()
    if status in {400, 404, 405, 406, 415, 422}:
        return "stream" in lowered or "stream_options" in lowered
    return status == 501


def _append_delta_text(message: dict[str, Any], key: str, value: Any) -> None:
    if isinstance(value, str):
        message[key] = str(message.get(key) or "") + value


def _merge_tool_call_delta(tool_calls: list[dict[str, Any]], delta: dict[str, Any]) -> None:
    index = delta.get("index")
    if not isinstance(index, int):
        index = len(tool_calls)
    while len(tool_calls) <= index:
        tool_calls.append({"index": len(tool_calls), "function": {"name": "", "arguments": ""}})
    current = tool_calls[index]
    current["index"] = index
    for key in ("id", "type"):
        value = delta.get(key)
        if value is not None:
            current[key] = value
    function = delta.get("function")
    if isinstance(function, dict):
        current_function = current.setdefault("function", {})
        if isinstance(current_function, dict):
            name = function.get("name")
            if isinstance(name, str):
                current_function["name"] = str(current_function.get("name") or "") + name
            arguments = function.get("arguments")
            if isinstance(arguments, str):
                current_function["arguments"] = str(current_function.get("arguments") or "") + arguments


def _finalize_stream_choice(index: int, state: dict[str, Any]) -> dict[str, Any]:
    message = state.setdefault("message", {})
    if not isinstance(message, dict):
        message = {}
    message.setdefault("role", "assistant")
    message.setdefault("content", "")
    tool_calls = state.get("tool_calls")
    if isinstance(tool_calls, list) and tool_calls:
        message["tool_calls"] = tool_calls
        if message.get("content") == "":
            message["content"] = None
    choice: dict[str, Any] = {
        "index": index,
        "message": message,
        "finish_reason": state.get("finish_reason"),
    }
    return choice


def _decode_sse_response(response: Any) -> dict[str, object]:
    result: dict[str, Any] = {"choices": []}
    choices_by_index: dict[int, dict[str, Any]] = {}
    usage: dict[str, Any] | None = None
    metadata_keys = ("id", "object", "created", "model", "system_fingerprint")

    while True:
        raw_line = response.readline()
        if raw_line == b"" or raw_line == "":
            break
        line = raw_line.decode("utf-8", errors="replace") if isinstance(raw_line, bytes) else str(raw_line)
        line = line.strip()
        if not line or line.startswith(":") or not line.startswith("data:"):
            continue
        data = line[5:].strip()
        if data == "[DONE]":
            break
        chunk = json.loads(data)
        if not isinstance(chunk, dict):
            continue
        for key in metadata_keys:
            if key in chunk and key not in result:
                result[key] = chunk[key]
        chunk_usage = chunk.get("usage")
        if isinstance(chunk_usage, dict):
            usage = chunk_usage
        for choice in chunk.get("choices") or []:
            if not isinstance(choice, dict):
                continue
            index = choice.get("index", 0)
            if not isinstance(index, int):
                index = 0
            state = choices_by_index.setdefault(index, {"message": {"role": "assistant", "content": ""}})
            finish_reason = choice.get("finish_reason")
            if finish_reason is not None:
                state["finish_reason"] = finish_reason
            delta = choice.get("delta")
            if not isinstance(delta, dict):
                continue
            message = state.setdefault("message", {"role": "assistant", "content": ""})
            if not isinstance(message, dict):
                continue
            role = delta.get("role")
            if isinstance(role, str):
                message["role"] = role
            _append_delta_text(message, "content", delta.get("content"))
            _append_delta_text(message, "reasoning_content", delta.get("reasoning_content"))
            for tool_delta in delta.get("tool_calls") or []:
                if isinstance(tool_delta, dict):
                    tool_calls = state.setdefault("tool_calls", [])
                    if isinstance(tool_calls, list):
                        _merge_tool_call_delta(tool_calls, tool_delta)

    result["choices"] = [_finalize_stream_choice(index, choices_by_index[index]) for index in sorted(choices_by_index)]
    if usage is not None:
        result["usage"] = usage
    return result


def _execute_chat_request(base_url: str, payload: dict[str, Any], *, stream: bool, api_key_override: str | None = None) -> dict[str, object]:
    request_payload = dict(payload)
    if stream:
        request_payload["stream"] = True
        request_payload["stream_options"] = {"include_usage": True}
    body = json.dumps(request_payload).encode("utf-8")
    request = build_chat_request(base_url, body, api_key_override=api_key_override)
    timeout = STREAM_IDLE_TIMEOUT_SECONDS if stream else REQUEST_TIMEOUT_SECONDS
    with urllib.request.urlopen(request, timeout=timeout) as response:
        if stream:
            return _decode_sse_response(response)
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
    api_key_override: str | None = None,
) -> dict[str, object]:
    payload: dict[str, Any] = {
        "model": model,
        "messages": _sanitize_tool_message_order(messages),
        "max_tokens": max_tokens,
        "temperature": 0,
    }
    if DEFAULT_STOP_SEQUENCES:
        payload["stop"] = list(DEFAULT_STOP_SEQUENCES)
    if DEFAULT_CONTEXT_TOKENS:
        payload["n_ctx"] = int(DEFAULT_CONTEXT_TOKENS)
    if tools is not None:
        payload["tools"] = tools
    if tool_choice is not None:
        payload["tool_choice"] = tool_choice

    max_request_attempts = max(1, REQUEST_RETRIES + 1)
    last_error: ChatCompletionError | None = None
    retry_after_seconds: float | None = None
    for attempt in range(1, max_request_attempts + 1):
        retry_after_seconds = None
        started = time.time()
        stream = _streaming_allowed()
        try:
            decoded = _execute_chat_request(base_url, payload, stream=stream, api_key_override=api_key_override)
            if request_log_path is not None and attempt > 1:
                append_jsonl(
                    request_log_path,
                    {
                        "status": "request_retry_succeeded",
                        "request_index": request_index,
                        "attempt": attempt,
                        "duration_seconds": round(time.time() - started, 3),
                        "transport_mode": transport_mode(),
                    },
                )
            return decoded
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            classify_http_error = True
            if stream and _is_streaming_rejection(exc.code, detail):
                disable_streaming_fallback(f"HTTP {exc.code}: {detail[:300]}")
                if request_log_path is not None:
                    append_jsonl(
                        request_log_path,
                        {
                            "status": "streaming_rejected_fallback",
                            "request_index": request_index,
                            "attempt": attempt,
                            "duration_seconds": round(time.time() - started, 3),
                            "transport_mode": transport_mode(),
                        },
                    )
                started = time.time()
                try:
                    decoded = _execute_chat_request(base_url, payload, stream=False, api_key_override=api_key_override)
                    return decoded
                except urllib.error.HTTPError as fallback_exc:
                    detail = fallback_exc.read().decode("utf-8", errors="replace")
                    exc = fallback_exc
                except (TimeoutError, socket.timeout) as fallback_exc:
                    classify_http_error = False
                    last_error = ChatCompletionError(
                        f"request_timeout: {fallback_exc}",
                        kind="request_timeout",
                        attempts=attempt,
                        timeout_seconds=REQUEST_TIMEOUT_SECONDS,
                        transient=True,
                    )
                except (urllib.error.URLError, OSError) as fallback_exc:
                    classify_http_error = False
                    last_error = ChatCompletionError(
                        f"transport_error: {fallback_exc}",
                        kind="transport_error",
                        attempts=attempt,
                        timeout_seconds=REQUEST_TIMEOUT_SECONDS,
                        transient=True,
                    )
            if classify_http_error:
                transient = is_transient_http_status(exc.code)
                retry_after_seconds = parse_retry_after(exc.headers)
                kind = "context_length_exceeded" if "exceeds the available context size" in detail else ("http_transient" if transient else "http_error")
                last_error = ChatCompletionError(
                    f"HTTP {exc.code}: {detail[:1200]}",
                    kind=kind,
                    attempts=attempt,
                    timeout_seconds=REQUEST_TIMEOUT_SECONDS,
                    transient=transient,
                    last_status=exc.code,
                )
        except (TimeoutError, socket.timeout) as exc:
            timeout_seconds = STREAM_IDLE_TIMEOUT_SECONDS if stream else REQUEST_TIMEOUT_SECONDS
            last_error = ChatCompletionError(
                f"request_timeout: {exc}",
                kind="request_timeout",
                attempts=attempt,
                timeout_seconds=timeout_seconds,
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
            append_jsonl(
                request_log_path,
                {
                    "status": "request_retry" if last_error.transient and attempt < max_request_attempts else "request_failed",
                    "request_index": request_index,
                    "attempt": attempt,
                    "max_attempts": max_request_attempts,
                    "duration_seconds": round(time.time() - started, 3),
                    "error": last_error.to_dict(),
                    "transport_mode": transport_mode(),
                },
            )
        if last_error is None or not last_error.transient or attempt >= max_request_attempts:
            break
        time.sleep(
            retry_delay_seconds(
                attempt=attempt,
                base_delay_seconds=REQUEST_RETRY_BACKOFF_SECONDS,
                retry_after_seconds=retry_after_seconds,
            )
        )

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
            f"request_timeout after {last_error.attempts} attempt(s), timeout={last_error.timeout_seconds}s",
            kind=last_error.kind,
            attempts=last_error.attempts,
            timeout_seconds=last_error.timeout_seconds,
            transient=last_error.transient,
            last_status=last_error.last_status,
        ) from last_error
    raise last_error


def response_text(response: dict[str, object]) -> str:
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


def logged_response_message(message: dict[str, object]) -> dict[str, object]:
    logged = {k: v for k, v in message.items() if k in {"role", "content", "tool_calls"}}
    reasoning = message.get("reasoning_content")
    if isinstance(reasoning, str) and reasoning:
        logged["reasoning_content"] = reasoning[-DEFAULT_TOOL_RESULT_CHARS:]
        logged["provider_reasoning_chars"] = len(reasoning)
    return logged
