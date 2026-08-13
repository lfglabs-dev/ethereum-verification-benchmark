"""Generic opt-in OpenAI Responses API transport with task-local state."""
from __future__ import annotations

import json
import os
import socket
import time
import urllib.error
import urllib.request
import uuid
from dataclasses import dataclass
from typing import Any

from harness.identity import HARNESS_USER_AGENT
from harness.transport_backoff import is_transient_http_status, retry_delay_seconds
from harness.transport_errors import ChatCompletionError

DEFAULT_WIRE_API = os.environ.get("DEFAULT_HARNESS_WIRE_API", "chat_completions").strip().lower()
if DEFAULT_WIRE_API not in {"chat_completions", "responses"}:
    raise ValueError("DEFAULT_HARNESS_WIRE_API must be chat_completions or responses")


@dataclass
class ResponsesState:
    previous_response_id: str | None = None
    cursor: int = 0
    resets: int = 0
    last_reset_reason: str | None = None
    consumed_prefix: str | None = None
    requests: int = 0

    def reset(self, reason: str) -> None:
        self.previous_response_id = None
        self.cursor = 0
        self.consumed_prefix = None
        self.resets += 1
        self.last_reset_reason = reason

    def metadata(self) -> dict[str, Any]:
        return {"wire_api": "responses", "state_mode": "previous_response_id", "requests": self.requests, "last_response_id": self.previous_response_id, "state_resets": self.resets, "last_reset_reason": self.last_reset_reason}


def _fingerprint(messages: list[dict[str, Any]], end: int) -> str:
    return json.dumps(messages[:end], sort_keys=True, separators=(",", ":"), default=str)


def _flat_tools(tools: list[dict[str, Any]] | None) -> list[dict[str, Any]]:
    out = []
    for tool in tools or []:
        fn = tool.get("function") if isinstance(tool, dict) and tool.get("type") == "function" else None
        if not isinstance(fn, dict) or not isinstance(fn.get("name"), str):
            raise ValueError("malformed function tool")
        out.append({"type": "function", **fn})
    return out


def _inputs(messages: list[dict[str, Any]], state: ResponsesState) -> list[dict[str, Any]]:
    continuing = state.previous_response_id is not None
    if continuing and (len(messages) < state.cursor or state.consumed_prefix != _fingerprint(messages, state.cursor)):
        state.reset("transcript_replaced_or_compacted")
        continuing = False
    source = messages[state.cursor:] if continuing else messages
    out = []
    for message in source:
        role, content = message.get("role"), message.get("content")
        if continuing and role == "assistant":
            continue
        if role == "tool":
            call_id = message.get("tool_call_id")
            if not isinstance(call_id, str) or not 1 <= len(call_id) <= 64:
                raise ValueError("Responses requires matching 1-64 char call_id")
            out.append({"type": "function_call_output", "call_id": call_id, "output": content if isinstance(content, str) else str(content or "")})
        elif role in {"system", "developer", "user", "assistant"} and isinstance(content, str) and content:
            out.append({"role": "developer" if role == "system" else role, "content": [{"type": "input_text", "text": content}]})
    return out


def _decode_sse(response: Any) -> dict[str, Any]:
    terminal = None
    while True:
        raw = response.readline()
        if raw in {b"", ""}:
            break
        line = raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else str(raw)
        if not line.strip().startswith("data:"):
            continue
        data = line.strip()[5:].strip()
        if data == "[DONE]":
            break
        event = json.loads(data)
        if isinstance(event, dict) and event.get("type") in {"response.completed", "response.failed", "response.incomplete"} and isinstance(event.get("response"), dict):
            terminal = event["response"]
    if terminal is None:
        raise ChatCompletionError("Responses stream ended without terminal event", kind="invalid_response", attempts=1, timeout_seconds=0, transient=True)
    return terminal


def responses_completion(messages: list[dict[str, Any]], *, state: ResponsesState, model: str, tools: list[dict[str, Any]] | None = None, base_url: str | None = None, api_key: str | None = None) -> dict[str, Any]:
    key = api_key or os.environ.get("DEFAULT_HARNESS_RESPONSES_API_KEY") or os.environ.get("DEFAULT_HARNESS_API_KEY")
    if not key:
        raise ChatCompletionError("missing Responses API credential", kind="provider_setup_error", attempts=0, timeout_seconds=0, transient=False)
    base = base_url or os.environ.get("DEFAULT_HARNESS_RESPONSES_BASE_URL") or os.environ.get("DEFAULT_HARNESS_BASE_URL", "https://api.meta.ai/v1")
    inputs = _inputs(messages, state)
    payload: dict[str, Any] = {"model": model, "input": inputs, "tools": _flat_tools(tools), "tool_choice": "auto", "store": True}
    effort = os.environ.get("DEFAULT_HARNESS_REASONING_EFFORT", "").strip()
    if effort:
        payload["reasoning"] = {"effort": effort}
    if os.environ.get("DEFAULT_HARNESS_OMIT_MAX_TOKENS", "0").lower() not in {"1", "true", "yes"}:
        payload["max_output_tokens"] = max(16, int(os.environ.get("DEFAULT_HARNESS_MAX_RESPONSE_TOKENS", "8192")))
    if os.environ.get("DEFAULT_HARNESS_OMIT_SAMPLING", "0").lower() not in {"1", "true", "yes"}:
        temperature = float(os.environ.get("DEFAULT_HARNESS_TEMPERATURE", "0") or 0)
        payload["temperature"] = temperature
        if temperature == 0:
            payload["top_p"] = 1
    if state.previous_response_id:
        payload["previous_response_id"] = state.previous_response_id
    stream = os.environ.get("DEFAULT_HARNESS_STREAMING", "1").lower() not in {"0", "false", "no"}
    wire_payload = {**payload, **({"stream": True} if stream else {})}
    timeout = int(os.environ.get("DEFAULT_HARNESS_STREAM_IDLE_TIMEOUT_SECONDS" if stream else "DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS", "180"))
    retries = int(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRIES", "5"))
    idempotency_key = str(uuid.uuid4())
    decoded = None
    last_error = None
    for attempt in range(1, retries + 2):
        req = urllib.request.Request(base.rstrip("/") + "/responses", data=json.dumps(wire_payload).encode(), headers={"Authorization": "Bearer " + key, "Content-Type": "application/json", "User-Agent": HARNESS_USER_AGENT, "Idempotency-Key": idempotency_key}, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=timeout) as response:
                decoded = _decode_sse(response) if stream else json.load(response)
            break
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode(errors="replace")
            transient = is_transient_http_status(exc.code)
            last_error = ChatCompletionError(f"Responses HTTP {exc.code}: {detail[:1200]}", kind="http_transient" if transient else "http_error", attempts=attempt, timeout_seconds=timeout, transient=transient, last_status=exc.code)
        except (TimeoutError, socket.timeout, urllib.error.URLError, OSError) as exc:
            last_error = ChatCompletionError(f"Responses transport error: {exc}", kind="request_timeout" if isinstance(exc, (TimeoutError, socket.timeout)) else "transport_error", attempts=attempt, timeout_seconds=timeout, transient=True)
        if not last_error.transient or attempt > retries:
            raise last_error
        time.sleep(retry_delay_seconds(attempt=attempt, base_delay_seconds=float(os.environ.get("DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS", "2")), retry_after_seconds=None))
    if not isinstance(decoded, dict) or decoded.get("status", "completed") != "completed":
        raise ChatCompletionError("Responses did not complete", kind="response_failed", attempts=1, timeout_seconds=timeout, transient=False)
    response_id = decoded.get("id")
    if not isinstance(response_id, str) or not response_id:
        raise ChatCompletionError("Responses missing id", kind="protocol_error", attempts=1, timeout_seconds=timeout, transient=False)
    request_previous_id = payload.get("previous_response_id")
    text, calls = [], []
    for item in decoded.get("output") or []:
        if not isinstance(item, dict):
            continue
        if item.get("type") == "function_call":
            call_id = item.get("call_id")
            if not isinstance(call_id, str) or not 1 <= len(call_id) <= 64:
                raise ChatCompletionError("Responses invalid call_id", kind="protocol_error", attempts=1, timeout_seconds=timeout, transient=False)
            calls.append({"id": call_id, "type": "function", "function": {"name": item.get("name"), "arguments": item.get("arguments") or "{}"}})
        elif item.get("type") == "message":
            text.extend(part["text"] for part in item.get("content") or [] if isinstance(part, dict) and part.get("type") == "output_text" and isinstance(part.get("text"), str))
    state.previous_response_id = response_id
    state.cursor = len(messages)
    state.consumed_prefix = _fingerprint(messages, state.cursor)
    state.requests += 1
    usage = decoded.get("usage") or {}
    message: dict[str, Any] = {"role": "assistant", "content": "\n".join(text) or None}
    if calls:
        message["tool_calls"] = calls
    return {"id": response_id, "choices": [{"index": 0, "message": message, "finish_reason": "tool_calls" if calls else "stop"}], "usage": {"prompt_tokens": int(usage.get("input_tokens", 0) or 0), "completion_tokens": int(usage.get("output_tokens", 0) or 0), "total_tokens": int(usage.get("total_tokens", 0) or 0), **({"output_tokens_details": usage["output_tokens_details"]} if isinstance(usage.get("output_tokens_details"), dict) else {})}, "wire_api": "responses", "responses_state": {**state.metadata(), "previous_response_id": request_previous_id}}


def responses_preflight(model: str, *, base_url: str | None = None, api_key: str | None = None) -> dict[str, Any]:
    state = ResponsesState()
    tools = [{"type": "function", "function": {"name": "preflight_echo", "description": "Echo a value.", "parameters": {"type": "object", "properties": {"value": {"type": "string"}}, "required": ["value"], "additionalProperties": False}}}]
    messages = [{"role": "developer", "content": "You must call preflight_echo."}, {"role": "user", "content": "Call preflight_echo with value ok."}]
    first = responses_completion(messages, state=state, model=model, tools=tools, base_url=base_url, api_key=api_key)
    calls = first["choices"][0]["message"].get("tool_calls") or []
    if not calls:
        return {"status": "failed", "checks": {"responses": True, "tool_calls": False, "previous_response_id": False, "usage_accounting": bool(first.get("usage"))}}
    messages += [first["choices"][0]["message"], {"role": "tool", "tool_call_id": calls[0]["id"], "content": '{"value":"ok"}'}]
    second = responses_completion(messages, state=state, model=model, tools=tools, base_url=base_url, api_key=api_key)
    usage = {key: int(first["usage"].get(key, 0)) + int(second["usage"].get(key, 0)) for key in ("prompt_tokens", "completion_tokens", "total_tokens")}
    usage["requests"] = 2
    checks = {"responses": True, "tool_calls": True, "previous_response_id": second["responses_state"]["previous_response_id"] == first["id"], "usage_accounting": usage["total_tokens"] > 0}
    return {"status": "passed" if all(checks.values()) else "failed", "model": model, "wire_api": "responses", "checks": checks, "usage": usage, "responses_state": state.metadata()}
