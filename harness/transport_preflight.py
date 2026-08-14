"""Provider preflight checks for OpenAI-compatible chat endpoints."""

from __future__ import annotations

import json
import os
import urllib.request
from urllib.parse import urlparse

from harness.transport_request import (
    DEFAULT_BASE_URL,
    DEFAULT_MODEL,
    DEFAULT_STREAMING_ENABLED,
    build_chat_request,
    chat_completion,
    reset_transport_fallback,
    streaming_fallback_reason,
    transport_mode,
)


PROTOCOL_PROBE_ATTEMPTS = max(
    1, int(os.environ.get("DEFAULT_HARNESS_PROTOCOL_PROBE_ATTEMPTS", "3"))
)
# Reasoning tokens count against the same output limit as visible text and tool
# arguments. A 64-token probe can therefore truncate a valid reasoning model
# before its first tool call and misclassify it as protocol-incompatible.
PROTOCOL_PROBE_MAX_TOKENS = max(
    256, int(os.environ.get("DEFAULT_HARNESS_PROTOCOL_PROBE_MAX_TOKENS", "256"))
)


def endpoint_smoke(base_url: str = DEFAULT_BASE_URL, model: str = DEFAULT_MODEL) -> dict[str, object]:
    body = json.dumps(
        {
            "model": model,
            "messages": [{"role": "user", "content": "Dis moi tres brievement qui est Vasco de Gama (2 phrases)"}],
            "max_tokens": 500,
            "temperature": 0,
        }
    ).encode("utf-8")
    request = build_chat_request(base_url, body)
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read().decode("utf-8"))


def local_no_auth_endpoint(base_url: str) -> bool:
    host = urlparse(base_url).hostname
    return host in {"127.0.0.1", "localhost", "::1"}


def _valid_json_text_echo(response: dict[str, object]) -> bool:
    """Return whether a no-native-tools probe produced the requested JSON call.

    Some OpenAI-compatible models, notably Leanstral 1.5, do not emit native
    ``tool_calls`` but can drive the harness through JSON text.  Validate that
    protocol from the actual response instead of merely assuming it exists.
    ``raw_decode`` intentionally accepts a valid first JSON value followed by a
    leaked chat-template sentinel, matching the runtime parser's tolerance.
    """
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices or not isinstance(choices[0], dict):
        return False
    message = choices[0].get("message")
    if not isinstance(message, dict):
        return False
    content = message.get("content")
    if not isinstance(content, str):
        return False
    start = content.find("{")
    if start < 0:
        return False
    try:
        payload, _ = json.JSONDecoder().raw_decode(content[start:])
    except json.JSONDecodeError:
        return False
    return bool(
        isinstance(payload, dict)
        and payload.get("tool") == "preflight_echo"
        and isinstance(payload.get("arguments"), dict)
        and payload["arguments"].get("value") == "ok"
    )


def generic_preflight(
    base_url: str = DEFAULT_BASE_URL,
    model: str = DEFAULT_MODEL,
    *,
    api_key_override: str | None = None,
) -> dict[str, object]:
    if DEFAULT_STREAMING_ENABLED:
        reset_transport_fallback()
    result: dict[str, object] = {
        "status": "passed",
        "base_url": base_url,
        "model": model,
        "transport_mode": transport_mode(),
        "checks": {},
        "usage": {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0},
    }

    def record_usage(response: dict[str, object]) -> None:
        usage = response.get("usage")
        if isinstance(usage, dict):
            result_usage = result["usage"]
            assert isinstance(result_usage, dict)
            result_usage["requests"] = int(result_usage.get("requests", 0)) + 1
            for key in ("prompt_tokens", "completion_tokens", "total_tokens"):
                value = usage.get(key)
                if isinstance(value, (int, float)):
                    result_usage[key] = int(result_usage.get(key, 0)) + int(value)

    text_response = chat_completion(
        [{"role": "user", "content": "Reply with exactly: ok"}],
        base_url=base_url,
        model=model,
        max_tokens=16,
        api_key_override=api_key_override,
    )
    record_usage(text_response)
    result["transport_mode"] = transport_mode()
    fallback_reason = streaming_fallback_reason()
    if fallback_reason:
        result["streaming_fallback_reason"] = fallback_reason
    result["checks"]["chat_completions"] = True
    result["checks"]["model_selection"] = True

    probe_tools = [
        {
            "type": "function",
            "function": {
                "name": "preflight_echo",
                "description": "Echo a short string.",
                "parameters": {
                    "type": "object",
                    "properties": {"value": {"type": "string"}},
                    "required": ["value"],
                    "additionalProperties": False,
                },
            },
        }
    ]
    native_tool_calls = False
    try:
        tool_response = chat_completion(
            [{"role": "user", "content": "Call preflight_echo with value ok."}],
            base_url=base_url,
            model=model,
            max_tokens=PROTOCOL_PROBE_MAX_TOKENS,
            tools=probe_tools,
            tool_choice="auto",
            api_key_override=api_key_override,
        )
        record_usage(tool_response)
        result["transport_mode"] = transport_mode()
        message = ((tool_response.get("choices") or [{}])[0] or {}).get("message", {})
        native_tool_calls = bool(isinstance(message, dict) and message.get("tool_calls"))
        result["checks"]["tool_calls"] = native_tool_calls
    except Exception as exc:  # noqa: BLE001 - fallback is an accepted protocol mode
        result["checks"]["tool_calls"] = False
        result["tool_call_probe_error"] = str(exc)

    if native_tool_calls:
        result["checks"]["json_text_fallback"] = None
        result["checks"]["json_text_fallback_probed"] = False
    else:
        fallback_valid = False
        fallback_errors: list[str] = []
        fallback_attempts = 0
        for fallback_attempts in range(1, PROTOCOL_PROBE_ATTEMPTS + 1):
            try:
                fallback_response = chat_completion(
                    [
                        {
                            "role": "system",
                            "content": (
                                "Reply only with one JSON tool call. The exact required shape is "
                                '{"tool":"preflight_echo","arguments":{"value":"ok"}}. '
                                "Do not emit prose, booleans, XML, sentinel tokens, or markdown."
                            ),
                        },
                        {"role": "user", "content": "Call preflight_echo now with value ok."},
                    ],
                    base_url=base_url,
                    model=model,
                    max_tokens=PROTOCOL_PROBE_MAX_TOKENS,
                    api_key_override=api_key_override,
                )
                record_usage(fallback_response)
                fallback_valid = _valid_json_text_echo(fallback_response)
                if fallback_valid:
                    break
            except Exception as exc:  # noqa: BLE001 - normalized into preflight evidence
                fallback_errors.append(str(exc))
        result["checks"]["json_text_fallback"] = fallback_valid
        result["checks"]["json_text_fallback_probed"] = True
        result["checks"]["json_text_fallback_attempts"] = fallback_attempts
        if fallback_errors:
            result["json_text_fallback_probe_errors"] = fallback_errors

    if not result["checks"]["tool_calls"] and not result["checks"]["json_text_fallback"]:
        result["status"] = "failed"
        result["error"] = "provider supports neither native tool calls nor validated JSON-text fallback"
    result["transport_mode"] = transport_mode()
    fallback_reason = streaming_fallback_reason()
    if fallback_reason:
        result["streaming_fallback_reason"] = fallback_reason
    usage = result.get("usage")
    result["checks"]["usage_accounting"] = bool(isinstance(usage, dict) and usage.get("requests"))
    if not result["checks"]["usage_accounting"]:
        result["status"] = "failed"
        result["error"] = "preflight did not observe request accounting"
    return result
