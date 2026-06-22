"""Provider preflight checks for OpenAI-compatible chat endpoints."""

from __future__ import annotations

import json
import urllib.request
from urllib.parse import urlparse

from harness.transport_request import DEFAULT_BASE_URL, DEFAULT_MODEL, build_chat_request, chat_completion


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


def generic_preflight(base_url: str = DEFAULT_BASE_URL, model: str = DEFAULT_MODEL) -> dict[str, object]:
    result: dict[str, object] = {
        "status": "passed",
        "base_url": base_url,
        "model": model,
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
    )
    record_usage(text_response)
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
    try:
        tool_response = chat_completion(
            [{"role": "user", "content": "Call preflight_echo with value ok."}],
            base_url=base_url,
            model=model,
            max_tokens=64,
            tools=probe_tools,
            tool_choice="auto",
        )
        record_usage(tool_response)
        message = ((tool_response.get("choices") or [{}])[0] or {}).get("message", {})
        result["checks"]["tool_calls"] = bool(isinstance(message, dict) and message.get("tool_calls"))
        result["checks"]["json_text_fallback"] = True
    except Exception as exc:  # noqa: BLE001 - fallback is an accepted protocol mode
        result["checks"]["tool_calls"] = False
        result["checks"]["json_text_fallback"] = True
        result["tool_call_probe_error"] = str(exc)
    usage = result.get("usage")
    result["checks"]["usage_accounting"] = bool(isinstance(usage, dict) and usage.get("requests"))
    if not result["checks"]["usage_accounting"]:
        result["status"] = "failed"
        result["error"] = "preflight did not observe request accounting"
    return result
