from unittest import mock

from harness import transport_preflight


def _text_response():
    return {
        "choices": [{"message": {"content": "ok"}}],
        "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
    }


def _tool_response():
    return {
        "choices": [
            {
                "message": {
                    "content": None,
                    "tool_calls": [
                        {
                            "id": "call_1",
                            "type": "function",
                            "function": {"name": "preflight_echo", "arguments": '{"value":"ok"}'},
                        }
                    ],
                }
            }
        ],
        "usage": {"prompt_tokens": 1, "completion_tokens": 85, "total_tokens": 86},
    }


def test_reasoning_model_protocol_probe_has_room_for_tool_call():
    observed = []

    def fake_chat_completion(*args, **kwargs):
        observed.append(kwargs["max_tokens"])
        return _text_response() if len(observed) == 1 else _tool_response()

    with mock.patch.object(transport_preflight, "chat_completion", side_effect=fake_chat_completion):
        result = transport_preflight.generic_preflight(
            base_url="https://provider.example/v1", model="reasoning-model"
        )

    checks = result["checks"]
    assert isinstance(checks, dict)
    assert result["status"] == "passed"
    assert checks["tool_calls"] is True
    assert observed == [16, transport_preflight.PROTOCOL_PROBE_MAX_TOKENS]
    assert transport_preflight.PROTOCOL_PROBE_MAX_TOKENS >= 256
