from __future__ import annotations

import json
import unittest
import urllib.error
from unittest import mock

from harness import transport_request
from harness.transport_errors import ChatCompletionError


# Exact 400 body returned by the official Mistral API for the ordering bug,
# captured from results/runs/*-alchemix__earmark_conservation (request_index 5).
MISTRAL_ORDER_400_BODY = json.dumps(
    {
        "object": "error",
        "message": "Unexpected role 'tool' after role 'user'",
        "type": "invalid_request_message_order",
        "param": None,
        "code": "3230",
        "raw_status_code": 400,
    }
)


def _tool_after_user(messages: list[dict[str, object]]) -> bool:
    for prev, cur in zip(messages, messages[1:]):
        if prev.get("role") == "user" and cur.get("role") == "tool":
            return True
    return False


def _missing_tool_replies(messages: list[dict[str, object]]) -> bool:
    for idx, message in enumerate(messages):
        if message.get("role") != "assistant":
            continue
        calls = message.get("tool_calls") or []
        for offset, _call in enumerate(calls, start=1):
            follower = messages[idx + offset] if idx + offset < len(messages) else None
            if not follower or follower.get("role") != "tool":
                return True
    return False


# Reproduces the transcript the fair tool loop produced: an assistant tool_calls
# turn, a corrective ``user`` warning injected by repetition_failure, and then
# the tool result that was still appended afterwards.
BAD_TRANSCRIPT = [
    {"role": "system", "content": "sys"},
    {"role": "user", "content": "task"},
    {
        "role": "assistant",
        "content": None,
        "tool_calls": [
            {"id": "call-1", "type": "function", "function": {"name": "read_file", "arguments": "{\"path\": \"Specs.lean\"}"}}
        ],
    },
    {"role": "tool", "tool_call_id": "call-1", "name": "read_file", "content": "spec body"},
    {
        "role": "assistant",
        "content": None,
        "tool_calls": [
            {"id": "call-2", "type": "function", "function": {"name": "read_file", "arguments": "{\"path\": \"Specs.lean\"}"}}
        ],
    },
    {"role": "user", "content": "You repeated the same unproductive action. Change strategy."},
    {"role": "tool", "tool_call_id": "call-2", "name": "read_file", "content": "spec body"},
]


class SanitizeMessageOrderTests(unittest.TestCase):
    def test_moves_interleaved_user_after_tool_reply(self) -> None:
        sanitized = transport_request._sanitize_tool_message_order(BAD_TRANSCRIPT)
        self.assertFalse(_tool_after_user(sanitized), sanitized)
        self.assertFalse(_missing_tool_replies(sanitized), sanitized)
        roles = [m["role"] for m in sanitized]
        self.assertEqual(
            roles,
            ["system", "user", "assistant", "tool", "assistant", "tool", "user"],
        )
        # The corrective warning is preserved, just relocated after the reply.
        self.assertEqual(sanitized[-1]["role"], "user")
        self.assertIn("repeated", sanitized[-1]["content"])

    def test_synthesizes_stub_reply_for_unanswered_tool_call(self) -> None:
        messages = [
            {"role": "user", "content": "task"},
            {
                "role": "assistant",
                "content": None,
                "tool_calls": [
                    {"id": "call-x", "type": "function", "function": {"name": "check_proof", "arguments": "{}"}}
                ],
            },
            {"role": "user", "content": "malformed correction"},
        ]
        sanitized = transport_request._sanitize_tool_message_order(messages)
        self.assertFalse(_missing_tool_replies(sanitized), sanitized)
        stub = sanitized[2]
        self.assertEqual(stub["role"], "tool")
        self.assertEqual(stub["tool_call_id"], "call-x")

    def test_valid_transcript_is_unchanged(self) -> None:
        good = [
            {"role": "system", "content": "sys"},
            {"role": "user", "content": "task"},
            {
                "role": "assistant",
                "content": None,
                "tool_calls": [
                    {"id": "call-1", "type": "function", "function": {"name": "show_task", "arguments": "{}"}}
                ],
            },
            {"role": "tool", "tool_call_id": "call-1", "name": "show_task", "content": "ok"},
        ]
        self.assertEqual(transport_request._sanitize_tool_message_order(good), good)


class ChatCompletionMistralReplayTests(unittest.TestCase):
    def setUp(self) -> None:
        transport_request.reset_transport_fallback()

    def tearDown(self) -> None:
        transport_request.reset_transport_fallback()

    def test_sanitized_payload_never_sends_tool_after_user(self) -> None:
        captured: list[dict[str, object]] = []

        def fake_execute(base_url: str, payload: dict[str, object], *, stream: bool, api_key_override=None):
            captured.append(payload)
            return {"choices": [{"message": {"role": "assistant", "content": "ok"}}], "usage": {}}

        with mock.patch.object(transport_request, "_execute_chat_request", side_effect=fake_execute):
            transport_request.chat_completion(BAD_TRANSCRIPT, base_url="http://provider.test/v1")

        self.assertEqual(len(captured), 1)
        sent = captured[0]["messages"]
        self.assertFalse(_tool_after_user(sent), sent)
        self.assertFalse(_missing_tool_replies(sent), sent)

    def test_replayed_mistral_400_is_avoided_after_sanitization(self) -> None:
        # A strict endpoint that rejects any tool-after-user ordering with the
        # real Mistral 400 body, mirroring the official API's behaviour.
        def strict_execute(base_url: str, payload: dict[str, object], *, stream: bool, api_key_override=None):
            if _tool_after_user(payload["messages"]):
                raise urllib.error.HTTPError(
                    base_url, 400, "Bad Request", {}, _FakeBody(MISTRAL_ORDER_400_BODY)
                )
            return {"choices": [{"message": {"role": "assistant", "content": "ok"}}], "usage": {}}

        with mock.patch.object(transport_request, "_execute_chat_request", side_effect=strict_execute):
            result = transport_request.chat_completion(BAD_TRANSCRIPT, base_url="http://provider.test/v1")
        self.assertEqual(result["choices"][0]["message"]["content"], "ok")

    def test_unsanitized_transcript_would_have_triggered_the_400(self) -> None:
        # Guards the regression: the raw transcript is genuinely rejected by a
        # Mistral-strict endpoint, so the sanitizer is what saves the request.
        self.assertTrue(_tool_after_user(BAD_TRANSCRIPT))

        def strict_execute(base_url: str, payload: dict[str, object], *, stream: bool, api_key_override=None):
            raise urllib.error.HTTPError(
                base_url, 400, "Bad Request", {}, _FakeBody(MISTRAL_ORDER_400_BODY)
            )

        with mock.patch.object(transport_request, "_sanitize_tool_message_order", side_effect=lambda m: m):
            with mock.patch.object(transport_request, "_execute_chat_request", side_effect=strict_execute):
                with self.assertRaises(ChatCompletionError) as ctx:
                    transport_request.chat_completion(BAD_TRANSCRIPT, base_url="http://provider.test/v1")
        self.assertEqual(ctx.exception.last_status, 400)
        self.assertIn("invalid_request_message_order", str(ctx.exception))


class _FakeBody:
    def __init__(self, body: str) -> None:
        self._body = body.encode("utf-8")

    def read(self) -> bytes:
        return self._body

    def close(self) -> None:
        return None


if __name__ == "__main__":
    unittest.main()
