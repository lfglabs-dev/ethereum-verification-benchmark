from __future__ import annotations

import io
import json
import socket
import tempfile
import unittest
import urllib.error
from pathlib import Path
from unittest import mock

from harness import transport_preflight
from harness.transport_errors import ChatCompletionError
from harness import transport_request


class FakeResponse:
    def __init__(self, *, lines: list[bytes] | None = None, body: dict[str, object] | None = None, fail_at: int | None = None):
        self.lines = lines or []
        self.body = body or {}
        self.fail_at = fail_at
        self.index = 0

    def __enter__(self) -> FakeResponse:
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        return None

    def readline(self) -> bytes:
        if self.fail_at is not None and self.index == self.fail_at:
            raise socket.timeout("idle between chunks")
        if self.index >= len(self.lines):
            return b""
        line = self.lines[self.index]
        self.index += 1
        return line

    def read(self) -> bytes:
        return json.dumps(self.body).encode("utf-8")


def sse(payload: dict[str, object]) -> bytes:
    return f"data: {json.dumps(payload)}\n\n".encode("utf-8")


def non_streaming_response(content: str = "ok") -> dict[str, object]:
    return {
        "choices": [{"index": 0, "message": {"role": "assistant", "content": content}, "finish_reason": "stop"}],
        "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
    }


class TransportStreamingTests(unittest.TestCase):
    def setUp(self) -> None:
        transport_request.reset_transport_fallback()

    def tearDown(self) -> None:
        transport_request.reset_transport_fallback()

    def test_streaming_happy_path_accumulates_content_tool_calls_and_usage(self) -> None:
        lines = [
            sse({"id": "chatcmpl-1", "choices": [{"index": 0, "delta": {"role": "assistant", "content": "hel"}}]}),
            sse(
                {
                    "choices": [
                        {
                            "index": 0,
                            "delta": {
                                "content": "lo",
                                "tool_calls": [
                                    {
                                        "index": 0,
                                        "id": "call_1",
                                        "type": "function",
                                        "function": {"name": "preflight_", "arguments": "{\"value\""},
                                    }
                                ],
                            },
                        }
                    ]
                }
            ),
            sse({"choices": [{"index": 0, "delta": {"tool_calls": [{"index": 0, "function": {"name": "echo", "arguments": ":\"ok\"}"}}]}}]}),
            sse({"choices": [{"index": 0, "delta": {}, "finish_reason": "tool_calls"}]}),
            sse({"choices": [], "usage": {"prompt_tokens": 3, "completion_tokens": 5, "total_tokens": 8}}),
            b"data: [DONE]\n\n",
        ]
        seen: dict[str, object] = {}

        def fake_urlopen(request: object, timeout: int) -> FakeResponse:
            seen["timeout"] = timeout
            body = json.loads(request.data.decode("utf-8"))  # type: ignore[attr-defined]
            seen["payload"] = body
            return FakeResponse(lines=lines)

        with mock.patch.object(transport_request.urllib.request, "urlopen", side_effect=fake_urlopen):
            response = transport_request.chat_completion([{"role": "user", "content": "hi"}], base_url="http://provider.test/v1")

        self.assertEqual(seen["timeout"], transport_request.STREAM_IDLE_TIMEOUT_SECONDS)
        self.assertEqual(seen["payload"]["stream"], True)  # type: ignore[index]
        self.assertEqual(seen["payload"]["stream_options"], {"include_usage": True})  # type: ignore[index]
        message = response["choices"][0]["message"]  # type: ignore[index]
        self.assertEqual(message["content"], "hello")
        self.assertEqual(message["tool_calls"][0]["function"]["name"], "preflight_echo")
        self.assertEqual(message["tool_calls"][0]["function"]["arguments"], "{\"value\":\"ok\"}")
        self.assertEqual(response["usage"]["total_tokens"], 8)  # type: ignore[index]

    def test_streaming_chunks_under_idle_timeout_succeed(self) -> None:
        lines = [
            sse({"choices": [{"index": 0, "delta": {"role": "assistant"}}]}),
            sse({"choices": [{"index": 0, "delta": {"content": "slow "}}]}),
            sse({"choices": [{"index": 0, "delta": {"content": "ok"}, "finish_reason": "stop"}]}),
            b"data: [DONE]\n\n",
        ]
        timeouts: list[int] = []

        def fake_urlopen(request: object, timeout: int) -> FakeResponse:
            timeouts.append(timeout)
            return FakeResponse(lines=lines)

        with mock.patch.object(transport_request.urllib.request, "urlopen", side_effect=fake_urlopen):
            response = transport_request.chat_completion([{"role": "user", "content": "hi"}], base_url="http://provider.test/v1")

        self.assertEqual(timeouts, [transport_request.STREAM_IDLE_TIMEOUT_SECONDS])
        self.assertEqual(response["choices"][0]["message"]["content"], "slow ok")  # type: ignore[index]

    def test_mid_stream_idle_timeout_is_transient_and_retried(self) -> None:
        first = FakeResponse(
            lines=[
                sse({"choices": [{"index": 0, "delta": {"role": "assistant", "content": "partial"}}]}),
            ],
            fail_at=1,
        )
        second = FakeResponse(
            lines=[
                sse({"choices": [{"index": 0, "delta": {"role": "assistant", "content": "recovered"}, "finish_reason": "stop"}]}),
                b"data: [DONE]\n\n",
            ]
        )
        calls = [first, second]

        def fake_urlopen(request: object, timeout: int) -> FakeResponse:
            return calls.pop(0)

        with tempfile.TemporaryDirectory() as tmp:
            log_path = Path(tmp) / "requests.jsonl"
            with (
                mock.patch.object(transport_request, "REQUEST_RETRIES", 1),
                mock.patch.object(transport_request.time, "sleep", return_value=None),
                mock.patch.object(transport_request.urllib.request, "urlopen", side_effect=fake_urlopen),
            ):
                response = transport_request.chat_completion(
                    [{"role": "user", "content": "hi"}],
                    base_url="http://provider.test/v1",
                    request_log_path=log_path,
                    request_index=7,
                )
            log_entries = [json.loads(line) for line in log_path.read_text(encoding="utf-8").splitlines()]

        self.assertEqual(response["choices"][0]["message"]["content"], "recovered")  # type: ignore[index]
        self.assertEqual(log_entries[0]["status"], "request_retry")
        self.assertEqual(log_entries[0]["error"]["kind"], "request_timeout")
        self.assertTrue(log_entries[0]["error"]["transient"])
        self.assertEqual(log_entries[0]["error"]["timeout_seconds"], transport_request.STREAM_IDLE_TIMEOUT_SECONDS)
        self.assertEqual(log_entries[1]["status"], "request_retry_succeeded")

    def test_streaming_idle_timeout_exhaustion_raises_request_timeout(self) -> None:
        def fake_urlopen(request: object, timeout: int) -> FakeResponse:
            return FakeResponse(
                lines=[sse({"choices": [{"index": 0, "delta": {"role": "assistant"}}]})],
                fail_at=1,
            )

        with (
            mock.patch.object(transport_request, "REQUEST_RETRIES", 0),
            mock.patch.object(transport_request.urllib.request, "urlopen", side_effect=fake_urlopen),
        ):
            with self.assertRaises(ChatCompletionError) as raised:
                transport_request.chat_completion([{"role": "user", "content": "hi"}], base_url="http://provider.test/v1")

        self.assertEqual(raised.exception.kind, "request_timeout")
        self.assertTrue(raised.exception.transient)
        self.assertEqual(raised.exception.timeout_seconds, transport_request.STREAM_IDLE_TIMEOUT_SECONDS)

    def test_preflight_falls_back_when_provider_rejects_streaming(self) -> None:
        payloads: list[dict[str, object]] = []

        def fake_urlopen(request: object, timeout: int) -> FakeResponse:
            payload = json.loads(request.data.decode("utf-8"))  # type: ignore[attr-defined]
            payloads.append(payload)
            if payload.get("stream"):
                raise urllib.error.HTTPError(
                    request.full_url,  # type: ignore[attr-defined]
                    400,
                    "bad request",
                    {},
                    io.BytesIO(b"stream is not supported"),
                )
            if payload.get("tools"):
                return FakeResponse(body=non_streaming_response())
            messages = payload.get("messages")
            if isinstance(messages, list) and messages and "preflight_echo now" in str(messages[-1].get("content")):
                return FakeResponse(
                    body=non_streaming_response(
                        '{"tool":"preflight_echo","arguments":{"value":"ok"}}'
                    )
                )
            return FakeResponse(body=non_streaming_response())

        with mock.patch.object(transport_request.urllib.request, "urlopen", side_effect=fake_urlopen):
            result = transport_preflight.generic_preflight(base_url="http://provider.test/v1", model="mock-model")

        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["transport_mode"], "fallback_non_streaming")
        self.assertIn("streaming_fallback_reason", result)
        self.assertFalse(result["checks"]["tool_calls"])
        self.assertTrue(result["checks"]["json_text_fallback"])
        self.assertTrue(result["checks"]["json_text_fallback_probed"])
        self.assertTrue(payloads[0].get("stream"))
        self.assertTrue(all(not payload.get("stream") for payload in payloads[1:]))


class BuildChatRequestAuthTests(unittest.TestCase):
    def test_uses_module_api_key_when_no_override(self) -> None:
        with mock.patch.object(transport_request, "api_key", lambda: "driver-key"):
            request = transport_request.build_chat_request("http://provider.test/v1", b"{}")
        self.assertEqual(request.get_header("Authorization"), "Bearer driver-key")

    def test_override_takes_precedence_over_module_api_key(self) -> None:
        with mock.patch.object(transport_request, "api_key", lambda: "driver-key"):
            request = transport_request.build_chat_request(
                "http://prover.test/v1", b"{}", api_key_override="prover-key"
            )
        self.assertEqual(request.get_header("Authorization"), "Bearer prover-key")

    def test_none_override_falls_back_to_module_api_key(self) -> None:
        # Callers pass None (not "") to request driver-key fallback, so an
        # explicit None must resolve the driver key rather than dropping auth.
        with mock.patch.object(transport_request, "api_key", lambda: "driver-key"):
            request = transport_request.build_chat_request(
                "http://provider.test/v1", b"{}", api_key_override=None
            )
        self.assertEqual(request.get_header("Authorization"), "Bearer driver-key")


if __name__ == "__main__":
    unittest.main()
