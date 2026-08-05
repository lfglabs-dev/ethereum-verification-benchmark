"""Regression tests for transport-layer metadata persistence.

The harness must capture http_status and the upstream ``model`` field (so we
can tell when a router returned a different model than requested) and surface
them inside the persisted response so a non-passing result can be reclassified
as a transport-level truncation rather than a genuine model failure.

No network, no provider calls: ``urllib.request.urlopen`` is mocked.
"""

from __future__ import annotations

import json
import unittest
from unittest import mock

import harness.transport_request as transport_request_module
from harness import transport_request


def _fake_urlopen(status: int, body: dict):
    """Build a context manager whose .read() returns ``body`` JSON and
    whose .status/.getcode() return ``status``. Streaming clients also
    call readline(); we provide one that returns ``""`` so the SSE
    decoder exits cleanly."""

    class _Resp:
        def __init__(self) -> None:
            self.status = status

        def getcode(self) -> int:
            return status

        def read(self) -> bytes:
            return json.dumps({"model": "MiniMax-M3", **body}).encode()

        def readline(self) -> bytes:
            return b""

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc, tb):
            return False

    return _Resp()


class TransportResponseMetaTests(unittest.TestCase):
    def test_execute_injects_http_status_and_returned_model(self) -> None:
        resp = _fake_urlopen(
            200,
            {
                "choices": [
                    {"message": {"role": "assistant", "content": "hi"}, "finish_reason": "stop"}
                ],
                "usage": {"prompt_tokens": 5, "completion_tokens": 2, "total_tokens": 7},
            },
        )
        with mock.patch.object(transport_request_module.urllib.request, "urlopen", return_value=resp):
            decoded = transport_request._execute_chat_request(
                "http://provider.test/v1",
                {"model": "minimax/MiniMax-M3", "messages": []},
                stream=False,
            )
        self.assertEqual(decoded["_transport_http_status"], 200)
        self.assertEqual(decoded["_returned_model"], "MiniMax-M3")
        self.assertEqual(decoded["choices"][0]["finish_reason"], "stop")

    def test_execute_returns_status_when_present(self) -> None:
        resp = _fake_urlopen(
            524,
            {"error": {"message": "origin timeout"}, "choices": []},
        )
        with mock.patch.object(transport_request_module.urllib.request, "urlopen", return_value=resp):
            decoded = transport_request._execute_chat_request(
                "http://provider.test/v1",
                {"model": "minimax/MiniMax-M3", "messages": []},
                stream=False,
            )
        self.assertEqual(decoded["_transport_http_status"], 524)

    def test_chat_completion_propagates_truncation_marker(self) -> None:
        resp = _fake_urlopen(
            200,
            {
                "choices": [
                    {"message": {"role": "assistant", "content": "..."}, "finish_reason": "length"}
                ],
                "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
            },
        )
        with mock.patch.object(transport_request_module.urllib.request, "urlopen", return_value=resp), mock.patch.object(
            transport_request, "DEFAULT_OMIT_MAX_TOKENS", False
        ), mock.patch.object(transport_request, "DEFAULT_STREAMING_ENABLED", False):
            decoded = transport_request.chat_completion(
                [{"role": "user", "content": "hi"}],
                base_url="http://provider.test/v1",
                max_tokens=1,
            )
        self.assertEqual(decoded["choices"][0]["finish_reason"], "length")
        self.assertEqual(decoded["_transport_http_status"], 200)
        self.assertEqual(decoded["_returned_model"], "MiniMax-M3")


if __name__ == "__main__":
    unittest.main()