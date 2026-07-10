"""Request-shape tests for the outgoing chat-completions payload.

These assert what the harness actually puts on the wire, with a focus on the
opt-in ``DEFAULT_HARNESS_OMIT_MAX_TOKENS`` compatibility switch. Some strict
OpenAI-compatible providers (observed with Virtuals' ``openai-gpt-56-sol-pro``)
return a generic 400 whenever a request carries any token-limit field, so the
harness must be able to drop those fields entirely — generically, without
provider-name special casing — while leaving every other provider unchanged.

No network, no provider calls: ``_execute_chat_request`` is mocked and the
captured payload is inspected directly.
"""

from __future__ import annotations

import unittest
from unittest import mock

from harness import transport_request


def _capture_payload(**kwargs) -> dict[str, object]:
    captured: list[dict[str, object]] = []

    def fake_execute(base_url: str, payload: dict[str, object], *, stream: bool, api_key_override=None):
        captured.append(payload)
        return {"choices": [{"message": {"role": "assistant", "content": "ok"}}], "usage": {}}

    with mock.patch.object(transport_request, "_execute_chat_request", side_effect=fake_execute):
        transport_request.chat_completion(
            [{"role": "user", "content": "hi"}],
            base_url="http://provider.test/v1",
            **kwargs,
        )
    assert len(captured) == 1, captured
    return captured[0]


class DefaultRequestShapeTests(unittest.TestCase):
    def test_default_sends_max_tokens(self) -> None:
        with mock.patch.object(transport_request, "DEFAULT_OMIT_MAX_TOKENS", False):
            payload = _capture_payload(max_tokens=321)
        self.assertEqual(payload["max_tokens"], 321)
        self.assertEqual(payload["model"], transport_request.DEFAULT_MODEL)
        self.assertEqual(payload["temperature"], 0)

    def test_default_flag_is_off(self) -> None:
        # The compatibility switch must not change behaviour unless opted in.
        self.assertFalse(transport_request.DEFAULT_OMIT_MAX_TOKENS)


class OmitMaxTokensRequestShapeTests(unittest.TestCase):
    def test_omit_drops_max_tokens(self) -> None:
        with mock.patch.object(transport_request, "DEFAULT_OMIT_MAX_TOKENS", True):
            payload = _capture_payload(max_tokens=321)
        self.assertNotIn("max_tokens", payload)
        # The rest of the request is untouched.
        self.assertEqual(payload["temperature"], 0)
        self.assertIn("messages", payload)

    def test_omit_leaves_no_token_limit_key_in_payload(self) -> None:
        with mock.patch.object(transport_request, "DEFAULT_OMIT_MAX_TOKENS", True):
            payload = _capture_payload(max_tokens=64)
        for key in transport_request._TOKEN_LIMIT_PARAM_KEYS:
            self.assertNotIn(key, payload)

    def test_documented_strip_set_covers_the_known_offenders(self) -> None:
        self.assertEqual(
            set(transport_request._TOKEN_LIMIT_PARAM_KEYS),
            {"max_tokens", "max_completion_tokens", "reasoning_effort"},
        )

    def test_env_true_values_enable_omission(self) -> None:
        import importlib
        import os

        for raw in ("1", "true", "yes", "TRUE", "Yes"):
            with mock.patch.dict(os.environ, {"DEFAULT_HARNESS_OMIT_MAX_TOKENS": raw}):
                reloaded = importlib.reload(transport_request)
                try:
                    self.assertTrue(reloaded.DEFAULT_OMIT_MAX_TOKENS, raw)
                finally:
                    importlib.reload(transport_request)

    def test_env_default_and_false_values_keep_max_tokens(self) -> None:
        import importlib
        import os

        for raw in ("0", "false", "no", ""):
            with mock.patch.dict(os.environ, {"DEFAULT_HARNESS_OMIT_MAX_TOKENS": raw}):
                reloaded = importlib.reload(transport_request)
                try:
                    self.assertFalse(reloaded.DEFAULT_OMIT_MAX_TOKENS, raw)
                finally:
                    importlib.reload(transport_request)


if __name__ == "__main__":
    unittest.main()
