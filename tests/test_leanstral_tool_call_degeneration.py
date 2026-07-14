"""Guards against the Leanstral 1.5 tool-call degeneration bug.

Leanstral 1.5 is a ChatML fine-tune served through llama.cpp. When the server
does not stop on `<|im_end|>`, the sentinel leaks into the OpenAI `content`
stream and the model runs past its turn boundary, regenerating the whole fake
conversation. Two harness defects turned that into scored model failures:

1. `chat_completion` never sent `stop` sequences, so nothing halted the leak.
2. `_json_payload_from_text` demanded the entire content be valid JSON, so a
   perfectly good `{"tool":...}<|im_end|>` was discarded and counted as a
   no-tool response, eventually terminating as `failed_no_tool_calls` and being
   misclassified as GENUINE_FAIL instead of a provider/tool-protocol breakdown.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness import transport_request
from harness import transport_preflight
from harness.classification import classify_run, classify_target
from harness.runners import lean_tools

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "leanstral_tool_call_degeneration.jsonl"


def non_streaming_response(content: str) -> dict[str, object]:
    return {
        "choices": [{"index": 0, "message": {"role": "assistant", "content": content}, "finish_reason": "stop"}],
        "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
    }


class StopSequenceTests(unittest.TestCase):
    def setUp(self) -> None:
        transport_request.reset_transport_fallback()

    def tearDown(self) -> None:
        transport_request.reset_transport_fallback()

    def test_default_stop_sequences_cover_chatml_and_tool_sentinels(self) -> None:
        for sentinel in (
            "<|im_end|>",
            "</|im_end|>",
            "<|im_start|>",
            "</|im_start|>",
            "<|tool_call_begin|>",
            "<|tool_call_end|>",
        ):
            self.assertIn(sentinel, transport_request.DEFAULT_STOP_SEQUENCES)

    def test_chat_completion_sends_stop_sequences(self) -> None:
        seen: dict[str, object] = {}

        def fake_urlopen(request: object, timeout: int):
            body = json.loads(request.data.decode("utf-8"))  # type: ignore[attr-defined]
            seen["payload"] = body

            class _Resp:
                def __enter__(self_inner):
                    return self_inner

                def __exit__(self_inner, *a):
                    return None

                def read(self_inner):
                    return json.dumps(non_streaming_response("ok")).encode("utf-8")

                def readline(self_inner):
                    return b""

            return _Resp()

        with (
            mock.patch.object(transport_request, "DEFAULT_STREAMING_ENABLED", False),
            mock.patch.object(transport_request.urllib.request, "urlopen", side_effect=fake_urlopen),
        ):
            transport_request.chat_completion([{"role": "user", "content": "hi"}], base_url="http://provider.test/v1")

        payload = seen["payload"]
        self.assertIn("stop", payload)  # type: ignore[operator]
        self.assertIn("<|im_end|>", payload["stop"])  # type: ignore[index]

    def test_stop_sequences_env_override(self) -> None:
        with mock.patch.dict("os.environ", {"DEFAULT_HARNESS_STOP_SEQUENCES": "FOO\nBAR"}):
            self.assertEqual(transport_request._configured_stop_sequences(), ["FOO", "BAR"])
        with mock.patch.dict("os.environ", {"DEFAULT_HARNESS_STOP_SEQUENCES": ""}):
            self.assertEqual(transport_request._configured_stop_sequences(), [])


class SentinelParsingTests(unittest.TestCase):
    def test_clean_json_tool_call(self) -> None:
        calls = lean_tools._tool_calls_from_text('{"tool":"show_task","arguments":{}}')
        self.assertEqual([c["function"]["name"] for c in calls], ["show_task"])

    def test_trailing_sentinel_is_salvaged(self) -> None:
        calls = lean_tools._tool_calls_from_text('{"tool":"show_task","arguments":{}}<|im_end|>')
        self.assertEqual([c["function"]["name"] for c in calls], ["show_task"])

    def test_literal_newlines_in_proof_argument_are_salvaged(self) -> None:
        text = '''{"tool":"check_proof","arguments":{"proof":"
theorem sample : True := by
  exact True.intro"}}'''
        calls = lean_tools._tool_calls_from_text(text)

        self.assertEqual([call["function"]["name"] for call in calls], ["check_proof"])
        self.assertIn("exact True.intro", calls[0]["function"]["arguments"]["proof"])

    def test_degeneration_recovers_first_valid_call(self) -> None:
        for record in self._fixture_records():
            with self.subTest(request_index=record.get("request_index")):
                calls = lean_tools._tool_calls_from_text(record["content"])
                self.assertTrue(calls, f"expected a recovered call for: {record['content'][:60]!r}")
                self.assertEqual(calls[0]["function"]["name"], record["expected_tool"])

    def test_tool_call_sentinels_do_not_break_parsing(self) -> None:
        text = '<|tool_call_begin|>read_file<|tool_call_end|>{"tool":"read_file","arguments":{"path":"Foo.lean"}}'
        calls = lean_tools._tool_calls_from_text(text)
        self.assertEqual(calls[0]["function"]["name"], "read_file")
        self.assertEqual(calls[0]["function"]["arguments"], {"path": "Foo.lean"})

    def test_pure_sentinel_noise_yields_no_call(self) -> None:
        # No structured call present -> genuinely empty, must not fabricate one.
        self.assertEqual(lean_tools._tool_calls_from_text("<|im_end|>\n<|im_start|>assistant\n"), [])

    def _fixture_records(self) -> list[dict[str, object]]:
        records = []
        for line in FIXTURE.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            record = json.loads(line)
            if "expected_tool" in record:
                records.append(record)
        return records


class ToolProtocolSelectionTests(unittest.TestCase):
    def test_preflight_validates_json_text_fallback_from_actual_response(self) -> None:
        responses = [
            non_streaming_response("ok"),
            non_streaming_response("<|im_first|>False<|tool_call_end|>"),
            non_streaming_response(
                '{"tool":"preflight_echo","arguments":{"value":"ok"}}<|im_end|>'
            ),
        ]
        with mock.patch.object(transport_preflight, "chat_completion", side_effect=responses):
            result = transport_preflight.generic_preflight(
                base_url="http://provider.test/v1", model="leanstral-test"
            )

        self.assertEqual(result["status"], "passed")
        self.assertFalse(result["checks"]["tool_calls"])
        self.assertTrue(result["checks"]["json_text_fallback"])
        self.assertTrue(result["checks"]["json_text_fallback_probed"])
        self.assertEqual(result["checks"]["json_text_fallback_attempts"], 1)
        self.assertEqual(result["usage"]["requests"], 3)

    def test_preflight_rejects_unvalidated_json_text_fallback(self) -> None:
        responses = [
            non_streaming_response("ok"),
            non_streaming_response("<|im_first|>False<|tool_call_end|>"),
            non_streaming_response("False"),
            non_streaming_response("False"),
            non_streaming_response("False"),
        ]
        with mock.patch.object(transport_preflight, "chat_completion", side_effect=responses):
            result = transport_preflight.generic_preflight(
                base_url="http://provider.test/v1", model="leanstral-test"
            )

        self.assertEqual(result["status"], "failed")
        self.assertFalse(result["checks"]["tool_calls"])
        self.assertFalse(result["checks"]["json_text_fallback"])
        self.assertEqual(result["checks"]["json_text_fallback_attempts"], 3)
        self.assertEqual(result["usage"]["requests"], 5)
        self.assertIn("neither native tool calls", result["error"])

    def test_preflight_retries_stochastic_json_text_negotiation(self) -> None:
        responses = [
            non_streaming_response("ok"),
            non_streaming_response("False"),
            non_streaming_response("False"),
            non_streaming_response('{"tool":"preflight_echo","arguments":{"value":"ok"}}'),
        ]
        with mock.patch.object(transport_preflight, "chat_completion", side_effect=responses):
            result = transport_preflight.generic_preflight(
                base_url="http://provider.test/v1", model="leanstral-test"
            )

        self.assertEqual(result["status"], "passed")
        self.assertTrue(result["checks"]["json_text_fallback"])
        self.assertEqual(result["checks"]["json_text_fallback_attempts"], 2)
        self.assertEqual(result["usage"]["requests"], 4)

    def test_preflight_downgrades_to_json_when_native_tools_are_missing(self) -> None:
        preflight = {
            "checks": {
                "tool_calls": False,
                "json_text_fallback": True,
            }
        }
        with mock.patch.object(lean_tools, "DEFAULT_NATIVE_TOOLS", True):
            self.assertFalse(lean_tools._native_tools_for_preflight(preflight))

    def test_preflight_keeps_native_tools_when_supported(self) -> None:
        preflight = {
            "checks": {
                "tool_calls": True,
                "json_text_fallback": True,
            }
        }
        with mock.patch.object(lean_tools, "DEFAULT_NATIVE_TOOLS", True):
            self.assertTrue(lean_tools._native_tools_for_preflight(preflight))

    def test_empty_completions_are_retried_and_keep_role_metrics(self) -> None:
        with tempfile.TemporaryDirectory() as raw_tmp:
            tmp = Path(raw_tmp)
            editable = "Benchmark/Generated/Test.lean"
            proof_path = tmp / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text("theorem test : True := by\n  sorry\n", encoding="utf-8")
            task = {
                "task_ref": "test/group/task",
                "task_id": "task",
                "theorem_name": "test",
                "editable_files": [editable],
                "target_module": "Benchmark.Generated.Test",
            }
            empty = non_streaming_response("")
            with mock.patch.object(lean_tools, "chat_completion", return_value=empty) as completion:
                result = lean_tools._attempt_task_fair(
                    task,
                    tmp,
                    base_url="http://provider.test/v1",
                    max_attempts=1,
                    max_tool_calls=1,
                    attempts_dir=tmp / "attempts",
                    tool_log_path=tmp / "tools.jsonl",
                    conversation_log_path=tmp / "conversation.jsonl",
                    native_tools=False,
                )
            self.assertEqual(completion.call_count, 3)
            self.assertEqual(result["status"], "failed_no_tool_calls")
            self.assertEqual(result["no_tool_responses"], 3)
            self.assertIn("role_metrics", result)

    def test_repetition_termination_keeps_role_metrics(self) -> None:
        with tempfile.TemporaryDirectory() as raw_tmp:
            tmp = Path(raw_tmp)
            editable = "Benchmark/Generated/Test.lean"
            proof_path = tmp / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text("theorem test : True := by\n  sorry\n", encoding="utf-8")
            task = {
                "task_ref": "test/group/task",
                "task_id": "task",
                "theorem_name": "test",
                "editable_files": [editable],
                "target_module": "Benchmark.Generated.Test",
            }
            response = non_streaming_response("not a tool call")
            with mock.patch.object(lean_tools, "chat_completion", return_value=response):
                result = lean_tools._attempt_task_fair(
                    task,
                    tmp,
                    base_url="http://provider.test/v1",
                    max_attempts=1,
                    max_tool_calls=1,
                    attempts_dir=tmp / "attempts",
                    tool_log_path=tmp / "tools.jsonl",
                    conversation_log_path=tmp / "conversation.jsonl",
                    native_tools=False,
                )
            self.assertEqual(result["status"], "repetition_loop")
            self.assertIn("role_metrics", result)

    def test_json_compaction_preserves_repetition_correction(self) -> None:
        with tempfile.TemporaryDirectory() as raw_tmp:
            tmp = Path(raw_tmp)
            editable = "Benchmark/Generated/Test.lean"
            proof_path = tmp / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text("theorem test : True := by\n  exact True.intro\n", encoding="utf-8")
            task = {
                "task_ref": "test/group/task",
                "task_id": "task",
                "theorem_name": "test",
                "editable_files": [editable],
                "target_module": "Benchmark.Generated.Test",
            }
            responses = [
                '{"tool":"show_task","arguments":{}}',
                f'{{"tool":"read_file","arguments":{{"path":"{editable}"}}}}',
                f'{{"tool":"read_file","arguments":{{"path":"{editable}"}}}}',
                '{"tool":"check_proof","arguments":{"proof":"exact True.intro"}}',
            ]
            request_index = 0

            def completion(messages: list[dict[str, object]], **_: object) -> dict[str, object]:
                nonlocal request_index
                if request_index == 3:
                    latest = str(messages[-1].get("content") or "")
                    self.assertIn("repeated the same unproductive action", latest)
                    self.assertIn("Tool result for read_file", latest)
                response = non_streaming_response(responses[request_index])
                request_index += 1
                return response

            def execute(name: str, *_: object, **__: object) -> dict[str, object]:
                if name == "check_proof":
                    return {"ok": True, "passed": True}
                return {"ok": True}

            with (
                mock.patch.object(lean_tools, "chat_completion", side_effect=completion),
                mock.patch.object(lean_tools, "_execute_fair_tool", side_effect=execute),
            ):
                result = lean_tools._attempt_task_fair(
                    task,
                    tmp,
                    base_url="http://provider.test/v1",
                    max_attempts=1,
                    max_tool_calls=4,
                    attempts_dir=tmp / "attempts",
                    tool_log_path=tmp / "tools.jsonl",
                    conversation_log_path=tmp / "conversation.jsonl",
                    native_tools=False,
                )

            self.assertEqual(result["status"], "lean_passed")
            self.assertEqual(request_index, 4)

    def test_json_tool_results_do_not_reissue_first_call_instruction(self) -> None:
        with tempfile.TemporaryDirectory() as raw_tmp:
            tmp = Path(raw_tmp)
            editable = "Benchmark/Generated/Test.lean"
            proof_path = tmp / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text("theorem test : True := by\n  sorry\n", encoding="utf-8")
            task = {
                "task_ref": "test/group/task",
                "task_id": "task",
                "theorem_name": "test",
                "editable_files": [editable],
                "target_module": "Benchmark.Generated.Test",
            }
            request_count = 0

            def completion(messages: list[dict[str, object]], **_: object) -> dict[str, object]:
                nonlocal request_count
                request_count += 1
                if request_count == 1:
                    return non_streaming_response('{"tool":"show_task","arguments":{}}')
                if request_count == 2:
                    latest = str(messages[-1].get("content") or "")
                    self.assertIn("show_task was already called", latest)
                    self.assertNotIn("First call show_task", latest)
                return non_streaming_response("")

            with mock.patch.object(lean_tools, "chat_completion", side_effect=completion):
                result = lean_tools._attempt_task_fair(
                    task,
                    tmp,
                    base_url="http://provider.test/v1",
                    max_attempts=1,
                    max_tool_calls=2,
                    attempts_dir=tmp / "attempts",
                    tool_log_path=tmp / "tools.jsonl",
                    conversation_log_path=tmp / "conversation.jsonl",
                    native_tools=False,
                )
            self.assertEqual(result["tool_calls_executed"], 1)
            self.assertEqual(result["status"], "failed_no_tool_calls")


class DegenerationClassificationTests(unittest.TestCase):
    def _verifier_target(self, task_ref: str, status: str = "no_submission") -> dict[str, object]:
        return {"task_ref": task_ref, "status": status, "output": ""}

    def test_failed_no_tool_calls_without_submission_is_infra_invalid(self) -> None:
        task_result = {
            "task_ref": "alchemix/earmark/earmark_preserves_invariant",
            "status": "failed_no_tool_calls",
            "failure_class": "no_tool_calls",
            "no_tool_responses": 7,
            "attempts": [],
        }
        result = classify_target(self._verifier_target(task_result["task_ref"]), task_result)
        self.assertEqual(result["final_class"], "INFRA_INVALID")
        self.assertFalse(result["reusable"])
        self.assertIn("provider_invalid_tool_protocol", result["final_reason"])

    def test_malformed_tool_call_without_submission_is_infra_invalid(self) -> None:
        task_result = {
            "task_ref": "grp/iface/malformed",
            "status": "malformed_tool_call",
            "failure_class": "malformed_tool_call",
            "attempts": [],
        }
        result = classify_target(self._verifier_target(task_result["task_ref"]), task_result)
        self.assertEqual(result["final_class"], "INFRA_INVALID")

    def test_no_tool_calls_with_gradeable_submission_stays_genuine(self) -> None:
        # The model reached a real proof attempt; a later no-tool turn must not
        # launder a genuine failure into infra-invalid.
        task_result = {
            "task_ref": "grp/iface/worked",
            "status": "failed_submitted",
            "failure_class": "lean_unsolved_goal",
            "no_tool_responses": 2,
            "attempts": [{"attempt": 1, "status": "lean_failed", "candidate_path": "a.lean"}],
        }
        result = classify_target(self._verifier_target(task_result["task_ref"], "lean_check_failed"), task_result)
        self.assertEqual(result["final_class"], "GENUINE_FAIL")
        self.assertTrue(result["reusable"])

    def test_failed_no_attempt_stays_genuine(self) -> None:
        # The model made real tool calls but never submitted a proof. That is a
        # genuine give-up, not a tool-protocol breakdown, so it must not be
        # laundered into INFRA_INVALID by the degeneration gate.
        task_result = {
            "task_ref": "grp/iface/gaveup",
            "status": "failed_no_attempt",
            "failure_class": "no_submission",
            "attempts": [],
        }
        result = classify_target(self._verifier_target(task_result["task_ref"]), task_result)
        self.assertEqual(result["final_class"], "GENUINE_FAIL")
        self.assertTrue(result["reusable"])

    def test_run_of_all_degenerate_tasks_is_infra_invalid(self) -> None:
        verifier = {
            "score": {"total_targets": 2, "passed_targets": 0},
            "targets": [self._verifier_target("g/i/a"), self._verifier_target("g/i/b")],
        }
        task_results = [
            {"task_ref": "g/i/a", "status": "failed_no_tool_calls", "failure_class": "no_tool_calls", "no_tool_responses": 7, "attempts": []},
            {"task_ref": "g/i/b", "status": "failed_no_tool_calls", "failure_class": "no_tool_calls", "no_tool_responses": 7, "attempts": []},
        ]
        summary = classify_run(verifier, task_results)
        self.assertEqual(summary["run_class"], "INFRA_INVALID")
        self.assertFalse(summary["reusable"])


if __name__ == "__main__":
    unittest.main()
