"""Repetition guard semantics for the fair Lean tool loop.

Two actions are repeats only when their *full* canonical payload is identical,
and a run is stopped only after identical actions repeat consecutively
(warning on the 2nd, stop on the 3rd). Distinct proofs that share a long
identical header must never be treated as repeats.
"""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.runners import lean_tools

HEADER = "-- shared header\n" + "have h : True := trivial\n" * 40  # > 500 chars
assert len(json.dumps({"proof": HEADER})) > 600


def text_response(content: str) -> dict[str, object]:
    return {
        "choices": [{"index": 0, "message": {"role": "assistant", "content": content}, "finish_reason": "stop"}],
        "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
    }


def tool_text(tool: str, arguments: dict[str, object]) -> str:
    return json.dumps({"tool": tool, "arguments": arguments})


class SignatureTests(unittest.TestCase):
    def test_distinct_payloads_with_identical_500_char_prefix_differ(self) -> None:
        a = {"proof": HEADER + "exact foo"}
        b = {"proof": HEADER + "exact bar"}
        self.assertEqual(json.dumps(a, sort_keys=True)[:500], json.dumps(b, sort_keys=True)[:500])
        self.assertNotEqual(
            lean_tools._action_signature("tool:check_proof", a),
            lean_tools._action_signature("tool:check_proof", b),
        )

    def test_signature_is_canonical_over_key_order(self) -> None:
        self.assertEqual(
            lean_tools._action_signature("tool:x", {"a": 1, "b": 2}),
            lean_tools._action_signature("tool:x", {"b": 2, "a": 1}),
        )
        self.assertNotEqual(
            lean_tools._action_signature("tool:x", {"a": 1}),
            lean_tools._action_signature("tool:y", {"a": 1}),
        )

    def test_tracker_counts_only_consecutive_repeats(self) -> None:
        tracker = lean_tools._RepetitionTracker()
        self.assertEqual([tracker.observe(s) for s in ["a", "a", "b", "a", "a", "a"]], [1, 2, 1, 1, 2, 3])


class FairLoopRepetitionTests(unittest.TestCase):
    def run_loop(self, responses: list[str], *, max_tool_calls: int = 10) -> tuple[dict[str, object], int]:
        with tempfile.TemporaryDirectory() as raw_tmp:
            tmp = Path(raw_tmp)
            editable = "Benchmark/Generated/Test.lean"
            proof_path = tmp / editable
            proof_path.parent.mkdir(parents=True)
            proof_path.write_text("theorem test : True := by\n  exact ?_\n", encoding="utf-8")
            task = {
                "task_ref": "test/group/task",
                "task_id": "task",
                "theorem_name": "test",
                "editable_files": [editable],
                "target_module": "Benchmark.Generated.Test",
            }
            calls = 0

            def completion(*_: object, **__: object) -> dict[str, object]:
                nonlocal calls
                response = text_response(responses[min(calls, len(responses) - 1)])
                calls += 1
                return response

            def execute(name: str, args: dict[str, object], *_: object, **__: object) -> dict[str, object]:
                if name == "check_proof":
                    return {"ok": True, "passed": str(args.get("proof", "")).endswith("PASS")}
                return {"ok": True}

            with (
                mock.patch.object(lean_tools, "chat_completion", side_effect=completion),
                mock.patch.object(lean_tools, "_execute_fair_tool", side_effect=execute),
            ):
                result = lean_tools._attempt_task_fair(
                    task,
                    tmp,
                    base_url="http://provider.test/v1",
                    max_attempts=16,
                    max_tool_calls=max_tool_calls,
                    attempts_dir=tmp / "attempts",
                    tool_log_path=tmp / "tools.jsonl",
                    conversation_log_path=tmp / "conversation.jsonl",
                    native_tools=False,
                )
            return result, calls

    def test_distinct_long_proofs_with_shared_prefix_do_not_trigger(self) -> None:
        responses = [tool_text("check_proof", {"proof": HEADER + f"exact attempt_{i}"}) for i in range(5)]
        responses.append(tool_text("check_proof", {"proof": HEADER + "PASS"}))
        result, calls = self.run_loop(responses)
        self.assertEqual(result["status"], "lean_passed")
        self.assertEqual(calls, 6)

    def test_identical_consecutive_actions_still_stop(self) -> None:
        same = tool_text("check_proof", {"proof": HEADER + "exact same"})
        result, calls = self.run_loop([same, same, same, tool_text("check_proof", {"proof": "PASS"})])
        self.assertEqual(result["status"], "repetition_loop")
        self.assertEqual(calls, 3)
        self.assertEqual(result["loop_repeat_count"], 3)
        self.assertTrue(str(result["loop_signature"]).startswith("tool:check_proof:sha256:"))
        self.assertIn("exact same", str(result["loop_signature_preview"]))

    def test_identical_actions_separated_by_different_action_do_not_stop(self) -> None:
        read = tool_text("read_file", {"path": "Benchmark/Generated/Test.lean"})
        responses = [
            read,
            tool_text("check_proof", {"proof": "exact one"}),
            read,
            tool_text("check_proof", {"proof": "exact two"}),
            read,
            tool_text("check_proof", {"proof": "PASS"}),
        ]
        result, calls = self.run_loop(responses)
        self.assertEqual(result["status"], "lean_passed")
        self.assertEqual(calls, 6)

    def test_identical_no_tool_text_still_stops(self) -> None:
        result, calls = self.run_loop(["I am thinking. " * 50])
        self.assertEqual(result["status"], "repetition_loop")
        self.assertTrue(str(result["loop_signature"]).startswith("no-tool:sha256:"))


if __name__ == "__main__":
    unittest.main()
