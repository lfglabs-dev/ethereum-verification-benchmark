from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.runners import lean_tools


ORIGINAL = """theorem sample : True := by
  sorry
"""

SYSTEM_PROMPT = "You are a Lean proof engineer. Use the fair tools."


def _failed_attempt(**overrides: object) -> dict[str, object]:
    attempt: dict[str, object] = {
        "attempt": "tool:check_proof",
        "status": "lean_failed",
        "exit_code": 1,
        "candidate_path": None,
        "output": "Benchmark/Generated/Sample.lean:2:2: error: unsolved goals\n⊢ x + 0 = x",
        "failure_kind": "lean_unsolved_goals",
        "diagnostics": {
            "changed_goal": True,
            "new_goal": "x + 0 = x",
            "first_error": "unsolved goals",
            "failure_kind": "lean_unsolved_goals",
            "local_hypotheses": ["x : Nat"],
        },
        "hint": "The goal is not closed; inspect it with show_goal.",
    }
    attempt.update(overrides)
    return attempt


class RepairPromptContentTests(unittest.TestCase):
    def test_repair_prompt_is_compact_and_focused(self) -> None:
        content = lean_tools._repair_prompt_user_content(
            task={
                "task_ref": "erc20/state/transfer",
                "theorem_name": "transfer_spec",
                "specification_files": ["Spec.lean"],
            },
            editable="Benchmark/Generated/Sample.lean",
            candidate="theorem sample : True := by\n  simp",
            attempt=_failed_attempt(),
            minimal_hint=False,
        )

        # It focuses the model on repairing the existing proof.
        self.assertIn("Repair the existing proof", content)
        self.assertIn("theorem sample : True := by", content)
        self.assertIn("transfer_spec", content)
        self.assertIn("x + 0 = x", content)
        self.assertIn("unsolved goals", content)
        self.assertIn("single check_proof call", content)
        # It must NOT re-send the full task summary or bundled proof patterns.
        self.assertNotIn("TASK_SUMMARY", content)
        self.assertNotIn("proof_patterns", content)

    def test_candidate_and_output_are_truncated(self) -> None:
        big_candidate = "-- filler\n" * 2000
        big_output = "err line\n" * 2000
        content = lean_tools._repair_prompt_user_content(
            task={"task_ref": "t"},
            editable="F.lean",
            candidate=big_candidate,
            attempt=_failed_attempt(output=big_output, diagnostics={}, hint=""),
            minimal_hint=False,
        )
        self.assertIn("[candidate truncated for repair prompt]", content)
        # Both the candidate and the error tail are bounded by the char caps
        # (plus small headers/markers), so the prompt stays small.
        self.assertLess(
            len(content),
            lean_tools.REPAIR_PROMPT_CANDIDATE_CHARS + lean_tools.REPAIR_PROMPT_ERROR_CHARS + 2000,
        )

    def test_minimal_hint_only_appears_for_automation_failures(self) -> None:
        timeout_attempt = _failed_attempt(failure_kind="lean_timeout", diagnostics={}, hint="")
        with_hint = lean_tools._repair_prompt_user_content(
            task={"task_ref": "t"},
            editable="F.lean",
            candidate="body",
            attempt=timeout_attempt,
            minimal_hint=True,
        )
        self.assertIn(lean_tools.MINIMAL_PROOF_HINT, with_hint)

        parse_attempt = _failed_attempt(
            failure_kind="lean_parse_error",
            output="unexpected token",
            diagnostics={},
            hint="",
        )
        without_hint = lean_tools._repair_prompt_user_content(
            task={"task_ref": "t"},
            editable="F.lean",
            candidate="body",
            attempt=parse_attempt,
            minimal_hint=True,
        )
        self.assertNotIn(lean_tools.MINIMAL_PROOF_HINT, without_hint)

    def test_minimal_hint_triggers_on_grind_marker(self) -> None:
        attempt = _failed_attempt(
            failure_kind="lean_parse_error",  # not an automation kind
            output="error: grind failed to close the goal",
            diagnostics={},
            hint="",
        )
        self.assertTrue(lean_tools._minimal_proof_hint_applies(attempt))

    def test_minimal_hint_is_content_free(self) -> None:
        # The nudge must never name a task, spec, or concrete proof term - it is a
        # generic strategy tip only, safe to ship in a public harness.
        hint = lean_tools.MINIMAL_PROOF_HINT.lower()
        for banned in ("transfer", "erc20", "balance", "theorem ", ":= by"):
            self.assertNotIn(banned, hint)


class RepairMessagesTests(unittest.TestCase):
    def test_repair_messages_are_two_role_compact_list(self) -> None:
        messages = lean_tools._diagnostic_repair_messages(
            system_prompt=SYSTEM_PROMPT,
            task={"task_ref": "t", "theorem_name": "foo"},
            editable="F.lean",
            candidate="body",
            attempt=_failed_attempt(),
            minimal_hint=False,
        )
        self.assertEqual([m["role"] for m in messages], ["system", "user"])
        # The base system prompt is kept but must be overridden so the model
        # does not obey its "call show_task first" instruction during repair.
        self.assertTrue(messages[0]["content"].startswith(SYSTEM_PROMPT))
        self.assertIn("REPAIR MODE", messages[0]["content"])
        self.assertIn("do not call show_task", messages[0]["content"])
        self.assertIn("Repair the existing proof", messages[1]["content"])


class LastFailedAttemptTests(unittest.TestCase):
    def test_picks_most_recent_non_passing_attempt(self) -> None:
        result = {
            "results": [
                {"status": "lean_failed", "failure_kind": "a"},
                {"status": "rejected_forbidden_placeholder"},
                {"status": "lean_failed", "failure_kind": "latest"},
            ]
        }
        picked = lean_tools._last_failed_proof_attempt(result)
        assert picked is not None
        self.assertEqual(picked["failure_kind"], "latest")

    def test_returns_none_when_last_passed(self) -> None:
        result = {"results": [{"status": "lean_failed"}, {"status": "lean_passed"}]}
        # A passing attempt short-circuits the loop before repair, but guard anyway:
        picked = lean_tools._last_failed_proof_attempt(result)
        assert picked is not None
        self.assertEqual(picked["status"], "lean_failed")

    def test_returns_none_without_results(self) -> None:
        self.assertIsNone(lean_tools._last_failed_proof_attempt({}))


class AttemptLoopRepairSwapTests(unittest.TestCase):
    def _task(self, proof_rel: str) -> dict[str, object]:
        return {
            "task_ref": "sample/group/task",
            "task_id": "task",
            "target_module": "Benchmark.Generated.Sample",
            "editable_files": [proof_rel],
            "specification_files": [],
            "implementation_files": [],
        }

    def test_failed_check_proof_swaps_in_compact_repair_prompt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            proof_rel = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / proof_rel
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(ORIGINAL, encoding="utf-8")

            captured_messages: list[list[dict[str, object]]] = []

            def fake_run(workspace_arg: Path, module: str, file_rel: str) -> tuple[int, str]:
                text = (workspace_arg / file_rel).read_text(encoding="utf-8")
                if "trivial" in text:
                    return 0, ""
                return 1, "Benchmark/Generated/Sample.lean:2:2: error: unsolved goals\n⊢ True"

            def fake_chat_completion(messages: list[dict[str, object]], **kwargs: object) -> dict[str, object]:
                captured_messages.append([dict(m) for m in messages])
                body = "grind" if len(captured_messages) == 1 else "trivial"
                return {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": None,
                                "tool_calls": [
                                    {
                                        "id": f"call-{len(captured_messages)}",
                                        "function": {
                                            "name": "check_proof",
                                            "arguments": json.dumps({"proof": body}),
                                        },
                                    }
                                ],
                            }
                        }
                    ]
                }

            with (
                mock.patch.object(lean_tools, "chat_completion", fake_chat_completion),
                mock.patch.object(lean_tools, "_run_lean_module", fake_run),
            ):
                result = lean_tools._attempt_task_fair(
                    self._task(proof_rel),
                    workspace,
                    base_url="http://provider.test/v1",
                    max_attempts=3,
                    max_tool_calls=5,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tool-calls.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    draft_log_path=workspace / "draft.jsonl",
                )

            self.assertEqual(result["status"], "lean_passed")
            # Second driver request must be the compact repair prompt, not the
            # accumulated transcript.
            self.assertGreaterEqual(len(captured_messages), 2)
            repair = captured_messages[1]
            self.assertEqual([m["role"] for m in repair], ["system", "user"])
            self.assertIn("Repair the existing proof", repair[1]["content"])
            # The failed candidate submitted grind, which trips the automation
            # fallback nudge.
            self.assertIn(lean_tools.MINIMAL_PROOF_HINT, repair[1]["content"])

    def test_repair_path_disabled_falls_back_to_compaction(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            proof_rel = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / proof_rel
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(ORIGINAL, encoding="utf-8")

            captured_messages: list[list[dict[str, object]]] = []

            def fake_run(workspace_arg: Path, module: str, file_rel: str) -> tuple[int, str]:
                text = (workspace_arg / file_rel).read_text(encoding="utf-8")
                if "trivial" in text:
                    return 0, ""
                return 1, "error: unsolved goals\n⊢ True"

            def fake_chat_completion(messages: list[dict[str, object]], **kwargs: object) -> dict[str, object]:
                captured_messages.append([dict(m) for m in messages])
                body = "grind" if len(captured_messages) == 1 else "trivial"
                return {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": None,
                                "tool_calls": [
                                    {
                                        "id": f"call-{len(captured_messages)}",
                                        "function": {"name": "check_proof", "arguments": json.dumps({"proof": body})},
                                    }
                                ],
                            }
                        }
                    ]
                }

            with (
                mock.patch.object(lean_tools, "DIAGNOSTIC_RETRY_ENABLED", False),
                mock.patch.object(lean_tools, "chat_completion", fake_chat_completion),
                mock.patch.object(lean_tools, "_run_lean_module", fake_run),
            ):
                lean_tools._attempt_task_fair(
                    self._task(proof_rel),
                    workspace,
                    base_url="http://provider.test/v1",
                    max_attempts=3,
                    max_tool_calls=5,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tool-calls.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    draft_log_path=workspace / "draft.jsonl",
                )

            # With retry disabled, the second request keeps the accumulated
            # transcript (tool role messages present), not a 2-message reset.
            self.assertGreaterEqual(len(captured_messages), 2)
            self.assertTrue(any(m.get("role") == "tool" for m in captured_messages[1]))


if __name__ == "__main__":
    unittest.main()
