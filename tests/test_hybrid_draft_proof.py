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


class HybridDraftProofTests(unittest.TestCase):
    def test_default_tool_list_is_unchanged_when_draft_mode_disabled(self) -> None:
        with mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", False):
            tools = lean_tools._fair_tools()
        self.assertIs(tools, lean_tools.FAIR_TOOLS)
        self.assertNotIn("draft_proof", [tool["function"]["name"] for tool in tools])

    def test_draft_proof_invokes_prover_model_and_writes_audit_log(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            log_path = Path(tmp) / "draft.jsonl"
            calls: list[dict[str, object]] = []

            def fake_chat_completion(messages: list[dict[str, object]], **kwargs: object) -> dict[str, object]:
                calls.append({"messages": messages, **kwargs})
                return {
                    "choices": [{"message": {"role": "assistant", "content": "trivial"}}],
                    "usage": {"prompt_tokens": 10, "completion_tokens": 1, "total_tokens": 11},
                }

            with (
                mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True),
                mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"),
                mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"),
                mock.patch.object(lean_tools, "chat_completion", fake_chat_completion),
            ):
                result = lean_tools._draft_proof_with_prover(
                    {"task_context": "Need a proof of True", "goal": "⊢ True", "errors": ""},
                    task={"task_ref": "sample/group/task", "target_module": "Benchmark.Generated.Sample"},
                    original=ORIGINAL,
                    base_url="http://provider.test/v1",
                    draft_log_path=log_path,
                )

            self.assertTrue(result["ok"])
            self.assertEqual(result["proof"], "trivial")
            self.assertEqual(calls[0]["model"], "prover-model")
            self.assertIsNone(calls[0]["tools"])
            audit = json.loads(log_path.read_text(encoding="utf-8").strip())
            self.assertEqual(audit["status"], "drafted")
            self.assertEqual(audit["driver_model"], "driver-model")
            self.assertEqual(audit["prover_model"], "prover-model")

    def test_driver_can_call_draft_tool_before_checking_proof(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            proof_rel = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / proof_rel
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(ORIGINAL, encoding="utf-8")
            calls: list[str] = []

            def fake_chat_completion(messages: list[dict[str, object]], **kwargs: object) -> dict[str, object]:
                model = str(kwargs.get("model"))
                calls.append(model)
                if model == "prover-model":
                    return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
                if calls.count("driver-model") == 1:
                    return {
                        "choices": [
                            {
                                "message": {
                                    "role": "assistant",
                                    "content": None,
                                    "tool_calls": [
                                        {
                                            "id": "draft-1",
                                            "function": {
                                                "name": "draft_proof",
                                                "arguments": json.dumps({"task_context": "Need a proof of True", "goal": "⊢ True", "errors": ""}),
                                            },
                                        }
                                    ],
                                }
                            }
                        ]
                    }
                return {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": None,
                                "tool_calls": [
                                    {
                                        "id": "proof-1",
                                        "function": {"name": "check_proof", "arguments": json.dumps({"proof": "trivial"})},
                                    }
                                ],
                            }
                        }
                    ]
                }

            with (
                mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True),
                mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"),
                mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"),
                mock.patch.object(lean_tools, "chat_completion", fake_chat_completion),
                mock.patch.object(lean_tools, "_run_lean_module", lambda *args, **kwargs: (0, "")),
            ):
                result = lean_tools._attempt_task_fair(
                    {
                        "task_ref": "sample/group/task",
                        "task_id": "task",
                        "target_module": "Benchmark.Generated.Sample",
                        "editable_files": [proof_rel],
                        "specification_files": [],
                        "implementation_files": [],
                    },
                    workspace,
                    base_url="http://provider.test/v1",
                    max_attempts=1,
                    max_tool_calls=3,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tool-calls.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    draft_log_path=workspace / "draft.jsonl",
                )

            self.assertEqual(result["status"], "lean_passed")
            self.assertEqual(calls, ["driver-model", "prover-model", "driver-model"])
            self.assertEqual(len(result["attempts"]), 1)
            entries = [json.loads(line) for line in (workspace / "tool-calls.jsonl").read_text(encoding="utf-8").splitlines()]
            self.assertEqual([entry["tool"] for entry in entries], ["draft_proof", "check_proof"])

    def test_draft_proof_usage_counts_toward_task_budget(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            proof_rel = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / proof_rel
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(ORIGINAL, encoding="utf-8")
            calls: list[str] = []

            def fake_chat_completion(messages: list[dict[str, object]], **kwargs: object) -> dict[str, object]:
                model = str(kwargs.get("model"))
                calls.append(model)
                if model == "prover-model":
                    return {
                        "choices": [{"message": {"role": "assistant", "content": "trivial"}}],
                        "usage": {"prompt_tokens": 8, "completion_tokens": 3, "total_tokens": 11},
                    }
                return {
                    "choices": [
                        {
                            "message": {
                                "role": "assistant",
                                "content": None,
                                "tool_calls": [
                                    {
                                        "id": "draft-1",
                                        "function": {
                                            "name": "draft_proof",
                                            "arguments": json.dumps({"task_context": "Need a proof of True"}),
                                        },
                                    }
                                ],
                            }
                        }
                    ],
                    "usage": {"prompt_tokens": 5, "completion_tokens": 2, "total_tokens": 7},
                }

            with (
                mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True),
                mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"),
                mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"),
                mock.patch.object(lean_tools, "DEFAULT_TOKEN_BUDGET", 5),
                mock.patch.object(lean_tools, "chat_completion", fake_chat_completion),
                mock.patch.object(lean_tools, "_run_lean_module", lambda *args, **kwargs: (0, "")),
            ):
                result = lean_tools._attempt_task_fair(
                    {
                        "task_ref": "sample/group/task",
                        "task_id": "task",
                        "target_module": "Benchmark.Generated.Sample",
                        "editable_files": [proof_rel],
                        "specification_files": [],
                        "implementation_files": [],
                    },
                    workspace,
                    base_url="http://provider.test/v1",
                    max_attempts=1,
                    max_tool_calls=3,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tool-calls.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    draft_log_path=workspace / "draft.jsonl",
                )

            self.assertEqual(calls, ["driver-model", "prover-model"])
            self.assertEqual(result["status"], "failed_no_attempt")
            self.assertTrue(result["token_budget_exhausted"])
            self.assertEqual(result["usage"], {"prompt_tokens": 13, "completion_tokens": 5, "total_tokens": 18, "requests": 2})
            self.assertEqual(result["attempts"], [])

    def test_forbidden_prover_output_is_rejected_without_proof_attempt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            proof_path = workspace / "Benchmark" / "Generated" / "Sample.lean"
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(ORIGINAL, encoding="utf-8")
            attempts: list[dict[str, object]] = []

            def fake_chat_completion(*args: object, **kwargs: object) -> dict[str, object]:
                return {"choices": [{"message": {"role": "assistant", "content": "sorry"}}]}

            with (
                mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True),
                mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"),
                mock.patch.object(lean_tools, "chat_completion", fake_chat_completion),
            ):
                result = lean_tools._execute_fair_tool(
                    "draft_proof",
                    {"task_context": "Need a proof of True"},
                    task={"task_ref": "sample/group/task", "target_module": "Benchmark.Generated.Sample"},
                    workspace=workspace,
                    original=ORIGINAL,
                    proof_path=proof_path,
                    target_module="Benchmark.Generated.Sample",
                    attempts_dir=workspace / "attempts",
                    attempts=attempts,
                    base_url="http://provider.test/v1",
                    draft_log_path=workspace / "draft.jsonl",
                )

            self.assertFalse(result["ok"])
            self.assertEqual(result["error"], "prover_output_contains_forbidden_placeholder")
            self.assertEqual(attempts, [])
            self.assertEqual(proof_path.read_text(encoding="utf-8"), ORIGINAL)


if __name__ == "__main__":
    unittest.main()
