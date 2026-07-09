from __future__ import annotations

import json
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest import mock

from harness.runners import lean_tools


ORIGINAL = """theorem sample : True := by
  sorry
"""

SPEC = """namespace Benchmark.Spec

def transfer_spec (x : Nat) : Prop := x + 0 = x

private def secret_helper : Nat := 41

theorem transfer_public (x : Nat) : x + 0 = x := by simp

end Benchmark.Spec
"""


def _strict_env(stack: ExitStack, *, repair_attempts: int = 2, decl_index: int = 40) -> None:
    """Patch module constants so strict hybrid mode is active with a distinct
    driver and prover model, without touching the real environment."""
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True))
    stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", True))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODE", "draft_proof"))
    stack.enter_context(mock.patch.object(lean_tools, "PROVER_REPAIR_ATTEMPTS", repair_attempts))
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_DECL_INDEX_LIMIT", decl_index))


def _task(proof_rel: str, workspace: Path) -> dict[str, object]:
    spec_rel = "Benchmark/Spec.lean"
    (workspace / spec_rel).parent.mkdir(parents=True, exist_ok=True)
    (workspace / spec_rel).write_text(SPEC, encoding="utf-8")
    return {
        "task_ref": "erc20/state/transfer",
        "task_id": "transfer",
        "target_module": "Benchmark.Generated.Sample",
        "theorem_name": "sample",
        "editable_files": [proof_rel],
        "specification_files": [spec_rel],
        "implementation_files": [],
    }


class RoleConfigTests(unittest.TestCase):
    def test_role_config_defaults_to_standalone_when_off(self) -> None:
        with ExitStack() as stack:
            stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", False))
            stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", False))
            stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "solo-model"))
            stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", ""))
            config = lean_tools._role_config()
        self.assertFalse(config["strict_role_separation"])
        self.assertFalse(config["ensemble"])
        self.assertTrue(config["driver_writes_proofs"])
        self.assertEqual(config["role_label"], "standalone: solo-model")

    def test_role_config_marks_strict_hybrid_ensemble(self) -> None:
        with ExitStack() as stack:
            _strict_env(stack)
            config = lean_tools._role_config()
        self.assertTrue(config["strict_role_separation"])
        self.assertTrue(config["ensemble"])
        self.assertFalse(config["driver_writes_proofs"])
        self.assertEqual(config["prover_repair_attempts"], 2)
        self.assertEqual(config["stages"][lean_tools.STAGE_WRITER], "prover-model")
        self.assertEqual(config["stages"][lean_tools.STAGE_REPAIRER], "prover-model")
        self.assertEqual(config["stages"][lean_tools.STAGE_DRIVER], "driver-model")
        # The ensemble label must name both roles so it cannot be mistaken for a
        # standalone writer-model score.
        self.assertIn("driver=driver-model", config["role_label"])
        self.assertIn("writer=prover-model", config["role_label"])

    def test_non_strict_hybrid_allows_driver_repair(self) -> None:
        with ExitStack() as stack:
            stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True))
            stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", False))
            stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"))
            stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"))
            config = lean_tools._role_config()
        self.assertTrue(config["ensemble"])
        self.assertTrue(config["driver_writes_proofs"])
        self.assertIn("driver_may_repair", config["role_label"])


class PromptFormattingTests(unittest.TestCase):
    def test_writer_prompt_is_body_only_with_declaration_index(self) -> None:
        messages = lean_tools._draft_proof_prompt(
            task={"task_ref": "erc20/state/transfer", "target_module": "M"},
            theorem_statement="theorem sample : True",
            task_context="Prove the transfer spec.",
            goal="⊢ True",
            errors="",
            prompt_kind="write",
            declaration_index="- def transfer_spec (x : Nat) : Prop",
        )
        self.assertEqual([m["role"] for m in messages], ["system", "user"])
        system = messages[0]["content"]
        self.assertIn("only the Lean proof body", system)
        self.assertIn("Do not return markdown", system)
        user = messages[1]["content"]
        self.assertIn("transfer_spec", user)
        self.assertIn("Available public declarations", user)

    def test_repair_prompt_includes_current_proof_and_minimal_edit(self) -> None:
        messages = lean_tools._draft_proof_prompt(
            task={"task_ref": "t", "target_module": "M"},
            theorem_statement="theorem sample : True",
            task_context="",
            goal="⊢ True",
            errors="error: unsolved goals",
            prompt_kind="repair",
            current_proof="simp",
        )
        self.assertIn("repairer", messages[0]["content"])
        self.assertIn("smallest edit", messages[0]["content"])
        self.assertIn("Current failing proof body", messages[1]["content"])
        self.assertIn("simp", messages[1]["content"])


class DraftRejectionTests(unittest.TestCase):
    def test_markdown_json_and_placeholders_are_rejected(self) -> None:
        self.assertEqual(lean_tools._reject_draft_reason("```lean\ntrivial\n```"), "prover_output_contains_markdown")
        self.assertEqual(lean_tools._reject_draft_reason('{"proof": "trivial"}'), "prover_output_looks_like_json")
        self.assertEqual(lean_tools._reject_draft_reason("theorem foo : True := by trivial"), "prover_output_contains_theorem_statement")
        self.assertEqual(lean_tools._reject_draft_reason("simp -- TODO finish"), "prover_output_contains_placeholder_text")
        self.assertEqual(lean_tools._reject_draft_reason("sorry"), "prover_output_contains_forbidden_placeholder")
        self.assertIsNone(lean_tools._reject_draft_reason("simp [transfer_spec]"))

    def test_draft_valid_syntax_flag(self) -> None:
        self.assertIs(lean_tools._draft_valid_syntax("simp [a, b]"), True)
        self.assertIs(lean_tools._draft_valid_syntax("simp [a, b"), False)
        self.assertIs(lean_tools._draft_valid_syntax(""), False)


class DeclarationIndexTests(unittest.TestCase):
    def test_index_lists_public_decls_and_skips_private(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            task = _task("Benchmark/Generated/Sample.lean", workspace)
            index = lean_tools._task_declaration_index(workspace, task, limit=40)
            names = {entry["name"] for entry in index}
            self.assertIn("Benchmark.Spec.transfer_spec", names)
            self.assertIn("Benchmark.Spec.transfer_public", names)
            # `private def secret_helper` must never be indexed.
            self.assertNotIn("Benchmark.Spec.secret_helper", names)

    def test_index_excludes_hidden_solution_paths(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            task = _task("Benchmark/Generated/Sample.lean", workspace)
            # Point the manifest at hidden reference-proof and preview files.
            for hidden in ("Benchmark/Proofs.lean", "Benchmark/GeneratedPreview/Leak.lean"):
                p = workspace / hidden
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("theorem leaked_solution : True := by trivial\n", encoding="utf-8")
            task["specification_files"] = ["Benchmark/Proofs.lean"]
            task["implementation_files"] = ["Benchmark/GeneratedPreview/Leak.lean"]
            task["editable_files"] = ["Benchmark/Proofs.lean"]
            sources = lean_tools._task_index_source_files(task)
            self.assertNotIn("Benchmark/Proofs.lean", sources)
            self.assertNotIn("Benchmark/GeneratedPreview/Leak.lean", sources)
            index = lean_tools._task_declaration_index(workspace, task, limit=40)
            names = {entry["name"] for entry in index}
            self.assertNotIn("leaked_solution", names)

    def test_index_respects_zero_limit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            task = _task("Benchmark/Generated/Sample.lean", workspace)
            self.assertEqual(lean_tools._task_declaration_index(workspace, task, limit=0), [])


class RepairOutcomeClassificationTests(unittest.TestCase):
    def test_pass_is_improved(self) -> None:
        outcome = lean_tools._classify_repair_outcome(
            {"failure_kind": "lean_unsolved_goals", "diagnostics": {"first_error": "unsolved goals"}},
            {"status": "lean_passed"},
        )
        self.assertEqual(outcome, "improved")

    def test_rejected_repair_is_regressed(self) -> None:
        outcome = lean_tools._classify_repair_outcome(
            {"failure_kind": "lean_unsolved_goals", "diagnostics": {"first_error": "unsolved goals"}},
            {"status": "rejected_forbidden_placeholder"},
        )
        self.assertEqual(outcome, "regressed")

    def test_new_parse_error_is_regressed(self) -> None:
        outcome = lean_tools._classify_repair_outcome(
            {"failure_kind": "lean_unsolved_goals", "diagnostics": {"first_error": "unsolved goals"}},
            {"status": "lean_failed", "failure_kind": "lean_parse_error", "diagnostics": {"first_error": "unexpected token"}},
        )
        self.assertEqual(outcome, "regressed")

    def test_same_signature_is_no_change(self) -> None:
        outcome = lean_tools._classify_repair_outcome(
            {"failure_kind": "lean_unsolved_goals", "diagnostics": {"first_error": "unsolved goals"}},
            {"status": "lean_failed", "failure_kind": "lean_unsolved_goals", "diagnostics": {"first_error": "unsolved goals"}},
        )
        self.assertEqual(outcome, "no_change")


class StrictLoopTests(unittest.TestCase):
    def _run(self, workspace: Path, fake_chat, fake_run, *, max_tool_calls: int = 8, repair_attempts: int = 2):
        proof_rel = "Benchmark/Generated/Sample.lean"
        proof_path = workspace / proof_rel
        proof_path.parent.mkdir(parents=True, exist_ok=True)
        proof_path.write_text(ORIGINAL, encoding="utf-8")
        task = _task(proof_rel, workspace)
        with ExitStack() as stack:
            _strict_env(stack, repair_attempts=repair_attempts)
            stack.enter_context(mock.patch.object(lean_tools, "chat_completion", fake_chat))
            stack.enter_context(mock.patch.object(lean_tools, "_run_lean_module", fake_run))
            return lean_tools._attempt_task_fair(
                task,
                workspace,
                base_url="http://provider.test/v1",
                max_attempts=5,
                max_tool_calls=max_tool_calls,
                attempts_dir=workspace / "attempts",
                tool_log_path=workspace / "tool-calls.jsonl",
                conversation_log_path=workspace / "conversation.jsonl",
                draft_log_path=workspace / "draft.jsonl",
            )

    def test_strict_system_prompt_forbids_driver_edits(self) -> None:
        captured: list[list[dict[str, object]]] = []

        def fake_chat(messages, **kwargs):
            captured.append([dict(m) for m in messages])
            # Immediately submit a passing proof so the run ends quickly.
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {"id": "c1", "function": {"name": "check_proof", "arguments": json.dumps({"proof": "trivial"})}}
                            ],
                        }
                    }
                ]
            }

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""))
        self.assertEqual(result["status"], "lean_passed")
        system = captured[0][0]["content"]
        self.assertIn("STRICT ROLE SEPARATION", system)
        self.assertIn("must never write or edit Lean proof", system)

    def test_failed_check_routes_repair_to_prover_and_records_metrics(self) -> None:
        # Driver: writes then repairs via the prover. Prover: first draft is a
        # failing `simp`, repair draft is `trivial`. Lean passes only on trivial.
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            model = str(kwargs.get("model"))
            if model == "prover-model":
                # Detect repair vs write by the system prompt in messages[0].
                is_repair = "repairer" in str(messages[0].get("content"))
                body = "trivial" if is_repair else "simp"
                return {"choices": [{"message": {"role": "assistant", "content": body}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                args = {"task_context": "prove transfer", "goal": "⊢ True"}
                name = "draft_proof"
            elif n == 2:
                args = {"proof": "simp"}
                name = "check_proof"
            elif n == 3:
                args = {"task_context": "prove transfer", "mode": "repair"}
                name = "draft_proof"
            else:
                args = {"proof": "trivial"}
                name = "check_proof"
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {"id": f"c{n}", "function": {"name": name, "arguments": json.dumps(args)}}
                            ],
                        }
                    }
                ]
            }

        def fake_run(workspace_arg, module, file_rel):
            text = (workspace_arg / file_rel).read_text(encoding="utf-8")
            return (0, "") if "trivial" in text else (1, "error: unsolved goals\n⊢ True")

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, fake_run)

        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["prover_writer_calls"], 1)
        self.assertEqual(metrics["prover_repair_calls"], 1)
        self.assertEqual(metrics["repair_improved"], 1)
        self.assertEqual(metrics["repair_regressed"], 0)
        self.assertEqual(metrics["role_config"]["role_label"], result["role_metrics"]["role_config"]["role_label"])

    def test_prover_repair_budget_is_enforced(self) -> None:
        # Every proof fails; the driver keeps asking for repairs. Only
        # PROVER_REPAIR_ATTEMPTS repair drafts may reach the prover.
        def fake_chat(messages, **kwargs):
            model = str(kwargs.get("model"))
            if model == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "simp"}}]}
            # Driver: alternate check_proof (fails) then draft_proof repair forever.
            # Use the transcript length to decide the next action deterministically.
            has_pending_fail = any(
                m.get("role") == "tool" and "lean_failed" in str(m.get("content")) for m in messages
            )
            if has_pending_fail:
                name, args = "draft_proof", {"task_context": "x", "mode": "repair"}
            else:
                name, args = "check_proof", {"proof": "simp"}
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {"id": "c", "function": {"name": name, "arguments": json.dumps(args)}}
                            ],
                        }
                    }
                ]
            }

        with tempfile.TemporaryDirectory() as tmp:
            draft_log = Path(tmp) / "draft.jsonl"
            self._run(Path(tmp), fake_chat, lambda *a, **k: (1, "error: unsolved goals"), max_tool_calls=12, repair_attempts=1)
            # The budget check returns before ever calling the prover, so the draft
            # audit log holds exactly the prover calls that were made. At most one
            # repair draft may reach the prover, regardless of how many the driver
            # requests.
            entries = [json.loads(line) for line in draft_log.read_text(encoding="utf-8").splitlines()]
        repair_drafts = [e for e in entries if e.get("prompt_kind") == "repair"]
        self.assertLessEqual(len(repair_drafts), 1)

    def test_backward_compat_non_strict_keeps_driver_diagnostic_retry(self) -> None:
        # With strict mode off but draft_proof enabled, a failed check must still
        # trigger the driver-side diagnostic-repair reset (2-message transcript),
        # proving the new code path is gated behind STRICT_ROLE_SEPARATION.
        captured: list[list[dict[str, object]]] = []

        def fake_chat(messages, **kwargs):
            captured.append([dict(m) for m in messages])
            body = "simp" if len(captured) == 1 else "trivial"
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {"id": f"c{len(captured)}", "function": {"name": "check_proof", "arguments": json.dumps({"proof": body})}}
                            ],
                        }
                    }
                ]
            }

        def fake_run(workspace_arg, module, file_rel):
            text = (workspace_arg / file_rel).read_text(encoding="utf-8")
            return (0, "") if "trivial" in text else (1, "error: unsolved goals\n⊢ True")

        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            proof_rel = "Benchmark/Generated/Sample.lean"
            proof_path = workspace / proof_rel
            proof_path.parent.mkdir(parents=True, exist_ok=True)
            proof_path.write_text(ORIGINAL, encoding="utf-8")
            task = _task(proof_rel, workspace)
            with ExitStack() as stack:
                stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True))
                stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", False))
                stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"))
                stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"))
                stack.enter_context(mock.patch.object(lean_tools, "chat_completion", fake_chat))
                stack.enter_context(mock.patch.object(lean_tools, "_run_lean_module", fake_run))
                result = lean_tools._attempt_task_fair(
                    task,
                    workspace,
                    base_url="http://provider.test/v1",
                    max_attempts=3,
                    max_tool_calls=6,
                    attempts_dir=workspace / "attempts",
                    tool_log_path=workspace / "tool-calls.jsonl",
                    conversation_log_path=workspace / "conversation.jsonl",
                    draft_log_path=workspace / "draft.jsonl",
                )

        self.assertEqual(result["status"], "lean_passed")
        # Second driver request is the compact 2-message diagnostic-repair reset.
        self.assertEqual([m["role"] for m in captured[1]], ["system", "user"])
        self.assertIn("Repair the existing proof", captured[1][1]["content"])


if __name__ == "__main__":
    unittest.main()
