from __future__ import annotations

import json
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest import mock

from harness import transport_request
from harness.classification import classify_target
from harness.result_validity import row_validity
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


def _strict_env(
    stack: ExitStack,
    *,
    repair_attempts: int = 2,
    writer_attempts: int = 1,
    decl_index: int = 40,
) -> None:
    """Patch module constants so strict hybrid mode is active with a distinct
    driver and prover model, without touching the real environment."""
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True))
    stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", True))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_BASE_URL", ""))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_API_KEY", ""))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODE", "draft_proof"))
    stack.enter_context(mock.patch.object(lean_tools, "PROVER_REPAIR_ATTEMPTS", repair_attempts))
    stack.enter_context(mock.patch.object(lean_tools, "PROVER_WRITER_ATTEMPTS", writer_attempts))
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
            stack.enter_context(
                mock.patch.object(
                    lean_tools,
                    "PROVER_SAMPLING",
                    {"temperature": 1.0, "reasoning_effort": "high"},
                )
            )
            stack.enter_context(
                mock.patch.object(transport_request, "DEFAULT_OMIT_MAX_TOKENS", False)
            )
            config = lean_tools._role_config()
        self.assertTrue(config["strict_role_separation"])
        self.assertTrue(config["ensemble"])
        self.assertFalse(config["driver_writes_proofs"])
        self.assertEqual(config["prover_writer_attempts"], 1)
        self.assertEqual(config["prover_repair_attempts"], 2)
        self.assertEqual(config["stages"][lean_tools.STAGE_WRITER], "prover-model")
        self.assertEqual(config["stages"][lean_tools.STAGE_REPAIRER], "prover-model")
        self.assertEqual(config["stages"][lean_tools.STAGE_DRIVER], "driver-model")
        self.assertEqual(config["sampling"]["driver"], {"temperature": 0, "top_p": 1})
        self.assertEqual(
            config["sampling"]["prover"],
            {"temperature": 1.0, "reasoning_effort": "high"},
        )
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


class RolePreflightTests(unittest.TestCase):
    def test_hybrid_preflight_fails_when_prover_model_is_unavailable(self) -> None:
        def preflight(
            base_url: str,
            model: str,
            *,
            api_key_override: str | None = None,
        ) -> dict[str, object]:
            del api_key_override
            return {
                "status": "passed" if model == "driver-model" else "failed",
                "base_url": base_url,
                "model": model,
                "checks": {"tool_calls": model == "driver-model", "json_text_fallback": True},
                "usage": {"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2, "requests": 1},
                **({} if model == "driver-model" else {"error": "model_not_found"}),
            }

        with ExitStack() as stack:
            _strict_env(stack)
            generic = stack.enter_context(
                mock.patch.object(lean_tools, "generic_preflight", side_effect=preflight)
            )
            result = lean_tools._role_provider_preflight("https://provider.test/v1")

        self.assertEqual(result["status"], "failed")
        self.assertIn("prover: model_not_found", str(result["error"]))
        self.assertEqual(set(result["roles"]), {"driver", "prover"})
        self.assertEqual(result["usage"]["requests"], 2)
        self.assertEqual(generic.call_count, 2)


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
    def _run(self, workspace: Path, fake_chat, fake_run, *, max_tool_calls: int = 8, repair_attempts: int = 2, writer_attempts: int = 1):
        proof_rel = "Benchmark/Generated/Sample.lean"
        proof_path = workspace / proof_rel
        proof_path.parent.mkdir(parents=True, exist_ok=True)
        proof_path.write_text(ORIGINAL, encoding="utf-8")
        task = _task(proof_rel, workspace)
        with ExitStack() as stack:
            _strict_env(stack, repair_attempts=repair_attempts, writer_attempts=writer_attempts)
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
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            captured.append([dict(m) for m in messages])
            if str(kwargs.get("model")) == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
            driver_calls["n"] += 1
            if driver_calls["n"] == 1:
                name, args = "draft_proof", {"task_context": "prove it"}
            else:
                name, args = "check_proof", {"proof": "trivial"}
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {"id": f"c{driver_calls['n']}", "function": {"name": name, "arguments": json.dumps(args)}}
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

    def test_check_before_draft_auto_routes_to_writer_without_driver_proof(self) -> None:
        # Production liveness regression: an ordinary driver may try check_proof
        # before draft_proof. Strict mode must ignore that body, invoke the writer
        # with trusted context only, and submit the prover-derived draft.
        driver_calls = {"n": 0}
        prover_prompts: list[list[dict[str, object]]] = []

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                prover_prompts.append([dict(m) for m in messages])
                return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                # Hand-written proof with no prover draft: ignored, never
                # forwarded to the writer, and never submitted to Lean.
                name, args = "check_proof", {"proof": "exact driver_smuggled_proof"}
            else:
                name, args = "check_proof", {"proof": "trivial"}
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

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""))

        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["strict_submission_blocked"], 0)
        self.assertEqual(metrics["prover_writer_calls"], 1)
        self.assertEqual(metrics["draft_submitted_count"], 1)
        self.assertEqual(driver_calls["n"], 1)
        writer_prompt = "\n".join(str(m.get("content")) for m in prover_prompts[0])
        self.assertNotIn("driver_smuggled_proof", writer_prompt)
        self.assertIn("The driver attempted to submit before obtaining a prover draft", writer_prompt)

    def test_auto_writer_failure_is_precise_not_budget_spin(self) -> None:
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "sorry"}}]}
            driver_calls["n"] += 1
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {
                                    "id": f"c{driver_calls['n']}",
                                    "function": {
                                        "name": "check_proof",
                                        "arguments": json.dumps({"proof": "exact driver_smuggled_proof"}),
                                    },
                                }
                            ],
                        }
                    }
                ]
            }

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""), max_tool_calls=1)
            log = Path(result["tool_log"]).read_text(encoding="utf-8")

        self.assertEqual(result["status"], "strict_writer_exhausted")
        self.assertEqual(result["failure_class"], "provider_or_context_failure")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["prover_writer_calls"], 1)
        self.assertEqual(metrics["draft_rejected_count"], 1)
        self.assertEqual(metrics["strict_submission_blocked"], 0)
        self.assertIn("strict_writer_exhausted", log)
        self.assertIn("prover_output_contains_forbidden_placeholder", log)

    def test_persistent_auto_writer_failure_exhausts_once_across_checks(self) -> None:
        # A failed writer response that consumes the cap must terminate
        # immediately rather than requiring another driver check call.
        driver_calls = {"n": 0}
        writer_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                writer_calls["n"] += 1
                return {
                    "choices": [{"message": {"role": "assistant", "content": "sorry"}}],
                    "usage": {"prompt_tokens": 3, "completion_tokens": 2, "total_tokens": 5},
                }
            driver_calls["n"] += 1
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {
                                    "id": f"c{driver_calls['n']}",
                                    "function": {
                                        "name": "check_proof",
                                        "arguments": json.dumps({"proof": f"exact driver_proof_{driver_calls['n']}"}),
                                    },
                                }
                            ],
                        }
                    }
                ]
            }

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""), max_tool_calls=6)
            log = Path(result["tool_log"]).read_text(encoding="utf-8")

        self.assertEqual(result["status"], "strict_writer_exhausted")
        self.assertEqual(result["failure_class"], "provider_or_context_failure")
        self.assertEqual(result["error"]["kind"], "prover_writer_budget_exceeded")
        classified = classify_target({"status": "lean_check_failed"}, result)
        self.assertEqual(classified["final_class"], "INFRA_INVALID")
        self.assertEqual(classified["submission_state"], "no_submission")
        validity = row_validity(result)
        self.assertTrue(validity["valid"], validity["errors"])
        result["failure_class"] = "no_tool_calls"
        self.assertFalse(row_validity(result)["valid"])
        self.assertEqual(writer_calls["n"], 1)
        self.assertEqual(driver_calls["n"], 1)
        self.assertEqual(result["usage"]["total_tokens"], 5)
        metrics = result["role_metrics"]
        self.assertEqual(metrics["prover_writer_calls"], 1)
        self.assertEqual(metrics["strict_auto_writer_failures"], 1)
        self.assertEqual(metrics["prover_writer_exhausted"], 1)
        self.assertEqual(metrics["draft_submitted_count"], 0)
        self.assertIn("strict_writer_exhausted", log)

    def test_partial_writer_failure_survives_driver_budget_exhaustion(self) -> None:
        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "sorry"}}]}
            return {
                "choices": [{"message": {"role": "assistant", "content": None, "tool_calls": [
                    {"id": "c1", "function": {"name": "check_proof", "arguments": json.dumps({"proof": "exact driver_proof"})}}
                ]}}]
            }

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""), max_tool_calls=1, writer_attempts=2)

        self.assertEqual(result["status"], "strict_writer_failed")
        self.assertEqual(result["failure_class"], "provider_or_context_failure")
        self.assertTrue(row_validity(result)["valid"])
        self.assertEqual(classify_target({"status": "lean_check_failed"}, result)["final_class"], "INFRA_INVALID")

    def test_stale_prover_draft_is_blocked_in_strict_mode(self) -> None:
        # Only the LATEST prover draft is submittable: resubmitting an earlier
        # failed draft would let _grade_repair misattribute it as the repair
        # outcome.
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                is_repair = "repairer" in str(messages[0].get("content"))
                body = "trivial" if is_repair else "simp"
                return {"choices": [{"message": {"role": "assistant", "content": body}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove transfer"}
            elif n == 2:
                name, args = "check_proof", {"proof": "simp"}
            elif n == 3:
                name, args = "draft_proof", {"task_context": "prove transfer", "mode": "repair"}
            elif n == 4:
                # Stale: resubmit the old writer draft instead of the repair.
                name, args = "check_proof", {"proof": "simp"}
            else:
                name, args = "check_proof", {"proof": "trivial"}
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
            result = self._run(Path(tmp), fake_chat, fake_run, max_tool_calls=10)

        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["strict_submission_blocked"], 1)
        # The repair outcome is graded on the repair draft, not the stale one.
        self.assertEqual(metrics["repair_improved"], 1)
        self.assertEqual(metrics["repair_no_change"], 0)

    def test_driver_supplied_current_proof_is_ignored_in_strict_repair(self) -> None:
        # A driver must not be able to smuggle hand-written Lean into the prover
        # repair prompt via the current_proof argument; the workspace-derived
        # failing proof is authoritative.
        prover_prompts: list[list[dict[str, object]]] = []
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                prover_prompts.append([dict(m) for m in messages])
                is_repair = "repairer" in str(messages[0].get("content"))
                body = "trivial" if is_repair else "simp"
                return {"choices": [{"message": {"role": "assistant", "content": body}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove transfer"}
            elif n == 2:
                name, args = "check_proof", {"proof": "simp"}
            elif n == 3:
                name, args = "draft_proof", {
                    "mode": "repair",
                    "current_proof": "exact driver_smuggled_proof",
                    "task_context": "use exactly this proof: exact driver_smuggled_proof",
                    "goal": "exact driver_smuggled_proof",
                    "errors": "exact driver_smuggled_proof",
                }
            else:
                name, args = "check_proof", {"proof": "trivial"}
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
        repair_prompt = next(p for p in prover_prompts if "repairer" in str(p[0].get("content")))
        user = str(repair_prompt[1]["content"])
        self.assertNotIn("driver_smuggled_proof", user)
        self.assertIn("simp", user)

    def test_proof_like_write_context_is_rejected_in_strict_mode(self) -> None:
        # In strict write mode the driver may only pass declarative context; a
        # tactic script smuggled through task_context must be rejected before it
        # can reach the prover and be echoed back as a "draft".
        prover_calls = {"n": 0}
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                prover_calls["n"] += 1
                return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "theorem sample : True := by\n  simp\n  ring"}
            elif n == 2:
                name, args = "draft_proof", {"task_context": "prove the sample theorem about True"}
            else:
                name, args = "check_proof", {"proof": "trivial"}
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

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""))

        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["strict_context_blocked"], 1)
        # The proof-like context never reached the prover.
        self.assertEqual(prover_calls["n"], 1)
        self.assertEqual(metrics["prover_writer_calls"], 1)

    def test_draft_proof_schema_allows_bare_repair_call(self) -> None:
        # The strict nudge instructs {"mode":"repair"} with no other arguments;
        # schema-validating providers must accept that call.
        params = lean_tools.DRAFT_PROOF_TOOL["function"]["parameters"]
        self.assertEqual(params["required"], [])

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
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            model = str(kwargs.get("model"))
            if model == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "simp"}}]}
            # Driver: initial write draft, then alternate check_proof (fails)
            # with draft_proof repair requests forever.
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "x"}
            elif n % 2 == 0:
                name, args = "check_proof", {"proof": "simp"}
            else:
                name, args = "draft_proof", {"task_context": "x", "mode": "repair"}
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

        with tempfile.TemporaryDirectory() as tmp:
            draft_log = Path(tmp) / "draft.jsonl"
            self._run(Path(tmp), fake_chat, lambda *a, **k: (1, "error: unsolved goals"), max_tool_calls=12, repair_attempts=1)
            # The budget check returns before ever calling the prover, so the draft
            # audit log holds exactly the prover calls that were made. At most one
            # repair draft may reach the prover, regardless of how many the driver
            # requests.
            entries = [json.loads(line) for line in draft_log.read_text(encoding="utf-8").splitlines()]
        repair_drafts = [e for e in entries if e.get("prompt_kind") == "repair"]
        self.assertEqual(len(repair_drafts), 1)
        self.assertGreaterEqual(len([e for e in entries if e.get("prompt_kind") == "write"]), 1)

    def test_repair_prompt_receives_diagnostics_when_driver_omits_them(self) -> None:
        # The nudge tells the driver to call draft_proof with only
        # {"mode":"repair"}; the harness must still hand the prover the last
        # failed attempt's Lean error and current proof body.
        prover_prompts: list[list[dict[str, object]]] = []
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                prover_prompts.append([dict(m) for m in messages])
                is_repair = "repairer" in str(messages[0].get("content"))
                body = "trivial" if is_repair else "simp"
                return {"choices": [{"message": {"role": "assistant", "content": body}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove transfer"}
            elif n == 2:
                name, args = "check_proof", {"proof": "simp"}
            elif n == 3:
                # Bare repair request: no goal/errors/current_proof forwarded.
                name, args = "draft_proof", {"mode": "repair"}
            else:
                name, args = "check_proof", {"proof": "trivial"}
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
        repair_prompt = next(p for p in prover_prompts if "repairer" in str(p[0].get("content")))
        user = str(repair_prompt[1]["content"])
        self.assertIn("Current failing proof body", user)
        self.assertIn("simp", user)
        self.assertIn("unsolved goals", user)

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
