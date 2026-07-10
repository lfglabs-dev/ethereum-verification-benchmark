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

theorem transfer_public (x : Nat) : x + 0 = x := by simp

end Benchmark.Spec
"""


def _strict_env(stack: ExitStack, *, repair_attempts: int = 2, decl_index: int = 40) -> None:
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True))
    stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", True))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODE", "draft_proof"))
    stack.enter_context(mock.patch.object(lean_tools, "PROVER_REPAIR_ATTEMPTS", repair_attempts))
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_DECL_INDEX_LIMIT", decl_index))


def _draft_only_env(stack: ExitStack) -> None:
    # Draft tool available but role separation OFF: the driver may author and
    # submit its own bodies, so a submission is only prover-derived when it
    # matches the prover's latest draft.
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", True))
    stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", False))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_DRIVER_MODEL", "driver-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODEL", "prover-model"))
    stack.enter_context(mock.patch.object(lean_tools, "DEFAULT_PROVER_MODE", "draft_proof"))


def _standalone_env(stack: ExitStack) -> None:
    # No prover at all: neither strict nor draft. Prover-specific counters must
    # stay zero for driver-authored submissions.
    stack.enter_context(mock.patch.object(lean_tools, "DRAFT_PROOF_ENABLED", False))
    stack.enter_context(mock.patch.object(lean_tools, "STRICT_ROLE_SEPARATION", False))


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


class NormalizeProverDraftTests(unittest.TestCase):
    def test_bare_body_is_unchanged_and_marked_bare(self) -> None:
        result = lean_tools._normalize_prover_draft("simp [transfer_spec]")
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "simp [transfer_spec]")
        self.assertEqual(result["provenance"], "bare")
        self.assertEqual(result["raw"], "simp [transfer_spec]")

    def test_single_markdown_fence_is_unwrapped(self) -> None:
        result = lean_tools._normalize_prover_draft("```lean\nsimp [transfer_spec]\n```")
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "simp [transfer_spec]")
        self.assertEqual(result["provenance"], "code_fence")

    def test_fence_without_language_tag_is_unwrapped(self) -> None:
        result = lean_tools._normalize_prover_draft("```\ntrivial\n```")
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "trivial")
        self.assertEqual(result["provenance"], "code_fence")

    def test_explanatory_prose_around_single_fence_is_dropped(self) -> None:
        raw = "Here is the proof:\n\n```lean\nsimp\n```\n\nThat closes the goal."
        result = lean_tools._normalize_prover_draft(raw)
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "simp")
        self.assertEqual(result["provenance"], "code_fence")
        # Raw output is preserved verbatim for the audit trail.
        self.assertEqual(result["raw"], raw)

    def test_leading_by_is_stripped_from_bare_body(self) -> None:
        result = lean_tools._normalize_prover_draft("by\n  simp\n  ring")
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "simp\n  ring")
        self.assertEqual(result["provenance"], "bare+stripped_leading_by")

    def test_leading_assign_by_is_stripped(self) -> None:
        result = lean_tools._normalize_prover_draft(":= by simp")
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "simp")
        self.assertEqual(result["provenance"], "bare+stripped_leading_by")

    def test_fence_and_leading_by_compose(self) -> None:
        result = lean_tools._normalize_prover_draft("```lean\nby simp\n```")
        self.assertIsNone(result["reject_reason"])
        self.assertEqual(result["body"], "simp")
        self.assertEqual(result["provenance"], "code_fence+stripped_leading_by")

    def test_multiple_fences_are_rejected_as_ambiguous(self) -> None:
        raw = "```lean\nsimp\n```\n```lean\nring\n```"
        result = lean_tools._normalize_prover_draft(raw)
        self.assertEqual(result["reject_reason"], "prover_output_multiple_code_blocks")
        self.assertIsNone(result["body"])

    def test_lean_outside_a_single_fence_is_ambiguous(self) -> None:
        raw = "simp only [foo]\n```lean\nring\n```"
        result = lean_tools._normalize_prover_draft(raw)
        self.assertEqual(result["reject_reason"], "prover_output_ambiguous_multiple_candidates")
        self.assertIsNone(result["body"])

    def test_unbalanced_fence_is_rejected(self) -> None:
        result = lean_tools._normalize_prover_draft("```lean\nsimp")
        self.assertEqual(result["reject_reason"], "prover_output_unbalanced_fence")
        self.assertIsNone(result["body"])

    def test_empty_output_is_rejected(self) -> None:
        result = lean_tools._normalize_prover_draft("   \n  ")
        self.assertEqual(result["reject_reason"], "empty_prover_output")
        self.assertIsNone(result["body"])

    def test_bare_by_with_no_body_is_not_stripped(self) -> None:
        # Nothing follows `by`; leave it so the caller can reject it rather than
        # silently producing an empty body.
        body, stripped = lean_tools._strip_leading_by("by")
        self.assertEqual(body, "by")
        self.assertFalse(stripped)

    def test_reject_draft_reason_still_guards_extracted_body(self) -> None:
        # The structural boundary hands a bare body to the existing content guard;
        # forbidden tokens and theorem statements are still rejected there.
        fenced_sorry = lean_tools._normalize_prover_draft("```lean\nsorry\n```")
        self.assertIsNone(fenced_sorry["reject_reason"])
        self.assertEqual(
            lean_tools._reject_draft_reason(str(fenced_sorry["body"])),
            "prover_output_contains_forbidden_placeholder",
        )


class DraftProverPipelineTests(unittest.TestCase):
    """The normalization is exercised end-to-end through _draft_proof_with_prover."""

    def _draft(self, stack: ExitStack, content: str, args: dict[str, object]) -> dict[str, object]:
        _strict_env(stack)
        stack.enter_context(
            mock.patch.object(
                lean_tools,
                "chat_completion",
                lambda messages, **kwargs: {"choices": [{"message": {"role": "assistant", "content": content}}]},
            )
        )
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            task = _task("Benchmark/Generated/Sample.lean", workspace)
            return lean_tools._draft_proof_with_prover(
                args,
                task=task,
                original=ORIGINAL,
                base_url="http://provider.test/v1",
                draft_log_path=workspace / "draft.jsonl",
                workspace=workspace,
            )

    def test_fenced_prover_output_is_accepted_and_normalized(self) -> None:
        with ExitStack() as stack:
            result = self._draft(stack, "```lean\nsimp [transfer_spec]\n```", {"task_context": "prove it"})
        self.assertTrue(result["ok"])
        self.assertEqual(result["proof"], "simp [transfer_spec]")
        self.assertEqual(result["provenance"], "code_fence")

    def test_multiple_blocks_reject_reaches_result(self) -> None:
        with ExitStack() as stack:
            result = self._draft(stack, "```lean\nsimp\n```\n```lean\nring\n```", {"task_context": "prove it"})
        self.assertFalse(result["ok"])
        self.assertEqual(result["error"], "prover_output_multiple_code_blocks")

    def test_draft_log_records_raw_and_normalized_preview(self) -> None:
        _strict_env_stack = ExitStack()
        with _strict_env_stack as stack:
            _strict_env(stack)
            stack.enter_context(
                mock.patch.object(
                    lean_tools,
                    "chat_completion",
                    lambda messages, **kwargs: {
                        "choices": [{"message": {"role": "assistant", "content": "```lean\ntrivial\n```"}}]
                    },
                )
            )
            with tempfile.TemporaryDirectory() as tmp:
                workspace = Path(tmp)
                task = _task("Benchmark/Generated/Sample.lean", workspace)
                draft_log = workspace / "draft.jsonl"
                lean_tools._draft_proof_with_prover(
                    {"task_context": "prove it"},
                    task=task,
                    original=ORIGINAL,
                    base_url="http://provider.test/v1",
                    draft_log_path=draft_log,
                    workspace=workspace,
                )
                entry = json.loads(draft_log.read_text(encoding="utf-8").splitlines()[0])
        self.assertEqual(entry["provenance"], "code_fence")
        self.assertIn("```", entry["raw_preview"])
        self.assertEqual(entry["proof_preview"], "trivial")
        self.assertEqual(entry["status"], "drafted")


class StrictLoopIntegrationTests(unittest.TestCase):
    def _run(self, workspace: Path, fake_chat, fake_run, *, max_tool_calls: int = 10, repair_attempts: int = 2):
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

    def test_fenced_writer_draft_is_solved_not_falsely_rejected(self) -> None:
        # This is the exact live false-negative: the prover wraps a valid body in
        # a Markdown fence. Before normalization it was rejected pre-Lean; now it
        # is unwrapped, submitted, and passes.
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "```lean\ntrivial\n```"}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove it"}
            else:
                # Driver echoes the normalized body it received from draft_proof.
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
        self.assertEqual(metrics["draft_rejected_count"], 0)
        self.assertEqual(metrics["draft_normalized_count"], 1)
        self.assertEqual(metrics["prover_writer_calls"], 1)
        self.assertEqual(metrics["draft_submitted_count"], 1)
        self.assertEqual(metrics["lean_check_failed_count"], 0)

    def test_lean_failure_metric_and_repair_conversion(self) -> None:
        # Writer draft fails Lean, repair draft passes: differentiated counters
        # must show one submitted+failed draft and one improved repair.
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                is_repair = "repairer" in str(messages[0].get("content"))
                body = "```lean\ntrivial\n```" if is_repair else "```lean\nsimp\n```"
                return {"choices": [{"message": {"role": "assistant", "content": body}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove transfer"}
            elif n == 2:
                name, args = "check_proof", {"proof": "simp"}
            elif n == 3:
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
        metrics = result["role_metrics"]
        self.assertEqual(metrics["draft_normalized_count"], 2)
        self.assertEqual(metrics["draft_submitted_count"], 2)
        self.assertEqual(metrics["lean_check_failed_count"], 1)
        self.assertEqual(metrics["prover_repair_calls"], 1)
        self.assertEqual(metrics["repair_improved"], 1)
        self.assertEqual(metrics["repair_regressed"], 0)

    def test_repair_without_prior_failure_is_blocked(self) -> None:
        # The driver requests a repair before any write draft or Lean failure. The
        # repairer must refuse: there is nothing failed to repair.
        driver_calls = {"n": 0}
        prover_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                prover_calls["n"] += 1
                return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                # Illegal bare repair with no antecedent.
                name, args = "draft_proof", {"mode": "repair"}
            elif n == 2:
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
        self.assertEqual(metrics["repair_blocked_no_failure"], 1)
        # The blocked repair never called the prover in repair mode; only the
        # later write draft did.
        self.assertEqual(prover_calls["n"], 1)
        self.assertEqual(metrics["prover_repair_calls"], 0)

    def test_provenance_guard_still_blocks_driver_authored_submission(self) -> None:
        # Normalization must not weaken the provenance guard: a body the driver
        # invents (never returned by the prover) is still rejected pre-Lean.
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                return {"choices": [{"message": {"role": "assistant", "content": "```lean\ntrivial\n```"}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "check_proof", {"proof": "exact my_own_lemma"}
            elif n == 2:
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
        self.assertEqual(metrics["strict_submission_blocked"], 1)
        # Only the normalized prover body was ever submitted to Lean.
        self.assertEqual(metrics["draft_submitted_count"], 1)


class RepairAntecedentAndBaselineTests(unittest.TestCase):
    """Finding 1: strict repair needs a real Lean failure or a structured
    pre-Lean rejection - never a merely unsubmitted normalized draft - and a
    repair that passes without a measured pre-repair baseline must not be
    counted as ``repair_improved``."""

    def _run(self, workspace: Path, fake_chat, fake_run, *, repair_attempts: int = 2):
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
                max_tool_calls=10,
                attempts_dir=workspace / "attempts",
                tool_log_path=workspace / "tool-calls.jsonl",
                conversation_log_path=workspace / "conversation.jsonl",
                draft_log_path=workspace / "draft.jsonl",
            )

    def test_repair_blocked_when_only_unsubmitted_draft_exists(self) -> None:
        # Writer draft is accepted (latest_draft is set) but never submitted, so
        # nothing failed. A repair request here must be refused: an unsubmitted
        # normalized draft is not a valid antecedent.
        driver_calls = {"n": 0}
        prover_calls = {"write": 0, "repair": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                if "repairer" in str(messages[0].get("content")):
                    prover_calls["repair"] += 1
                else:
                    prover_calls["write"] += 1
                return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove it"}
            elif n == 2:
                # Illegal: repair with only an unsubmitted draft, no Lean failure.
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

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""))

        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["repair_blocked_no_failure"], 1)
        self.assertEqual(metrics["prover_repair_calls"], 0)
        self.assertEqual(prover_calls["repair"], 0)
        # Only the write draft was submitted to Lean and it passed.
        self.assertEqual(metrics["draft_submitted_count"], 1)
        self.assertEqual(metrics["lean_check_failed_count"], 0)

    def test_structured_rejection_repair_forwards_draft_and_reason_no_false_improved(self) -> None:
        # Writer draft is rejected pre-Lean (multiple code blocks). A repair is
        # authorized by that structured rejection: the rejected draft AND the
        # reason must be forwarded to the prover, and a passing repair must NOT
        # count as repair_improved (there is no measured Lean baseline).
        rejected_raw = "```lean\nsimp\n```\n```lean\nring\n```"
        prover_repair_prompts: list[str] = []
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            if str(kwargs.get("model")) == "prover-model":
                is_repair = "repairer" in str(messages[0].get("content"))
                if is_repair:
                    prover_repair_prompts.append("\n".join(str(m.get("content")) for m in messages))
                    return {"choices": [{"message": {"role": "assistant", "content": "trivial"}}]}
                return {"choices": [{"message": {"role": "assistant", "content": rejected_raw}}]}
            driver_calls["n"] += 1
            n = driver_calls["n"]
            if n == 1:
                name, args = "draft_proof", {"task_context": "prove it"}
            elif n == 2:
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

        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(Path(tmp), fake_chat, lambda *a, **k: (0, ""))

        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        # The write draft was rejected pre-Lean; the repair was authorized by the
        # structured reason and never blocked.
        self.assertEqual(metrics["draft_rejected_count"], 1)
        self.assertEqual(metrics["repair_blocked_no_failure"], 0)
        self.assertEqual(metrics["prover_repair_calls"], 1)
        # A pass with no measured pre-repair Lean baseline is NOT repair_improved.
        self.assertEqual(metrics["repair_improved"], 0)
        self.assertEqual(metrics["repair_improved_no_baseline"], 1)
        # The repair prompt forwarded both the rejected draft body and the reason.
        self.assertTrue(prover_repair_prompts)
        joined = prover_repair_prompts[0]
        self.assertIn("ring", joined)
        self.assertIn("prover_output_multiple_code_blocks", joined)


class StandaloneAttributionTests(unittest.TestCase):
    """Finding 2: prover-specific submission counters must never move for
    driver-authored submissions outside strict/draft-prover attribution."""

    def _run(self, env_fn, workspace: Path, fake_chat, fake_run):
        proof_rel = "Benchmark/Generated/Sample.lean"
        proof_path = workspace / proof_rel
        proof_path.parent.mkdir(parents=True, exist_ok=True)
        proof_path.write_text(ORIGINAL, encoding="utf-8")
        task = _task(proof_rel, workspace)
        with ExitStack() as stack:
            env_fn(stack)
            stack.enter_context(mock.patch.object(lean_tools, "chat_completion", fake_chat))
            stack.enter_context(mock.patch.object(lean_tools, "_run_lean_module", fake_run))
            return lean_tools._attempt_task_fair(
                task,
                workspace,
                base_url="http://provider.test/v1",
                max_attempts=5,
                max_tool_calls=10,
                attempts_dir=workspace / "attempts",
                tool_log_path=workspace / "tool-calls.jsonl",
                conversation_log_path=workspace / "conversation.jsonl",
                draft_log_path=workspace / "draft.jsonl",
            )

    def _driver_two_submissions(self):
        driver_calls = {"n": 0}

        def fake_chat(messages, **kwargs):
            driver_calls["n"] += 1
            n = driver_calls["n"]
            # First submission fails Lean, second passes - both driver-authored.
            args = {"proof": "simp"} if n == 1 else {"proof": "trivial"}
            return {
                "choices": [
                    {
                        "message": {
                            "role": "assistant",
                            "content": None,
                            "tool_calls": [
                                {"id": f"c{n}", "function": {"name": "check_proof", "arguments": json.dumps(args)}}
                            ],
                        }
                    }
                ]
            }

        return fake_chat

    def _fake_run(self, workspace_arg, module, file_rel):
        text = (workspace_arg / file_rel).read_text(encoding="utf-8")
        return (0, "") if "trivial" in text else (1, "error: unsolved goals\n⊢ True")

    def test_standalone_mode_never_attributes_prover_submission_counters(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(_standalone_env, Path(tmp), self._driver_two_submissions(), self._fake_run)
        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        # Two driver submissions reached Lean (one failed), but there is no prover,
        # so prover-specific counters must be zero.
        self.assertEqual(metrics["draft_submitted_count"], 0)
        self.assertEqual(metrics["lean_check_failed_count"], 0)

    def test_draft_mode_driver_authored_submission_is_not_prover_derived(self) -> None:
        # Draft tool available but the driver never called it; it submits its own
        # bodies. Those are not prover-derived, so counters stay zero.
        with tempfile.TemporaryDirectory() as tmp:
            result = self._run(_draft_only_env, Path(tmp), self._driver_two_submissions(), self._fake_run)
        self.assertEqual(result["status"], "lean_passed")
        metrics = result["role_metrics"]
        self.assertEqual(metrics["draft_submitted_count"], 0)
        self.assertEqual(metrics["lean_check_failed_count"], 0)


if __name__ == "__main__":
    unittest.main()
