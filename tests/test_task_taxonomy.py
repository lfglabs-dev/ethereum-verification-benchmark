"""Tests for the task-taxonomy / failure-clustering layer (issue #93).

Three groups:
  * ClassifierTests          -- scripts/classify_failures.py over analysis/failure_modes.json
  * ExtractorTests           -- the pure helpers in scripts/extract_task_features.py
  * DecouplingInvariantTests -- the taxonomy layer never feeds result_key / reruns, and the
                                seed labels are current against the version they reviewed.

The classifier/extractor tests use small hand-built fixtures so they do not depend on the
large generated artifacts. The decoupling/seed tests read the real committed files, since
their whole point is to assert a property of the real data.
"""
from __future__ import annotations

import copy
import inspect
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import classify_failures as cf
import extract_task_features as ef
from plan_rerun import plan_rerun, result_key


class ClassifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.taxonomy = cf.load_taxonomy()

    def classify(self, status, output, *, harness_status=None) -> cf.Classification:
        return cf.classify(status, output, taxonomy=self.taxonomy, harness_status=harness_status)

    def test_passed_is_a_pass_with_no_lean_mode(self) -> None:
        result = self.classify("passed", "")
        self.assertEqual(result.outcome, "passed")
        self.assertTrue(result.is_pass)
        self.assertIsNone(result.lean_failure_mode)

    def test_unsolved_goals_is_the_soft_terminal_mode(self) -> None:
        result = self.classify("lean_check_failed", "error: unsolved goals\n⊢ a = b")
        self.assertEqual(result.outcome, "lean_check_failed")
        self.assertFalse(result.is_pass)
        self.assertEqual(result.lean_failure_mode, "unsolved_goals")

    def test_priority_sorry_beats_unsolved_goals(self) -> None:
        # Both signatures present; the more specific 'sorry_used' must win (listed first).
        output = "declaration uses 'sorry'\nunsolved goals"
        result = self.classify("lean_check_failed", output)
        self.assertEqual(result.lean_failure_mode, "sorry_used")

    def test_tactic_failed_captures_tactic_name_either_ordering(self) -> None:
        forward = self.classify("lean_check_failed", "tactic 'simp' failed, nested error")
        self.assertEqual(forward.lean_failure_mode, "tactic_failed")
        self.assertEqual(forward.detail, "simp")
        reversed_order = self.classify("lean_check_failed", "'show' tactic failed")
        self.assertEqual(reversed_order.lean_failure_mode, "tactic_failed")
        self.assertEqual(reversed_order.detail, "show")

    def test_decision_procedure_captures_grind(self) -> None:
        result = self.classify("lean_check_failed", "`grind` failed to close the goal")
        self.assertEqual(result.lean_failure_mode, "decision_procedure_failed")
        self.assertEqual(result.detail, "grind")

    def test_heartbeat_timeout_is_distinct_from_outcome_timeout(self) -> None:
        # A per-declaration heartbeat exhaustion is reported by the verifier as a failed
        # Lean check, NOT as the outcome-level wall-clock timeout.
        result = self.classify(
            "lean_check_failed",
            "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
        )
        self.assertEqual(result.outcome, "lean_check_failed")
        self.assertEqual(result.lean_failure_mode, "heartbeat_timeout")

    def test_outcome_level_timeout_has_no_lean_mode(self) -> None:
        result = self.classify("timeout", "")
        self.assertEqual(result.outcome, "timeout")
        self.assertFalse(result.is_pass)
        self.assertIsNone(result.lean_failure_mode)

    def test_unknown_identifier_captures_name(self) -> None:
        result = self.classify("lean_check_failed", "unknown identifier 'Foo.bar'")
        self.assertEqual(result.lean_failure_mode, "unknown_identifier")
        self.assertEqual(result.detail, "Foo.bar")

    def test_unmatched_lean_error_falls_back(self) -> None:
        result = self.classify("lean_check_failed", "some entirely novel lean diagnostic")
        self.assertEqual(result.lean_failure_mode, "other_lean_error")

    def test_incomplete_harness_overrides_any_status(self) -> None:
        # Even a 'passed' verifier verdict is untrustworthy if the harness did not complete.
        result = self.classify("passed", "", harness_status="errored")
        self.assertEqual(result.outcome, "harness_error")
        self.assertFalse(result.is_pass)

    def test_completed_with_failures_is_a_trusted_run(self) -> None:
        # The harness emits 'completed_with_failures' when the run finishes but some targets
        # fail. That is a genuine model failure to classify, not an infrastructure error.
        result = self.classify(
            "lean_check_failed", "unsolved goals", harness_status="completed_with_failures"
        )
        self.assertEqual(result.outcome, "lean_check_failed")
        self.assertEqual(result.lean_failure_mode, "unsolved_goals")
        passed = self.classify("passed", "", harness_status="completed_with_failures")
        self.assertEqual(passed.outcome, "passed")
        self.assertTrue(passed.is_pass)

    def test_legacy_passed_status_is_case_insensitive(self) -> None:
        artifact = {
            "harness_status": "completed",
            "evaluation": {"status": "Passed", "failure_mode": "lean_check_failed", "details": ""},
        }
        row = next(cf.iter_run_targets(artifact))
        self.assertEqual(row["status"], "passed")
        self.assertTrue(self.classify(row["status"], row["output"]).is_pass)

    def test_theorem_missing_outcome(self) -> None:
        result = self.classify("theorem_missing", "")
        self.assertEqual(result.outcome, "theorem_missing")
        self.assertFalse(result.is_pass)

    def test_empty_status_is_no_submission(self) -> None:
        self.assertEqual(self.classify("", "").outcome, "no_submission")
        self.assertEqual(self.classify(None, "").outcome, "no_submission")

    def test_unknown_status_surfaces_as_harness_error(self) -> None:
        # An unmapped non-empty status must not be silently treated as a Lean failure.
        result = self.classify("totally-unknown-status", "")
        self.assertEqual(result.outcome, "harness_error")
        self.assertFalse(result.is_pass)

    def test_iter_run_targets_handles_canonical_and_legacy_shapes(self) -> None:
        canonical = {
            "model": "m",
            "harness_status": "completed",
            "verifier": {"targets": [{"task_ref": "a/b/c", "status": "passed", "output": ""}]},
        }
        legacy = {
            "task_ref": "a/b/c",
            "harness_status": "completed",
            "evaluation": {"status": "failed", "failure_mode": "lean_check_failed", "details": "unsolved goals"},
        }
        canon_rows = list(cf.iter_run_targets(canonical))
        legacy_rows = list(cf.iter_run_targets(legacy))
        self.assertEqual(canon_rows[0]["status"], "passed")
        self.assertEqual(legacy_rows[0]["status"], "lean_check_failed")
        self.assertEqual(legacy_rows[0]["output"], "unsolved goals")


class ExtractorTests(unittest.TestCase):
    def test_valid_attempt_requires_completed_harness_and_output(self) -> None:
        ok = {"harness_status": "completed", "verifier_output_present": True}
        blank_harness = {"harness_status": "", "verifier_output_present": True}
        errored = {"harness_status": "errored", "verifier_output_present": True}
        no_output = {"harness_status": "completed", "verifier_output_present": False}
        completed_with_failures = {"harness_status": "completed_with_failures", "verifier_output_present": True}
        self.assertTrue(ef.is_valid_attempt(ok))
        self.assertTrue(ef.is_valid_attempt(blank_harness))
        self.assertTrue(ef.is_valid_attempt(completed_with_failures))
        self.assertFalse(ef.is_valid_attempt(errored))
        self.assertFalse(ef.is_valid_attempt(no_output))

    def test_select_cohort_respects_min_coverage(self) -> None:
        task_refs = {"t1", "t2", "t3", "t4"}
        attempts = {
            "full": {ref: {} for ref in task_refs},
            "three_quarters": {"t1": {}, "t2": {}, "t3": {}},
            "weak": {"t1": {}},
        }
        self.assertEqual(ef.select_cohort(attempts, task_refs, min_coverage=1.0), ["full"])
        self.assertEqual(
            ef.select_cohort(attempts, task_refs, min_coverage=0.75),
            ["full", "three_quarters"],
        )

    def test_divisiveness_is_zero_when_unanimous_and_one_when_split(self) -> None:
        self.assertEqual(ef.divisiveness(0.0), 0.0)
        self.assertEqual(ef.divisiveness(1.0), 0.0)
        self.assertEqual(ef.divisiveness(0.5), 1.0)
        self.assertEqual(ef.divisiveness(0.25), 0.5)

    def test_usage_total_tokens_prefers_total_then_falls_back(self) -> None:
        self.assertEqual(ef.usage_total_tokens({"usage": {"total_tokens": 120}}), 120)
        self.assertEqual(
            ef.usage_total_tokens({"usage": {"prompt_tokens": 100, "completion_tokens": 20}}),
            120,
        )
        self.assertEqual(ef.usage_total_tokens({}), 0)

    def test_build_features_aggregates_pass_rate_cohort_and_failure_modes(self) -> None:
        version = {
            "benchmark_version": "0.1",
            "tasks": [
                {
                    "task_ref": "fam/case/thm",
                    "task_fingerprint": "sha256:fp",
                    "task_interface_id": "sha256:iface",
                    "proof_family": "functional_correctness",
                    "property_class": "x",
                    "difficulty": "easy",
                }
            ],
        }
        results = {
            "models": [
                {
                    "model_id": "passer",
                    "task_results": [self._row("fam/case/thm", passed=True, tokens=100)],
                },
                {
                    "model_id": "failer",
                    "task_results": [self._row("fam/case/thm", passed=False, tokens=300)],
                },
            ]
        }
        enrichment = {
            ("failer", "fam/case/thm"): {
                "outcome": "lean_check_failed",
                "is_pass": False,
                "lean_failure_mode": "unsolved_goals",
                "detail": None,
            }
        }
        features = ef.build_features(version, results, enrichment=enrichment, min_coverage=1.0)
        task = features["tasks"][0]
        self.assertEqual(task["attempts"], 2)
        self.assertEqual(task["passes"], 1)
        self.assertEqual(task["pass_rate"], 0.5)
        self.assertEqual(task["cohort_pass_rate"], 0.5)
        self.assertEqual(task["divisiveness"], 1.0)
        self.assertEqual(task["failure_modes"], {"unsolved_goals": 1})
        self.assertEqual(sorted(features["cohort"]), ["failer", "passer"])

    def test_build_features_counts_non_lean_outcome_as_failure_mode(self) -> None:
        # A failing attempt whose outcome is not lean_check_failed (e.g. theorem_missing)
        # is still attributed to a failure-mode bucket using its outcome id.
        version = {
            "benchmark_version": "0.1",
            "tasks": [{"task_ref": "fam/case/thm", "task_fingerprint": "fp", "task_interface_id": "i"}],
        }
        results = {
            "models": [
                {"model_id": "m", "task_results": [self._row("fam/case/thm", passed=False, tokens=10)]}
            ]
        }
        enrichment = {
            ("m", "fam/case/thm"): {
                "outcome": "theorem_missing",
                "is_pass": False,
                "lean_failure_mode": None,
                "detail": None,
            }
        }
        features = ef.build_features(version, results, enrichment=enrichment, min_coverage=1.0)
        self.assertEqual(features["tasks"][0]["failure_modes"], {"theorem_missing": 1})

    @staticmethod
    def _row(task_ref: str, *, passed: bool, tokens: int) -> dict:
        return {
            "task_ref": task_ref,
            "passed": passed,
            "harness_status": "completed",
            "verifier_output_present": True,
            "usage": {"total_tokens": tokens, "requests": 1},
        }


class DecouplingInvariantTests(unittest.TestCase):
    """The taxonomy layer must never influence result_key or rerun decisions."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.version = json.loads((ROOT / "benchmark-versions" / "v0.1.json").read_text(encoding="utf-8"))
        cls.results = json.loads((ROOT / "results" / "manifests" / "v0.1.json").read_text(encoding="utf-8"))
        cls.taxonomy = json.loads((ROOT / "analysis" / "task_taxonomy.json").read_text(encoding="utf-8"))
        cls.version_fps = {t["task_ref"]: t.get("task_fingerprint") for t in cls.version["tasks"]}

    def test_result_key_inputs_exclude_taxonomy_concepts(self) -> None:
        params = set(inspect.signature(result_key).parameters)
        for forbidden in ("skill", "skills", "label", "labels", "taxonomy", "failure_mode", "observed"):
            self.assertNotIn(forbidden, params, f"result_key must not depend on {forbidden!r}")

    def test_rerun_plan_is_invariant_to_taxonomy_content(self) -> None:
        # A label edit must not change which tasks rerun. We model "editing the taxonomy"
        # and assert the plan over the unchanged version is byte-identical.
        model = "kimi/kimi-for-coding"
        baseline = plan_rerun(self.version, self.version, model=model, results_manifest=self.results)
        # Mutating the in-memory taxonomy (simulating a relabel) touches nothing plan_rerun reads.
        mutated_taxonomy = copy.deepcopy(self.taxonomy)
        for label in mutated_taxonomy["labels"]:
            label["skills"] = ["arithmetic_reasoning"]
            label["difficulty"] = "synthetic"
        after = plan_rerun(self.version, self.version, model=model, results_manifest=self.results)
        self.assertEqual(baseline, after)
        self.assertEqual(baseline["rerun_count"], 0)

    def test_seed_labels_reference_real_tasks(self) -> None:
        for label in self.taxonomy["labels"]:
            self.assertIn(label["task_ref"], self.version_fps, label["task_ref"])

    def test_seed_label_fingerprints_are_current(self) -> None:
        # Acceptance (d): seed labels were reviewed against this version; their recorded
        # fingerprints must still match, so the staleness check reports them as current.
        for label in self.taxonomy["labels"]:
            self.assertEqual(
                label["task_fingerprint"],
                self.version_fps[label["task_ref"]],
                f"label for {label['task_ref']} is stale against v0.1",
            )

    def test_seed_label_skills_are_in_the_controlled_vocabulary(self) -> None:
        vocab = {s["id"] for s in self.taxonomy["skill_vocabulary"]}
        for label in self.taxonomy["labels"]:
            for skill in label["skills"]:
                self.assertIn(skill, vocab, f"{skill!r} not in skill_vocabulary")

    def test_drifted_fingerprint_flags_relabel_without_blocking_reuse(self) -> None:
        # If a task's fingerprint drifts, the label is flagged stale (re-review) but the
        # result layer is governed solely by version fingerprints, not the taxonomy.
        label = self.taxonomy["labels"][0]
        task_ref = label["task_ref"]
        drifted = copy.deepcopy(self.version)
        target = next(t for t in drifted["tasks"] if t["task_ref"] == task_ref)
        target["task_fingerprint"] = "sha256:" + "d" * 64
        # The label is now stale (mismatch), independent of any result decision.
        self.assertNotEqual(label["task_fingerprint"], target["task_fingerprint"])
        # And the rerun planner keys off the version fingerprint change, not the label.
        plan = plan_rerun(
            self.version, drifted, model="kimi/kimi-for-coding", results_manifest=self.results
        )
        reran = {item["task_ref"]: item["reason"] for item in plan["rerun"]}
        self.assertEqual(reran.get(task_ref), "task_fingerprint changed")


if __name__ == "__main__":
    unittest.main()
