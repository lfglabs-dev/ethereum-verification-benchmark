from __future__ import annotations

import unittest

from harness import classification
from harness.classification import classify_run, classify_target, submission_state


class SubmissionStateTests(unittest.TestCase):
    def test_no_submission_when_no_attempts(self) -> None:
        self.assertEqual(
            submission_state({"task_ref": "t", "status": "failed_no_attempt", "attempts": []}),
            classification.SUBMISSION_STATE_NO_SUBMISSION,
        )

    def test_unknown_for_missing_result(self) -> None:
        self.assertEqual(submission_state(None), classification.SUBMISSION_STATE_UNKNOWN)

    def test_placeholder_when_only_rejected_submissions(self) -> None:
        result = {
            "task_ref": "t",
            "status": "failed_submitted",
            "attempts": [
                {"status": "rejected_forbidden_placeholder"},
                {"status": "rejected_statement_mismatch"},
            ],
        }
        self.assertEqual(submission_state(result), classification.SUBMISSION_STATE_PLACEHOLDER)

    def test_check_failed_when_lean_ran_and_failed(self) -> None:
        result = {
            "task_ref": "t",
            "status": "failed_submitted",
            "attempts": [
                {"status": "rejected_forbidden_placeholder"},
                {"status": "lean_failed", "candidate_path": "a.lean"},
            ],
        }
        self.assertEqual(submission_state(result), classification.SUBMISSION_STATE_CHECK_FAILED)

    def test_check_passed_takes_priority(self) -> None:
        result = {
            "task_ref": "t",
            "status": "lean_passed",
            "attempts": [
                {"status": "lean_failed", "candidate_path": "a.lean"},
                {"status": "lean_passed", "candidate_path": "b.lean"},
            ],
        }
        self.assertEqual(submission_state(result), classification.SUBMISSION_STATE_CHECK_PASSED)

    def test_top_level_lean_passed_status_counts_as_passed(self) -> None:
        # Even if the attempts list omits the winning attempt, the task status is
        # authoritative for a pass.
        result = {"task_ref": "t", "status": "lean_passed", "attempts": []}
        self.assertEqual(submission_state(result), classification.SUBMISSION_STATE_CHECK_PASSED)


class ClassifyTargetFieldsTests(unittest.TestCase):
    def _gradeable(self, task_ref: str) -> dict:
        return {
            "task_ref": task_ref,
            "status": "failed_submitted",
            "attempts": [{"attempt": 1, "status": "lean_failed", "candidate_path": "a.lean"}],
        }

    def test_passed_target_reports_passed_outcome(self) -> None:
        result = classify_target({"task_ref": "t", "status": "passed", "output": ""}, None)
        self.assertEqual(result["final_class"], "SOLVED")
        self.assertEqual(result["verifier_outcome"], "passed")

    def test_genuine_fail_reports_task_failure_and_check_failed(self) -> None:
        target = {
            "task_ref": "foo/bar/baz",
            "status": "lean_check_failed",
            "output": (
                "error: Benchmark/Generated/Foo/Bar/Tasks/Baz.lean:12:4: unsolved goals\n"
                "Some required builds logged failures:\n"
                "- Benchmark.Generated.Foo.Bar.Tasks.Baz\n"
                "error: build failed"
            ),
        }
        result = classify_target(target, self._gradeable(target["task_ref"]))
        self.assertEqual(result["final_class"], "GENUINE_FAIL")
        self.assertEqual(result["verifier_outcome"], "task_failure")
        self.assertEqual(result["submission_state"], classification.SUBMISSION_STATE_CHECK_FAILED)

    def test_support_module_failure_reports_support_outcome(self) -> None:
        target = {
            "task_ref": "dvd/se/a",
            "status": "lean_check_failed",
            "output": "Some required builds logged failures:\n- Benchmark.Grindset\n",
        }
        result = classify_target(target, self._gradeable(target["task_ref"]))
        self.assertEqual(result["final_class"], "INFRA_INVALID")
        self.assertEqual(result["verifier_outcome"], "support_module_failure")


class ClassifyRunAggregateTests(unittest.TestCase):
    def test_run_aggregates_submission_and_verifier_counts(self) -> None:
        verifier = {
            "score": {"total_targets": 3, "passed_targets": 1},
            "targets": [
                {"task_ref": "a", "status": "passed", "output": ""},
                {
                    "task_ref": "b",
                    "status": "lean_check_failed",
                    "output": (
                        "error: Benchmark/Generated/B.lean:1:0: unsolved goals\n"
                        "Some required builds logged failures:\n- Benchmark.Generated.B\n"
                    ),
                },
                {
                    "task_ref": "c",
                    "status": "lean_check_failed",
                    "output": "Some required builds logged failures:\n- Benchmark.Grindset\n",
                },
            ],
        }
        task_results = [
            {"task_ref": "a", "status": "lean_passed", "attempts": [{"status": "lean_passed"}]},
            {
                "task_ref": "b",
                "status": "failed_submitted",
                "attempts": [{"status": "lean_failed", "candidate_path": "x.lean"}],
            },
            {"task_ref": "c", "status": "failed_no_attempt", "attempts": []},
        ]
        summary = classify_run(verifier, task_results)

        self.assertEqual(summary["submission_state_counts"].get("check_proof_passed"), 1)
        self.assertEqual(summary["submission_state_counts"].get("check_proof_failed"), 1)
        self.assertEqual(summary["submission_state_counts"].get("no_submission"), 1)
        self.assertEqual(summary["verifier_outcome_counts"].get("passed"), 1)
        self.assertEqual(summary["verifier_outcome_counts"].get("task_failure"), 1)
        self.assertEqual(summary["verifier_outcome_counts"].get("support_module_failure"), 1)
        # Additive fields only; existing keys remain intact.
        self.assertIn("final_class_counts", summary)
        self.assertIn("run_class", summary)


if __name__ == "__main__":
    unittest.main()
