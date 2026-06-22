from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from harness.budgets import BudgetProfile, budget_artifact
from harness.result_validity import failure_taxonomy, row_validity
from scripts import aggregate_runs


class HarnessV02Tests(unittest.TestCase):
    def test_failure_taxonomy_uses_release_buckets(self) -> None:
        self.assertEqual(failure_taxonomy("malformed_tool_call", []), "malformed_tool_call")
        self.assertEqual(failure_taxonomy("preflight_failed", []), "provider_setup_error")
        self.assertEqual(failure_taxonomy("request_timeout", []), "request_timeout")
        self.assertEqual(
            failure_taxonomy(
                "failed_submitted",
                [{"failure_kind": "lean_unknown_name", "output": "error: unknown identifier Foo"}],
                tool_calls=2,
            ),
            "unknown_identifier",
        )
        self.assertEqual(
            failure_taxonomy(
                "failed_submitted",
                [{"failure_kind": "lean_unsolved_goals", "output": "unsolved goals"}],
                tool_calls=2,
            ),
            "lean_unsolved_goal",
        )

    def test_row_validity_rejects_setup_and_zero_usage_completion(self) -> None:
        budget = {"max_attempts": 4, "max_tool_calls": 40, "max_turns": None, "completion_token_budget": 0}
        valid = row_validity(
            {
                "status": "lean_passed",
                "usage": {"requests": 1, "total_tokens": 10},
                "tool_calls_executed": 3,
                "benchmark_budget": budget,
            },
            expected_budget=budget,
        )
        self.assertTrue(valid["valid"])
        invalid = row_validity(
            {
                "status": "lean_passed",
                "usage": {"requests": 1, "total_tokens": 0},
                "tool_calls_executed": 3,
                "benchmark_budget": budget,
            },
            expected_budget=budget,
        )
        self.assertFalse(invalid["valid"])
        setup = row_validity({"status": "preflight_failed", "provider_setup_error": True})
        self.assertFalse(setup["valid"])
        verifier_shell_pass = row_validity({"status": "lean_passed", "usage": {"requests": None}, "verifier_confirmed": True})
        self.assertTrue(verifier_shell_pass["valid"])

    def test_budget_artifact_separates_benchmark_and_operational_limits(self) -> None:
        artifact = budget_artifact(BudgetProfile(max_attempts=4, max_tool_calls=40, max_turns=20, shell_timeout_seconds=900))
        self.assertEqual(artifact["benchmark_budget"]["max_attempts"], 4)
        self.assertIn("request_timeout_seconds", artifact["operational_budget"])
        self.assertNotIn("request_timeout_seconds", artifact["benchmark_budget"])

    def test_aggregate_excludes_invalid_rows_from_pass_denominator(self) -> None:
        rows = [
            {"valid": True, "passed": True, "completion_tokens": 10, "prompt_tokens": 20, "failure_counts": {}},
            {"valid": False, "passed": False, "completion_tokens": 5, "prompt_tokens": 10, "failure_counts": {"provider_setup_error": 1}},
        ]
        summary = aggregate_runs._model_summary(rows)
        self.assertEqual(summary["tasks"], 2)
        self.assertEqual(summary["valid_tasks"], 1)
        self.assertEqual(summary["invalid_tasks"], 1)
        self.assertEqual(summary["passed"], 1)
        self.assertEqual(summary["failure_counts"], {"provider_setup_error": 1})

    def test_aggregate_accepts_verifier_clean_shell_pass_without_requests(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp) / "run"
            run_dir.mkdir()
            (run_dir / "run.json").write_text(
                json.dumps(
                    {
                        "run_id": "shell-pass",
                        "harness_id": "shell",
                        "model": "local",
                        "task_ref": "case/task",
                        "harness_status": "completed",
                        "usage": {"requests": None, "total_tokens": 123},
                        "verifier": {"score": {"passed_targets": 1, "total_targets": 1}},
                    }
                ),
                encoding="utf-8",
            )
            rows = aggregate_runs.collect_runs(Path(tmp))
        self.assertEqual(len(rows), 1)
        self.assertTrue(rows[0]["valid"])
        self.assertTrue(rows[0]["passed"])


if __name__ == "__main__":
    unittest.main()
