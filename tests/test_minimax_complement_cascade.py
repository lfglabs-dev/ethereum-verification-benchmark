import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import run_minimax_complement_cascade as cascade


class MiniMaxComplementCascadeTests(unittest.TestCase):
    def test_completed_harness_failures_are_not_retryable(self) -> None:
        response = {
            "status": "completed",
            "tasks": [
                {
                    "status": "max_attempts_exceeded",
                    "failure_class": "max_attempts_exceeded",
                    "attempts": [
                        {
                            "status": "lean_failed",
                            "output": "deterministic timeout at `isDefEq`",
                            "failure_kind": "lean_timeout",
                        }
                    ],
                }
            ],
            "operational_budget": {"request_timeout_seconds": 600},
        }

        self.assertFalse(cascade.is_retryable_harness_response(response, returncode=1))

    def test_harness_errors_remain_retryable(self) -> None:
        response = {
            "status": "harness_error",
            "error": "request_timeout while contacting provider",
        }

        self.assertTrue(cascade.is_retryable_harness_response(response, returncode=1))

    def test_recover_rows_preserves_invalid_existing_rows_for_resume_guard(self) -> None:
        selected = [{"task_ref": "family/case/task"}]
        invalid_row = {
            "profile": cascade.PROFILES[0].name,
            "task_ref": "family/case/task",
            "passed": False,
            "requests": 0,
            "provider_setup_error": "provider_setup_error",
        }
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            (output / "cascade_results.json").write_text(json.dumps([invalid_row]), encoding="utf-8")

            rows = cascade.recover_rows(output, selected, [cascade.PROFILES[0]])

        self.assertEqual(rows, [invalid_row])
        self.assertFalse(cascade.is_valid_model_row(rows[0]))

    def test_recover_rows_ignores_invalid_stdout_rows(self) -> None:
        selected = [
            {"task_ref": "family/case/invalid"},
            {"task_ref": "family/case/valid"},
        ]
        valid_row = {
            "profile": cascade.PROFILES[0].name,
            "task_ref": "family/case/valid",
            "passed": False,
            "requests": 1,
        }
        invalid_row = {
            "profile": cascade.PROFILES[0].name,
            "task_ref": "family/case/invalid",
            "passed": False,
            "requests": 0,
        }

        def fake_row_from_run_dir(task_ref: str, *_args: object, **_kwargs: object) -> dict:
            return valid_row if task_ref == "family/case/valid" else invalid_row

        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            profile_dir = output / "runs" / cascade.PROFILES[0].name
            profile_dir.mkdir(parents=True)
            (profile_dir / "family__case__invalid.stdout.txt").write_text("/tmp/invalid/results/runs/run\n")
            (profile_dir / "family__case__valid.stdout.txt").write_text("/tmp/valid/results/runs/run\n")

            with mock.patch.object(cascade, "row_from_run_dir", side_effect=fake_row_from_run_dir):
                rows = cascade.recover_rows(output, selected, [cascade.PROFILES[0]])

        self.assertEqual(rows, [valid_row])


if __name__ == "__main__":
    unittest.main()
