"""Regression tests for the model_truncation classifier path.

The classifier must reclassify a non-passing target as ``model_truncation``
when the harness captured a finish_reason="length" response, instead of
labelling it as ``forbidden_placeholder`` or ``unsolved_goals``. This is
essential to distinguish a model that ran out of completion budget from a
model that gave up.

No network calls; classification is exercised on synthetic run.json fixtures.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ModelTruncationClassifierTests(unittest.TestCase):
    def test_truncation_reclassifies_forbidden_placeholder(self) -> None:
        with tempfile.TemporaryDirectory(prefix="model-truncation-") as tmp:
            run_dir = Path(tmp) / "abcdef0123456789abcdef0123456789abcdef01"
            run_dir.mkdir()
            run = {
                "run_id": run_dir.name,
                "model": "minimax/MiniMax-M3",
                "verifier": {
                    "score": {"passed_targets": 0, "total_targets": 1},
                    "targets": [
                        {
                            "task_ref": "superfluid/realtime_balance_conservation/callback_level_two_is_rejected",
                            "status": "forbidden_placeholder",
                            "output": "declaration uses 'sorry'",
                        }
                    ],
                },
                "response_meta": {
                    "superfluid/realtime_balance_conservation/callback_level_two_is_rejected/1": {
                        "finish_reason": "length",
                        "returned_model": "MiniMax-M3",
                        "http_status": 200,
                    }
                },
            }
            (run_dir / "run.json").write_text(json.dumps(run), encoding="utf-8")

            result = subprocess.run(
                [sys.executable, "scripts/classify_failures.py", tmp, "--format", "json"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            rows = json.loads(result.stdout)
            self.assertEqual(len(rows), 1)
            row = rows[0]
            self.assertEqual(row["outcome"], "model_truncation")
            self.assertIn("finish_reason=length", row["detail"])

    def test_passing_target_is_not_relabelled(self) -> None:
        """A passing target must never be relabelled model_truncation even
        if some follow-up assistant turn was length-clipped."""
        with tempfile.TemporaryDirectory(prefix="model-truncation-pass-") as tmp:
            run_dir = Path(tmp) / ("ff" * 20)
            run_dir.mkdir()
            run = {
                "run_id": run_dir.name,
                "model": "minimax/MiniMax-M3",
                "verifier": {
                    "score": {"passed_targets": 1, "total_targets": 1},
                    "targets": [
                        {
                            "task_ref": "x/y/z",
                            "status": "passed",
                            "output": "",
                        }
                    ],
                },
                "response_meta": {
                    "x/y/z/2": {"finish_reason": "length", "returned_model": "MiniMax-M3", "http_status": 200},
                },
            }
            (run_dir / "run.json").write_text(json.dumps(run), encoding="utf-8")

            result = subprocess.run(
                [sys.executable, "scripts/classify_failures.py", tmp, "--format", "json"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            rows = json.loads(result.stdout)
            self.assertEqual(rows[0]["outcome"], "passed")

    def test_no_response_meta_keeps_legacy_classification(self) -> None:
        with tempfile.TemporaryDirectory(prefix="model-truncation-legacy-") as tmp:
            run_dir = Path(tmp) / ("ee" * 20)
            run_dir.mkdir()
            run = {
                "run_id": run_dir.name,
                "model": "minimax/MiniMax-M3",
                "verifier": {
                    "score": {"passed_targets": 0, "total_targets": 1},
                    "targets": [
                        {
                            "task_ref": "x/y/z",
                            "status": "forbidden_placeholder",
                            "output": "declaration uses 'sorry'",
                        }
                    ],
                },
            }
            (run_dir / "run.json").write_text(json.dumps(run), encoding="utf-8")
            result = subprocess.run(
                [sys.executable, "scripts/classify_failures.py", tmp, "--format", "json"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            rows = json.loads(result.stdout)
            self.assertEqual(rows[0]["outcome"], "forbidden_placeholder")


if __name__ == "__main__":
    unittest.main()