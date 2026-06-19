from __future__ import annotations

import csv
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import plan_budget_scaling_experiment as scaling


class BudgetScalingTests(unittest.TestCase):
    def test_summary_uses_selected_panel_size_when_results_are_partial(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            selected = [
                {"rank": 1, "task_ref": "family/case/task1"},
                {"rank": 2, "task_ref": "family/case/task2"},
                {"rank": 3, "task_ref": "family/case/task3"},
                {"rank": 4, "task_ref": "family/case/task4"},
            ]
            rows = [
                {
                    "profile": scaling.PROFILES[0].name,
                    "task_ref": "family/case/task1",
                    "passed": True,
                    "total_tokens": 100,
                    "completion_tokens": 10,
                    "requests": 1,
                },
                {
                    "profile": scaling.PROFILES[0].name,
                    "task_ref": "family/case/task2",
                    "passed": False,
                    "total_tokens": 200,
                    "completion_tokens": 20,
                    "requests": 1,
                },
            ]
            (out / "selected_tasks.json").write_text(json.dumps(selected), encoding="utf-8")
            (out / "cascade_results.json").write_text(json.dumps(rows), encoding="utf-8")

            scaling.write_cascade_summary(out)

            with (out / "cascade_summary.csv").open(encoding="utf-8", newline="") as handle:
                summary = list(csv.DictReader(handle))
            self.assertEqual(summary[0]["task_count"], "4")
            self.assertEqual(summary[0]["cumulative_solved"], "1")
            self.assertEqual(summary[0]["solve_rate"], "0.25")

            solve_rate_svg = (out / "cascade_solve_rate.svg").read_text(encoding="utf-8")
            solve_events_svg = (out / "cascade_solve_events.svg").read_text(encoding="utf-8")
            self.assertIn("selected 4-task panel", solve_rate_svg)
            self.assertIn("1/4", solve_rate_svg)
            self.assertIn("1/4 solved", solve_events_svg)


if __name__ == "__main__":
    unittest.main()
