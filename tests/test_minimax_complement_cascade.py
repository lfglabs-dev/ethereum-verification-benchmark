import json
import tempfile
import unittest
from pathlib import Path

from scripts import run_minimax_complement_cascade as cascade


class MiniMaxComplementCascadeTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
