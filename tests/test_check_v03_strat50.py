import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

PATH = Path(__file__).parents[1] / "scripts" / "check_v03_strat50.py"
SPEC = importlib.util.spec_from_file_location("check_v03_strat50", PATH)
assert SPEC and SPEC.loader
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class CheckV03Strat50Tests(unittest.TestCase):
    def test_rejects_semantically_equal_reformatted_panel(self):
        original = json.loads(CHECKER.PANEL.read_text())
        with tempfile.TemporaryDirectory() as directory:
            reformatted = Path(directory) / "panel.json"
            reformatted.write_text(json.dumps(original, separators=(",", ":")) + "\n")
            with mock.patch.object(CHECKER, "PANEL", reformatted):
                with self.assertRaisesRegex(SystemExit, "byte identity changed"):
                    CHECKER.main()

    def test_committed_panel_and_metadata_are_canonical(self):
        self.assertEqual(CHECKER.main(), 0)


if __name__ == "__main__":
    unittest.main()
