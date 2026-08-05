from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


class ClassifierSelfTestTests(unittest.TestCase):
    def test_self_test_runs_without_runs_dir(self) -> None:
        result = subprocess.run(
            [sys.executable, "scripts/classify_failures.py", "--self-test"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "failure classifier self-test passed")


if __name__ == "__main__":
    unittest.main()
