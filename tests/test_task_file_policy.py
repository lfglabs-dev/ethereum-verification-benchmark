"""Editable task files must not ship a proof of the task theorem."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import task_file_policy  # noqa: E402

LEAKED = """import Foo.Specs

namespace Foo

private theorem helper : True := by
  trivial

theorem target (x : Nat) : x = x := by
  exact rfl

end Foo
"""

PLACEHOLDER = """import Foo.Specs

namespace Foo

/-- docstring mentioning theorem words -/
theorem target (x : Nat) : x = x := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Foo
"""


class TaskFilePolicyTests(unittest.TestCase):
    def check(self, text: str) -> list[str]:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "Task.lean"
            path.write_text(text, encoding="utf-8")
            return task_file_policy.task_file_errors(path)

    def test_every_task_file_body_is_a_placeholder(self) -> None:
        files = task_file_policy.all_task_files()
        self.assertGreaterEqual(len(files), 300)
        errors = [error for path in files for error in task_file_policy.task_file_errors(path)]
        self.assertEqual(errors, [])

    def test_placeholder_accepted(self) -> None:
        self.assertEqual(self.check(PLACEHOLDER), [])
        self.assertEqual(self.check(PLACEHOLDER.replace("exact ?_", "sorry")), [])

    def test_full_proof_and_helpers_rejected(self) -> None:
        errors = self.check(LEAKED)
        self.assertEqual(len(errors), 2)
        self.assertIn("only the task theorem", errors[0])
        self.assertIn("must be a placeholder", errors[1])

    def test_one_line_lemma_application_rejected(self) -> None:
        errors = self.check(PLACEHOLDER.replace("exact ?_", "exact target_main x"))
        self.assertEqual(len(errors), 1)


if __name__ == "__main__":
    unittest.main()
