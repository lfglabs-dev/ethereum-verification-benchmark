from __future__ import annotations

import unittest

from harness.proof_patch import _patch_proof_body


ORIGINAL = """theorem sample : True := by
  sorry
"""


class ProofPatchTests(unittest.TestCase):
    def test_bare_leading_by_is_not_duplicated(self) -> None:
        candidate = _patch_proof_body(ORIGINAL, "by\n  trivial")
        self.assertEqual(candidate.rstrip(), "theorem sample : True := by\n  trivial")
        self.assertNotIn(":= by\n  by", candidate)

    def test_assign_by_wrapper_is_not_duplicated(self) -> None:
        candidate = _patch_proof_body(ORIGINAL, ":= by\n  trivial")
        self.assertEqual(candidate.rstrip(), "theorem sample : True := by\n  trivial")

    def test_by_cases_tactic_is_not_mistaken_for_wrapper(self) -> None:
        candidate = _patch_proof_body(ORIGINAL, "by_cases h : True\n· trivial\n· contradiction")
        self.assertIn("  by_cases h : True", candidate)

    def test_full_file_submission_cannot_change_preamble(self) -> None:
        submitted = """import Hidden.Proofs

namespace Sample

theorem sample : True := by
  exact True.intro

end Sample
"""
        candidate = _patch_proof_body(ORIGINAL, submitted)

        self.assertNotIn("Hidden.Proofs", candidate)
        self.assertTrue(candidate.startswith("theorem sample : True := by\n"))
        self.assertIn("  exact True.intro", candidate)


if __name__ == "__main__":
    unittest.main()
