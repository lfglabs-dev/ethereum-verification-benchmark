from __future__ import annotations

import unittest

from harness.proof_patch import _full_file_context_preserved, _patch_proof_body


ORIGINAL = """theorem sample : True := by
  sorry
"""

CONTEXT_ORIGINAL = """import Public.Specs

namespace Sample

open Public

theorem sample : True := by
  sorry

end Sample
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

    def test_full_file_submission_with_changed_context_is_detected(self) -> None:
        submitted = """import Hidden.Proofs

namespace Sample

theorem sample : True := by
  exact True.intro

end Sample
"""
        candidate = _patch_proof_body(CONTEXT_ORIGINAL, submitted)

        self.assertIn("Hidden.Proofs", candidate)
        self.assertFalse(_full_file_context_preserved(CONTEXT_ORIGINAL, candidate))

    def test_full_file_submission_preserves_allowed_helpers(self) -> None:
        submitted = """import Public.Specs

namespace Sample

open Public

private lemma helper : True := by
  trivial

theorem sample : True := by
  exact helper

end Sample
"""
        candidate = _patch_proof_body(CONTEXT_ORIGINAL, submitted)

        self.assertTrue(_full_file_context_preserved(CONTEXT_ORIGINAL, candidate))
        self.assertIn("private lemma helper", candidate)
        self.assertIn("exact helper", candidate)


if __name__ == "__main__":
    unittest.main()
