import unittest
from scripts.check_paraclear_correspondence import compare


class CorrespondenceHarnessTests(unittest.TestCase):
    def setUp(self):
        self.fixtures = [{"id": "a", "expected": {"success": False}}]

    def test_matching_rejection(self):
        compare(self.fixtures, [{"id": "a", "result": {"success": False}}])

    def test_missing_or_duplicate_results_fail(self):
        for responses in ([], [{"id": "a", "result": {"success": False}}] * 2):
            with self.assertRaises(ValueError):
                compare(self.fixtures, responses)

    def test_empty_fixtures_fail(self):
        with self.assertRaises(ValueError):
            compare([], [])

    def test_boolean_type_and_mismatch(self):
        for value in (0, "false", True):
            with self.assertRaises(ValueError):
                compare(self.fixtures, [{"id": "a", "result": {"success": value}}])

    def test_success_requires_full_accounting_result(self):
        fixtures = [{"id": "a", "expected": {"success": True, "custody_raw": "101"}}]
        with self.assertRaises(ValueError):
            compare(fixtures, [{"id": "a", "result": {"success": True}}])

    def test_account_flags_are_not_integer_booleans(self):
        fixtures = [{"id": "a", "expected": {"success": True, "registered": True}}]
        with self.assertRaises(ValueError):
            compare(fixtures, [{"id": "a", "result": {"success": True, "registered": 1}}])


if __name__ == "__main__":
    unittest.main()
