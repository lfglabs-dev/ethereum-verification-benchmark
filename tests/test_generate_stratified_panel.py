import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).parents[1] / "scripts" / "generate_stratified_panel.py"
SPEC = importlib.util.spec_from_file_location("generate_stratified_panel", PATH)
assert SPEC and SPEC.loader
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


def manifest(case_sizes):
    tasks = []
    for case_id, size in case_sizes.items():
        for index in range(size):
            tasks.append(
                {
                    "case_id": case_id,
                    "task_ref": f"{case_id}/task-{index}",
                    "difficulty": "easy" if index % 2 == 0 else "hard",
                    "category": f"category-{case_id}",
                    "proof_family": "functional_correctness",
                    "property_class": "accounting_bound",
                }
            )
    return {
        "benchmark_version": "0.test",
        "git_sha": "abc",
        "task_set_id": "sha256:tasks",
        "environment_id": "sha256:environment",
        "harness_id": "sha256:harness",
        "tasks": tasks,
    }


class GenerateStratifiedPanelTests(unittest.TestCase):
    def test_is_deterministic_and_covers_every_case(self):
        source = manifest({"a/case": 4, "b/case": 3, "c/case": 2})
        panel_a, metadata_a = GENERATOR.generate_panel(source, panel_size=5, seed=42)
        panel_b, metadata_b = GENERATOR.generate_panel(source, panel_size=5, seed=42)
        self.assertEqual(panel_a, panel_b)
        self.assertEqual(metadata_a, metadata_b)
        self.assertEqual(len(panel_a), 5)
        selected_cases = {task_ref.rsplit("/", 1)[0] for task_ref in panel_a}
        self.assertEqual(selected_cases, {"a/case", "b/case", "c/case"})
        self.assertEqual(metadata_a["selection"]["case_coverage"], 3)

    def test_seed_changes_selection_without_changing_allocation(self):
        source = manifest({"a/case": 5, "b/case": 5})
        panel_a, metadata_a = GENERATOR.generate_panel(source, panel_size=4, seed=42)
        panel_b, metadata_b = GENERATOR.generate_panel(source, panel_size=4, seed=43)
        self.assertNotEqual(panel_a, panel_b)
        self.assertEqual(
            metadata_a["selection"]["allocation"],
            metadata_b["selection"]["allocation"],
        )

    def test_largest_remainder_prefers_larger_remaining_stratum(self):
        allocation = GENERATOR.allocate_case_slots(
            {"large": 10, "medium": 4, "single": 1}, panel_size=7, seed=42
        )
        self.assertEqual(sum(allocation.values()), 7)
        self.assertGreater(allocation["large"], allocation["medium"])
        self.assertEqual(allocation["single"], 1)

    def test_rejects_panel_smaller_than_case_count(self):
        with self.assertRaisesRegex(ValueError, "cannot cover"):
            GENERATOR.generate_panel(
                manifest({"a/case": 1, "b/case": 1, "c/case": 1}),
                panel_size=2,
                seed=42,
            )

    def test_rejects_duplicate_task_refs(self):
        source = manifest({"a/case": 2})
        source["tasks"][1]["task_ref"] = source["tasks"][0]["task_ref"]
        with self.assertRaisesRegex(ValueError, "duplicate"):
            GENERATOR.generate_panel(source, panel_size=1, seed=42)


if __name__ == "__main__":
    unittest.main()
