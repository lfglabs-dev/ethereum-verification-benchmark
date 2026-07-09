from __future__ import annotations

import unittest

from harness.classification import classify_run, classify_target
from harness.verifier import _compact_output

GRINDSET_COLLISION_OUTPUT = (
    "error: Benchmark/Grindset.lean:1:0: import Verity.Proofs.Stdlib.Automation "
    "failed, environment already contains 'Verity.getStorage.eq_1' from "
    "Benchmark.Grindset.Monad\n"
    "error: Lean exited with code 1\n"
    "Some required builds logged failures:\n"
    "- Benchmark.Grindset\n"
    "error: build failed"
)

REAL_PROOF_OUTPUT = (
    "error: Benchmark/Generated/Foo/Bar/Tasks/Baz.lean:12:4: unsolved goals\n"
    "Some required builds logged failures:\n"
    "- Benchmark.Generated.Foo.Bar.Tasks.Baz\n"
    "error: build failed"
)


def _gradeable_task_result(task_ref: str) -> dict:
    return {
        "task_ref": task_ref,
        "status": "failed_submitted",
        "attempts": [{"attempt": 1, "status": "lean_failed", "candidate_path": "a.lean"}],
    }


class SupportModuleClassificationTests(unittest.TestCase):
    def test_grindset_support_failure_is_infra_invalid(self) -> None:
        target = {
            "task_ref": "dvd/side_entrance/deposit_sets_pool_balance",
            "status": "lean_check_failed",
            "output": GRINDSET_COLLISION_OUTPUT,
        }
        result = classify_target(target, _gradeable_task_result(target["task_ref"]))
        self.assertEqual(result["final_class"], "INFRA_INVALID")
        self.assertFalse(result["reusable"])
        self.assertTrue(result["final_reason"].startswith("support_module_build_failure:"))
        self.assertIn("Benchmark.Grindset", result["final_reason"])

    def test_real_proof_failure_stays_genuine(self) -> None:
        target = {
            "task_ref": "foo/bar/baz",
            "status": "lean_check_failed",
            "output": REAL_PROOF_OUTPUT,
        }
        result = classify_target(target, _gradeable_task_result(target["task_ref"]))
        self.assertEqual(result["final_class"], "GENUINE_FAIL")
        self.assertTrue(result["reusable"])

    def test_verity_timeout_support_failure_is_infra_invalid(self) -> None:
        target = {
            "task_ref": "foo/bar/qux",
            "status": "timeout",
            "output": "Some required builds logged failures:\n- Verity.Proofs.Stdlib.Automation\n",
        }
        result = classify_target(target, _gradeable_task_result(target["task_ref"]))
        self.assertEqual(result["final_class"], "INFRA_INVALID")

    def test_mixed_failure_including_task_module_stays_genuine(self) -> None:
        # If Lake reports the agent's own module among the failures, the guard
        # must not excuse it as infra.
        output = (
            "Some required builds logged failures:\n"
            "- Benchmark.Grindset\n"
            "- Benchmark.Generated.Foo.Bar.Tasks.Baz\n"
        )
        target = {"task_ref": "foo/bar/baz", "status": "lean_check_failed", "output": output}
        result = classify_target(target, _gradeable_task_result(target["task_ref"]))
        self.assertEqual(result["final_class"], "GENUINE_FAIL")

    def test_passed_target_unaffected(self) -> None:
        target = {"task_ref": "foo/bar/baz", "status": "passed", "output": ""}
        result = classify_target(target, None)
        self.assertEqual(result["final_class"], "SOLVED")

    def test_support_bullets_outside_lake_footer_are_ignored(self) -> None:
        # A stray "- Verity.Core" bullet inside a Lean diagnostic must not let
        # a real task-module failure be excused as infra.
        output = (
            "error: Benchmark/Generated/Foo/Bar/Tasks/Baz.lean:12:4: unsolved goals\n"
            "- Verity.Core\n"
            "Some required builds logged failures:\n"
            "- Benchmark.Generated.Foo.Bar.Tasks.Baz\n"
            "error: build failed"
        )
        target = {"task_ref": "foo/bar/baz", "status": "lean_check_failed", "output": output}
        result = classify_target(target, _gradeable_task_result(target["task_ref"]))
        self.assertEqual(result["final_class"], "GENUINE_FAIL")

    def test_compact_output_preserves_lake_footer_after_verbose_error(self) -> None:
        # _compact_output keeps only 8 lines after each error line; the Lake
        # footer must survive compaction so the support-module guard still
        # sees the failed module list.
        verbose = "\n".join(
            ["error: Benchmark/Grindset/Core.lean:1:0: elaboration failed"]
            + [f"  diagnostic detail line {i}" for i in range(20)]
            + ["Some required builds logged failures:", "- Benchmark.Grindset.Core"]
        )
        compacted = _compact_output(verbose)
        self.assertIn("Some required builds logged failures:", compacted)
        self.assertIn("- Benchmark.Grindset.Core", compacted)
        target = {"task_ref": "foo/bar/baz", "status": "lean_check_failed", "output": compacted}
        result = classify_target(target, _gradeable_task_result(target["task_ref"]))
        self.assertEqual(result["final_class"], "INFRA_INVALID")

    def test_run_with_only_support_failures_is_infra_invalid(self) -> None:
        verifier = {
            "score": {"total_targets": 2, "passed_targets": 0},
            "targets": [
                {"task_ref": "dvd/se/a", "status": "lean_check_failed", "output": GRINDSET_COLLISION_OUTPUT},
                {"task_ref": "dvd/se/b", "status": "lean_check_failed", "output": GRINDSET_COLLISION_OUTPUT},
            ],
        }
        task_results = [_gradeable_task_result("dvd/se/a"), _gradeable_task_result("dvd/se/b")]
        summary = classify_run(verifier, task_results)
        self.assertEqual(summary["run_class"], "INFRA_INVALID")
        self.assertEqual(summary["final_class_counts"].get("INFRA_INVALID"), 2)


if __name__ == "__main__":
    unittest.main()
