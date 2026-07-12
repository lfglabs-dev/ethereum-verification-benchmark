from __future__ import annotations

import unittest

from harness.classification import classify_run
from harness.manifests import Group, Task
from harness.workspace_builder import public_dependency_modules


def _task(*, implementation: tuple[str, ...], specification: tuple[str, ...]) -> Task:
    return Task(
        task_ref="erc20/state/transfer",
        task_id="transfer",
        case_id="state",
        suite="active",
        theorem_name="transfer",
        implementation_files=implementation,
        specification_files=specification,
        editable_files=("Benchmark/Cases/ERC20/State/Generated.lean",),
        reference_solution_module=None,
        reference_solution_declaration=None,
        manifest_path="cases/erc20/state/tasks/transfer.yaml",
    )


class PublicDependencyWarmTests(unittest.TestCase):
    def test_modules_are_public_deduplicated_and_sorted(self) -> None:
        group = Group(
            group_id="erc20/state",
            suite="active",
            tasks=(
                _task(
                    implementation=("Benchmark/Cases/ERC20/State/Impl.lean",),
                    specification=("Benchmark/Cases/ERC20/State/Spec.lean",),
                ),
                _task(
                    implementation=(
                        "Benchmark/Cases/ERC20/State/Impl.lean",
                        "cases/erc20/state/verity/Impl.lean",
                        "README.md",
                    ),
                    specification=(),
                ),
            ),
        )

        self.assertEqual(
            public_dependency_modules(group),
            ["Benchmark.Cases.ERC20.State.Impl", "Benchmark.Cases.ERC20.State.Spec"],
        )

    def test_hidden_proof_dependencies_are_rejected(self) -> None:
        group = Group(
            group_id="erc20/state",
            suite="active",
            tasks=(
                _task(
                    implementation=(),
                    specification=("Benchmark/Cases/ERC20/State/Proofs.lean",),
                ),
            ),
        )

        with self.assertRaisesRegex(ValueError, "forbidden dependency"):
            public_dependency_modules(group)

    def test_pre_provider_warm_failure_is_infra_invalid(self) -> None:
        task_ref = "erc20/state/transfer"
        classification = classify_run(
            {
                "score": {"passed_targets": 0, "total_targets": 1},
                "targets": [
                    {
                        "task_ref": task_ref,
                        "status": "lean_check_failed",
                        "output": "placeholder proof remains",
                    }
                ],
            },
            [
                {
                    "task_ref": task_ref,
                    "status": "request_failed",
                    "failure_class": "infra_dependency_warm_failed",
                    "error": {"kind": "transport_error"},
                    "attempts": [],
                }
            ],
        )

        self.assertEqual(classification["run_class"], "INFRA_INVALID")
        self.assertFalse(classification["reusable"])


if __name__ == "__main__":
    unittest.main()
