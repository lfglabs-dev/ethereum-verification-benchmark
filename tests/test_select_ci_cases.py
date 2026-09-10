from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


PATH = Path(__file__).parents[1] / "scripts" / "select_ci_cases.py"
SPEC = importlib.util.spec_from_file_location("select_ci_cases", PATH)
assert SPEC and SPEC.loader
SELECTOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SELECTOR
SPEC.loader.exec_module(SELECTOR)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def case_manifest(*, project: str, case_id: str, family: str, implementation: str) -> str:
    return "\n".join(
        [
            "manifest_kind: case",
            f"project: {project}",
            f"case_id: {case_id}",
            f"family_id: {family}",
            f"implementation_id: {implementation}",
            "lean_target: Benchmark.Cases.Alpha.Demo.Compile",
            "spec_target: Benchmark.Cases.Alpha.Demo.Specs",
            "proof_target: Benchmark.Cases.Alpha.Demo.Proofs",
            "",
        ]
    )


TASK = """manifest_kind: task
task_id: proof
implementation_files:
  - Benchmark/Cases/Alpha/Demo/Contract.lean
specification_files:
  - Benchmark/Cases/Alpha/Demo/Specs.lean
editable_files:
  - Benchmark/Generated/Alpha/Demo/Tasks/Proof.lean
reference_solution_module: Benchmark.Cases.Alpha.Demo.Proofs
"""


class SelectCiCasesTests(unittest.TestCase):
    def make_repo(self) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        write(
            root / "cases" / "alpha" / "demo" / "case.yaml",
            case_manifest(project="alpha", case_id="demo", family="alpha", implementation="impl-a"),
        )
        write(root / "cases" / "alpha" / "demo" / "tasks" / "proof.yaml", TASK)
        write(
            root / "cases" / "beta" / "other" / "case.yaml",
            case_manifest(project="beta", case_id="other", family="alpha", implementation="impl-b"),
        )
        return root

    def test_case_tree_change_selects_that_case(self):
        root = self.make_repo()
        selection = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("M", "cases/alpha/demo/tasks/proof.yaml")], root=root
        )
        self.assertEqual(selection.cases, ("alpha/demo",))
        self.assertFalse(selection.full)

    def test_manifest_mapped_lean_source_selects_its_case(self):
        root = self.make_repo()
        selection = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("M", "Benchmark/Cases/Alpha/Demo/Contract.lean")], root=root
        )
        self.assertEqual(selection.cases, ("alpha/demo",))
        self.assertFalse(selection.full)

    def test_implementation_change_selects_only_matching_cases(self):
        root = self.make_repo()
        selection = SELECTOR.select_changes(
            [
                SELECTOR.ChangedFile(
                    "M", "families/alpha/implementations/impl-a/implementation.yaml"
                )
            ],
            root=root,
        )
        self.assertEqual(selection.cases, ("alpha/demo",))
        self.assertFalse(selection.full)

    def test_shared_or_unmapped_sources_require_full_validation(self):
        root = self.make_repo()
        shared = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("M", "harness/task_runner.py")], root=root
        )
        unmapped = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("M", "Benchmark/Shared/NewHelper.lean")], root=root
        )
        self.assertTrue(shared.full)
        self.assertTrue(unmapped.full)

    def test_deleted_case_and_unknown_files_fail_closed(self):
        root = self.make_repo()
        deleted = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("D", "cases/alpha/demo/case.yaml")], root=root
        )
        unknown = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("M", "new-runtime-config.txt")], root=root
        )
        self.assertTrue(deleted.full)
        self.assertTrue(unknown.full)

    def test_docs_only_change_does_not_select_a_lean_target(self):
        root = self.make_repo()
        selection = SELECTOR.select_changes(
            [SELECTOR.ChangedFile("M", "docs/running-benchmark.md")], root=root
        )
        self.assertEqual(selection.cases, ())
        self.assertFalse(selection.full)

    def test_git_diff_reader_treats_renames_as_removed_and_added(self):
        completed = mock.Mock(
            returncode=0,
            stdout=(
                b"M\x00cases/alpha/demo/tasks/proof.yaml\x00"
                b"R100\x00Benchmark/Old.lean\x00Benchmark/New.lean\x00"
            ),
            stderr=b"",
        )
        with mock.patch.object(SELECTOR.subprocess, "run", return_value=completed):
            changes = SELECTOR.git_changes(base="base", head="head")
        self.assertEqual(
            changes,
            (
                SELECTOR.ChangedFile("M", "cases/alpha/demo/tasks/proof.yaml"),
                SELECTOR.ChangedFile("D", "Benchmark/Old.lean"),
                SELECTOR.ChangedFile("A", "Benchmark/New.lean"),
            ),
        )


if __name__ == "__main__":
    unittest.main()
