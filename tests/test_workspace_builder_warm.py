from __future__ import annotations

import os
import unittest
from contextlib import contextmanager
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from harness.classification import classify_run
from harness.manifests import Group, Task
from harness.workspace_builder import (
    _invalid_package_checkouts,
    _prefetch_mathlib_cache,
    _validate_effective_toolchain,
    _wait_for_package_checkouts,
    public_dependency_modules,
    setup_private_lake,
    warm_public_dependencies,
    warm_result_failed,
)


SKIPPED_CACHE_PREFETCH = {
    "kind": "mathlib_cache",
    "required": False,
    "status": "cached",
    "exit_code": 0,
}

VALID_TOOLCHAIN = {
    "kind": "lean_toolchain",
    "required": True,
    "status": "passed",
    "exit_code": 0,
    "declared_toolchain": "leanprover/lean4:v4.24.0",
    "effective_version": "Lean (version 4.24.0)",
    "command": [
        "elan",
        "run",
        "--install",
        "leanprover/lean4:v4.24.0",
        "lean",
        "--version",
    ],
}
VALID_CHECKOUTS = {
    "kind": "package_checkout_health",
    "required": True,
    "status": "passed",
    "exit_code": 0,
    "invalid_packages": [],
}


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
    def test_mathlib_cache_prefetch_is_persistent_and_best_effort(self) -> None:
        @contextmanager
        def fake_lease(*, label: str):
            self.assertEqual(label, "dependency_cache_get")
            yield "acquired"

        class FinishedProcess:
            returncode = 0
            pid = 123

            def poll(self):
                return 0

        with TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            root.mkdir()
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
            log_path = Path(tmp) / "warm.log"
            with log_path.open("a", encoding="utf-8") as log, patch(
                "harness.workspace_builder.ROOT", root
            ), patch(
                "harness.workspace_builder.verify_lease", fake_lease
            ), patch(
                "harness.workspace_builder.subprocess.Popen",
                return_value=FinishedProcess(),
            ) as popen:
                first = _prefetch_mathlib_cache(
                    timeout_seconds=30,
                    log=log,
                    log_path=log_path,
                    heartbeat_seconds=1,
                )
                second = _prefetch_mathlib_cache(
                    timeout_seconds=30,
                    log=log,
                    log_path=log_path,
                    heartbeat_seconds=1,
                )

        self.assertEqual(first["status"], "passed")
        self.assertEqual(second["status"], "cached")
        self.assertFalse(warm_result_failed(first))
        popen.assert_called_once()
        self.assertEqual(
            popen.call_args.args[0],
            [
                "elan",
                "run",
                "--install",
                "leanprover/lean4:v4.24.0",
                "lake",
                "exe",
                "cache",
                "get",
            ],
        )

    def test_effective_toolchain_install_uses_dependency_warm_timeout(self) -> None:
        group = Group(group_id="erc20/state", suite="active", tasks=())
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
            with patch("harness.workspace_builder.ROOT", root), patch(
                "harness.workspace_builder.subprocess.run"
            ) as run:
                run.return_value.returncode = 0
                run.return_value.stdout = "Lean (version 4.22.0)"
                run.return_value.stderr = ""
                result = warm_public_dependencies(
                    group,
                    timeout_seconds=2400,
                    log_path=root / "warm.log",
                )[0]

        self.assertEqual(result["status"], "failed")
        self.assertEqual(
            run.call_args.args[0],
            [
                "elan",
                "run",
                "--install",
                "leanprover/lean4:v4.24.0",
                "lean",
                "--version",
            ],
        )
        self.assertEqual(run.call_args.kwargs["timeout"], 2400)

    def test_conflicting_elan_toolchain_override_fails_preflight(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
            with patch("harness.workspace_builder.ROOT", root), patch.dict(
                os.environ, {"ELAN_TOOLCHAIN": "leanprover/lean4:v4.22.0"}
            ), patch("harness.workspace_builder.subprocess.run") as run:
                result = _validate_effective_toolchain(
                    root / "warm.log", timeout_seconds=1800
                )

        self.assertEqual(result["status"], "failed")
        self.assertIn("conflicts with repository pin", result["effective_version"])
        run.assert_not_called()

    def test_transient_package_checkout_race_is_waited_out(self) -> None:
        with TemporaryDirectory() as tmp, patch(
            "harness.workspace_builder._invalid_package_checkouts",
            side_effect=[["mathlib"], ["mathlib"], []],
        ), patch("harness.workspace_builder.time.sleep") as sleep, patch.dict(
            "os.environ", {"VERITY_PACKAGE_CHECKOUT_TIMEOUT_SECONDS": "30"}
        ):
            result = _wait_for_package_checkouts(Path(tmp) / "warm.log")

        self.assertEqual(result["status"], "passed")
        self.assertEqual(sleep.call_count, 2)

    def test_checkout_health_ignores_packages_outside_current_manifest(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            packages = root / ".lake" / "packages"
            (packages / "mathlib").mkdir(parents=True)
            (packages / "abandoned-checkout").mkdir()
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.24.0\n")
            (root / "lake-manifest.json").write_text(
                '{"packages": [{"name": "mathlib"}]}', encoding="utf-8"
            )
            with patch("harness.workspace_builder.ROOT", root), patch(
                "harness.workspace_builder.subprocess.run"
            ) as run:
                run.return_value.returncode = 0
                invalid = _invalid_package_checkouts()

        self.assertEqual(invalid, [])
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0][2], str(packages / "mathlib"))

    def test_failed_cache_prefetch_does_not_fail_required_warm(self) -> None:
        self.assertFalse(
            warm_result_failed(
                {
                    "kind": "mathlib_cache",
                    "required": False,
                    "status": "failed",
                    "exit_code": 124,
                }
            )
        )

    def test_package_health_is_checked_after_cache_prefetch(self) -> None:
        group = Group(group_id="erc20/state", suite="active", tasks=())
        events: list[str] = []

        @contextmanager
        def fake_lease(*, label: str):
            self.assertEqual(label, "dependency_warm")
            yield "acquired"

        def fake_prefetch(**kwargs):
            events.append("cache")
            return SKIPPED_CACHE_PREFETCH

        def fake_checkout(log_path: Path):
            events.append("health")
            return {
                **VALID_CHECKOUTS,
                "status": "failed",
                "exit_code": 1,
                "invalid_packages": ["mathlib"],
            }

        with TemporaryDirectory() as tmp, patch(
            "harness.workspace_builder.verify_lease", fake_lease
        ), patch(
            "harness.workspace_builder._validate_effective_toolchain",
            return_value=VALID_TOOLCHAIN,
        ), patch(
            "harness.workspace_builder._prefetch_mathlib_cache",
            side_effect=fake_prefetch,
        ), patch(
            "harness.workspace_builder._wait_for_package_checkouts",
            side_effect=fake_checkout,
        ), patch("harness.workspace_builder.subprocess.Popen") as popen:
            results = warm_public_dependencies(
                group, timeout_seconds=30, log_path=Path(tmp) / "warm.log"
            )

        self.assertEqual(events, ["cache", "health"])
        self.assertEqual(results[-1]["status"], "failed")
        popen.assert_not_called()

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
            [
                "Benchmark.Cases.ERC20.State.Impl",
                "Benchmark.Cases.ERC20.State.Spec",
                "Benchmark.Grindset.ArithCore",
                "Benchmark.Grindset.Attr",
                "Benchmark.Grindset.Core",
                "Benchmark.Grindset.Monad",
                "Benchmark.Grindset.Reach",
            ],
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

    def test_dependency_build_holds_verify_lease_until_process_finishes(self) -> None:
        group = Group(
            group_id="erc20/state",
            suite="active",
            tasks=(
                _task(
                    implementation=("Benchmark/Cases/ERC20/State/Impl.lean",),
                    specification=(),
                ),
            ),
        )
        events: list[str] = []

        @contextmanager
        def fake_lease(*, label: str):
            if label == "dependency_checkout_health":
                yield "acquired"
                return
            self.assertEqual(label, "dependency_warm")
            events.append("lease_enter")
            yield "acquired"
            events.append("lease_exit")

        def fake_checkout(log_path: Path):
            events.append("health")
            return VALID_CHECKOUTS

        class FinishedProcess:
            returncode = 0
            pid = 123

            def __init__(self, *args, **kwargs):
                events.append("process_start")

            def poll(self):
                events.append("process_poll")
                return 0

        with TemporaryDirectory() as tmp, patch(
            "harness.workspace_builder.verify_lease", fake_lease
        ), patch(
            "harness.workspace_builder.public_dependency_modules",
            return_value=["Benchmark.Cases.ERC20.State.Impl"],
        ), patch(
            "harness.workspace_builder._prefetch_mathlib_cache",
            return_value=SKIPPED_CACHE_PREFETCH,
        ), patch(
            "harness.workspace_builder._validate_effective_toolchain",
            return_value=VALID_TOOLCHAIN,
        ), patch(
            "harness.workspace_builder._wait_for_package_checkouts",
            side_effect=fake_checkout,
        ), patch(
            "harness.workspace_builder.subprocess.Popen", side_effect=FinishedProcess
        ) as popen:
            results = warm_public_dependencies(
                group,
                timeout_seconds=30,
                log_path=Path(tmp) / "warm.log",
            )

        self.assertEqual(results[3]["exit_code"], 0)
        self.assertEqual(
            popen.call_args.args[0],
            [
                "elan",
                "run",
                "--install",
                "leanprover/lean4:v4.24.0",
                "lake",
                "build",
                "Benchmark.Cases.ERC20.State.Impl",
            ],
        )
        self.assertEqual(
            events,
            [
                "lease_enter",
                "health",
                "process_start",
                "process_poll",
                "lease_exit",
            ],
        )

    def test_checkout_health_and_required_build_share_a_verify_lease(self) -> None:
        """A cache writer cannot invalidate checkout health before a build starts."""
        group = Group(group_id="erc20/state", suite="active", tasks=())
        events: list[str] = []

        @contextmanager
        def fake_lease(*, label: str):
            self.assertEqual(label, "dependency_warm")
            events.append("lease_enter")
            yield "acquired"
            events.append("lease_exit")

        def fake_checkout(log_path: Path):
            events.append("health")
            return VALID_CHECKOUTS

        class FinishedProcess:
            returncode = 0
            pid = 123

            def __init__(self, *args, **kwargs):
                events.append("process_start")

            def poll(self):
                return 0

        with TemporaryDirectory() as tmp, patch(
            "harness.workspace_builder.verify_lease", fake_lease
        ), patch(
            "harness.workspace_builder.public_dependency_modules",
            return_value=["Benchmark.Cases.ERC20.State.Impl"],
        ), patch(
            "harness.workspace_builder._prefetch_mathlib_cache",
            return_value=SKIPPED_CACHE_PREFETCH,
        ), patch(
            "harness.workspace_builder._validate_effective_toolchain",
            return_value=VALID_TOOLCHAIN,
        ), patch(
            "harness.workspace_builder._wait_for_package_checkouts",
            side_effect=fake_checkout,
        ), patch(
            "harness.workspace_builder.subprocess.Popen", side_effect=FinishedProcess
        ):
            warm_public_dependencies(
                group, timeout_seconds=30, log_path=Path(tmp) / "warm.log"
            )

        self.assertEqual(events, ["lease_enter", "health", "process_start", "lease_exit"])

    def test_lease_wait_does_not_consume_build_timeout_or_duration(self) -> None:
        group = Group(
            group_id="erc20/state",
            suite="active",
            tasks=(
                _task(
                    implementation=("Benchmark/Cases/ERC20/State/Impl.lean",),
                    specification=(),
                ),
            ),
        )

        @contextmanager
        def delayed_lease(*, label: str):
            if label == "dependency_checkout_health":
                yield "acquired"
                return
            self.assertEqual(label, "dependency_warm")
            yield "acquired"

        class FinishedProcess:
            returncode = 0
            pid = 123

            def poll(self):
                return 0

        clock = iter([0.0, 50.0, 55.0])
        with TemporaryDirectory() as tmp, patch(
            "harness.workspace_builder.verify_lease", delayed_lease
        ), patch(
            "harness.workspace_builder.public_dependency_modules",
            return_value=["Benchmark.Cases.ERC20.State.Impl"],
        ), patch(
            "harness.workspace_builder._prefetch_mathlib_cache",
            return_value=SKIPPED_CACHE_PREFETCH,
        ), patch(
            "harness.workspace_builder._validate_effective_toolchain",
            return_value=VALID_TOOLCHAIN,
        ), patch(
            "harness.workspace_builder._wait_for_package_checkouts",
            return_value=VALID_CHECKOUTS,
        ), patch("harness.workspace_builder.subprocess.Popen", return_value=FinishedProcess()), patch(
            "harness.workspace_builder.time.monotonic", side_effect=lambda: next(clock)
        ):
            result = warm_public_dependencies(
                group,
                timeout_seconds=30,
                log_path=Path(tmp) / "warm.log",
            )[3]

        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(result["lease_wait_seconds"], 50.0)
        self.assertEqual(result["duration_seconds"], 5.0)

    def test_spawn_failure_returns_failed_warm_result(self) -> None:
        group = Group(
            group_id="erc20/state",
            suite="active",
            tasks=(
                _task(
                    implementation=("Benchmark/Cases/ERC20/State/Impl.lean",),
                    specification=(),
                ),
            ),
        )

        @contextmanager
        def fake_lease(*, label: str):
            if label == "dependency_checkout_health":
                yield "acquired"
                return
            self.assertEqual(label, "dependency_warm")
            yield "acquired"

        with TemporaryDirectory() as tmp, patch(
            "harness.workspace_builder.verify_lease", fake_lease
        ), patch(
            "harness.workspace_builder._prefetch_mathlib_cache",
            return_value=SKIPPED_CACHE_PREFETCH,
        ), patch(
            "harness.workspace_builder._validate_effective_toolchain",
            return_value=VALID_TOOLCHAIN,
        ), patch(
            "harness.workspace_builder._wait_for_package_checkouts",
            return_value=VALID_CHECKOUTS,
        ), patch(
            "harness.workspace_builder.subprocess.Popen",
            side_effect=FileNotFoundError("lake not found"),
        ):
            result = warm_public_dependencies(
                group,
                timeout_seconds=30,
                log_path=Path(tmp) / "warm.log",
            )[3]

        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["exit_code"], 127)
        self.assertIn("lake not found", result["error"])

    def test_shared_build_cache_clone_holds_verify_lease(self) -> None:
        events: list[str] = []

        @contextmanager
        def fake_lease(*, label: str):
            self.assertEqual(label, "dependency_cache_clone")
            events.append("lease_enter")
            yield "acquired"
            events.append("lease_exit")

        def fake_clone(src: Path, dst: Path) -> None:
            self.assertTrue(src.name == "build")
            events.append("clone")
            dst.mkdir(parents=True)

        with TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            workspace = Path(tmp) / "workspace"
            (root / ".lake" / "build").mkdir(parents=True)
            workspace.mkdir()
            with patch("harness.workspace_builder.ROOT", root), patch(
                "harness.workspace_builder.verify_lease", fake_lease
            ), patch("harness.workspace_builder._clone_tree", fake_clone):
                setup_private_lake(workspace)

        self.assertEqual(events, ["lease_enter", "clone", "lease_exit"])

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
