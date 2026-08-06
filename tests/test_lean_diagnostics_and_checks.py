from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness import lean_check
from harness.runners import lean_tools


class LeanDiagnosticsAndChecksTests(unittest.TestCase):
    def test_remote_required_checks_enable_remote_lake_verification(self) -> None:
        class Process:
            returncode = 0
            pid = 1

            def communicate(self, timeout: int) -> tuple[str, str]:
                return "", ""

        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(
            "os.environ", {"SANDBOXED_COMPUTE_POLICY": "remote_required"}, clear=True
        ), mock.patch.object(lean_check.subprocess, "Popen", return_value=Process()) as popen:
            code, _ = lean_check._run_lean_command_unleased(Path(tmp), ["lake", "env", "lean", "Sample.lean"], 1)

        self.assertEqual(code, 0)
        self.assertEqual(popen.call_args.kwargs["env"]["SANDBOXED_REMOTE_LAKE_VERIFY"], "1")

    def test_file_check_success_is_confirmed_by_module_build(self) -> None:
        calls: list[list[str]] = []

        def fake_run(workspace: Path, command: list[str], timeout_seconds: int) -> tuple[int, str]:
            calls.append(command)
            if command == ["lake", "env", "lean", "Benchmark/Generated/Sample.lean"]:
                return 0, "file ok"
            if command == ["lake", "build", "Benchmark.Generated.Sample"]:
                return 1, "error: build failed after file check"
            return 99, "unexpected command"

        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(lean_tools, "LEAN_CHECK_MODE", "file"), mock.patch.object(
            lean_tools, "_run_lean_command", fake_run
        ):
            code, output = lean_tools._run_lean_module(
                Path(tmp),
                "Benchmark.Generated.Sample",
                file_rel="Benchmark/Generated/Sample.lean",
            )

        self.assertEqual(code, 1)
        self.assertIn("file ok", output)
        self.assertIn("build failed after file check", output)
        self.assertEqual(
            calls,
            [
                ["lake", "env", "lean", "Benchmark/Generated/Sample.lean"],
                ["lake", "build", "Benchmark.Generated.Sample"],
            ],
        )

    def test_compact_output_preserves_full_unsolved_goal_block(self) -> None:
        output = """Benchmark/Generated/Sample.lean:10:4: error: unsolved goals
case h_1
x : Nat
h : x = 1
branch : Bool
⊢ x + 0 = 1
Benchmark/Generated/Sample.lean:12:2: error: another failure
details
"""

        compact = lean_check._compact_lean_output(output)
        diagnostics = lean_check._goal_diagnostics(output)

        self.assertIn("⊢ x + 0 = 1", compact)
        self.assertEqual(diagnostics["local_hypotheses"], ["x : Nat", "h : x = 1", "branch : Bool"])
        self.assertEqual(diagnostics["target"], "x + 0 = 1")


if __name__ == "__main__":
    unittest.main()
