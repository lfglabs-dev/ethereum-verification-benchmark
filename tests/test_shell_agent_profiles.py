from __future__ import annotations

import json
import signal
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.paths import ROOT
from harness.manifests import load_group
from harness.runners.shell_agent import (
    _run_profile_preflights,
    _run_setup_process_group,
    _should_validate_host_auth,
)
from harness.result_validity import row_validity
from harness.verifier import setup_failure_verifier_result


class ShellAgentProfileTests(unittest.TestCase):
    def test_vibe_and_lean_lsp_are_pinned_and_proxy_metered(self) -> None:
        profile = json.loads((ROOT / "harness/agents/vibe-lean-lsp.json").read_text())

        self.assertTrue(profile["uses_proxy"])
        self.assertIn("mistral-vibe==2.19.1", profile["command"])
        self.assertIn("--trust", profile["command"])
        config = profile["config_files"]["~/.vibe/config.toml"]
        self.assertIn('api_base = "{proxy_url}"', config)
        self.assertIn('api_key_env_var = "VERITY_PROXY_KEY"', config)
        self.assertIn('"lean-lsp-mcp==0.28.0"', config)
        self.assertIn('LEAN_PROJECT_PATH = "{workspace}"', config)

    def test_host_authenticated_profiles_do_not_start_metering_proxy(self) -> None:
        for name in ("codex", "grok-build"):
            with self.subTest(profile=name):
                profile = json.loads((ROOT / f"harness/agents/{name}.json").read_text())
                self.assertFalse(profile["uses_proxy"])

    def test_preflight_stops_at_first_failure(self) -> None:
        profile = {
            "preflight_commands": [
                ["first", "--version"],
                ["second", "--version"],
                ["never", "--version"],
            ]
        }
        results = [
            subprocess.CompletedProcess([], 0, stdout="1.0", stderr=""),
            subprocess.CompletedProcess([], 9, stdout="", stderr="broken"),
        ]
        with tempfile.TemporaryDirectory() as raw_dir, mock.patch(
            "harness.runners.shell_agent.subprocess.run", side_effect=results
        ) as run:
            actual = _run_profile_preflights(profile, cwd=Path(raw_dir))

        self.assertEqual([item["status"] for item in actual], ["passed", "failed"])
        self.assertEqual(run.call_count, 2)
        self.assertIn("broken", actual[-1]["output_tail"])

    def test_invalid_preflight_shape_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "non-empty string list"):
            _run_profile_preflights({"preflight_commands": ["vibe --version"]}, cwd=ROOT)

    def test_multi_task_setup_failure_rows_keep_budget_and_valid_status(self) -> None:
        budget = {
            "max_attempts": None,
            "max_tool_calls": None,
            "max_turns": 20,
            "completion_token_budget": 1000,
        }
        run_row = {
            "status": "completed_with_failures",
            "harness_status": "completed_with_failures",
            "benchmark_budget": budget,
        }
        task_row = {
            "status": "request_failed",
            "failure_class": "infra_dependency_warm_failed",
            "error": {"kind": "transport_error"},
            "attempts": [],
            "benchmark_budget": budget,
        }

        self.assertTrue(row_validity(run_row, expected_budget=budget)["valid"])
        self.assertTrue(row_validity(task_row, expected_budget=budget)["valid"])

    def test_setup_failure_verifier_never_spawns_lean(self) -> None:
        group = load_group("ethereum/deposit_contract_minimal", "active")
        with tempfile.TemporaryDirectory() as raw_dir, mock.patch(
            "harness.verifier.subprocess.run"
        ) as run:
            result = setup_failure_verifier_result(
                group,
                Path(raw_dir),
                failure_class="infra_dependency_warm_failed",
                artifact_dir=Path(raw_dir) / "verifier",
            )

        run.assert_not_called()
        self.assertEqual(result["score"]["total_targets"], len(group.tasks))
        self.assertTrue(
            all(target["status"] == "verifier_infra_error" for target in result["targets"])
        )

    def test_setup_failure_precedes_host_auth_validation(self) -> None:
        host_auth = {"env_flag": "ALLOW_HOST_AUTH"}
        self.assertTrue(
            _should_validate_host_auth(
                host_auth, dry_run=False, setup_failure_class=None
            )
        )
        self.assertFalse(
            _should_validate_host_auth(
                host_auth,
                dry_run=False,
                setup_failure_class="infra_dependency_warm_failed",
            )
        )

    def test_target_warm_timeout_kills_the_process_group(self) -> None:
        process = mock.Mock(pid=4242, returncode=-9)
        process.communicate.side_effect = [
            subprocess.TimeoutExpired(["./harness/check.sh"], 1),
            ("partial stdout", "partial stderr"),
        ]
        with mock.patch(
            "harness.runners.shell_agent.subprocess.Popen", return_value=process
        ), mock.patch("harness.runners.shell_agent.os.killpg") as killpg:
            with self.assertRaises(subprocess.TimeoutExpired):
                _run_setup_process_group(
                    ["./harness/check.sh"], cwd=ROOT, timeout_seconds=1
                )

        killpg.assert_called_once_with(4242, signal.SIGKILL)
        self.assertEqual(process.communicate.call_count, 2)


if __name__ == "__main__":
    unittest.main()
