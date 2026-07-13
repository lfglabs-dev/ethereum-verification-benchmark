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
from harness.metering_proxy import adapt_text_tool_response
from harness.runners.shell_agent import (
    _completed_shell_status,
    _preserve_toolchain_env,
    _run_profile_preflights,
    _run_setup_process_group,
    _shell_task_status,
    _should_validate_host_auth,
)
from harness.result_validity import row_validity
from harness.verifier import setup_failure_verifier_result


class ShellAgentProfileTests(unittest.TestCase):
    def test_shell_prompt_avoids_broad_build_and_prefers_lean_tools(self) -> None:
        from harness.runners.shell_agent import _prompt

        prompt = _prompt(load_group("ethereum/deposit_contract_minimal", "active"))
        self.assertIn("Do not run a broad `lake build`", prompt)
        self.assertIn("Prefer available Lean MCP", prompt)

    def test_isolated_home_preserves_existing_elan_toolchains(self) -> None:
        with tempfile.TemporaryDirectory() as raw_home:
            elan_home = Path(raw_home) / ".elan"
            elan_home.mkdir()
            env: dict[str, str] = {}
            _preserve_toolchain_env(env, Path(raw_home))
            self.assertEqual(env["ELAN_HOME"], str(elan_home))

            explicit = {"ELAN_HOME": "/custom/elan"}
            _preserve_toolchain_env(explicit, Path(raw_home))
            self.assertEqual(explicit["ELAN_HOME"], "/custom/elan")

    def test_gradeable_shell_exit_is_a_completed_run(self) -> None:
        tasks = [{"status": "failed_submitted"}]
        self.assertEqual(
            _completed_shell_status(tasks, "harness_error"),
            "completed_with_failures",
        )
        self.assertEqual(
            _completed_shell_status([{"status": "lean_passed"}], "harness_error"),
            "completed",
        )

    def test_vibe_and_lean_lsp_are_pinned_and_proxy_metered(self) -> None:
        profile = json.loads((ROOT / "harness/agents/vibe-lean-lsp.json").read_text())

        self.assertTrue(profile["uses_proxy"])
        self.assertIn("mistral-vibe==2.19.1", profile["command"])
        self.assertIn("verity-lean", profile["command"])
        self.assertIn("--trust", profile["command"])
        self.assertTrue(profile["text_tool_fallback"])
        config = profile["config_files"]["~/.vibe/config.toml"]
        self.assertIn('api_base = "{proxy_url}"', config)
        self.assertIn('api_key_env_var = "VERITY_PROXY_KEY"', config)
        self.assertIn('"lean-lsp-mcp==0.28.0"', config)
        self.assertIn('LEAN_PROJECT_PATH = "{workspace}"', config)
        self.assertIn('system_prompt_id = "lean"', profile["config_files"]["~/.vibe/agents/verity-lean.toml"])

    def test_vibe_text_tool_fallback_recovers_multiple_calls(self) -> None:
        request = {
            "tools": [
                {"type": "function", "function": {"name": "read_file"}},
                {"type": "function", "function": {"name": "lean-lsp_lean_diagnostic_messages"}},
            ]
        }
        response = {
            "choices": [
                {
                    "message": {
                        "role": "assistant",
                        "content": 'I will inspect it.read{"path":"Foo.lean"}lean-lsp_lean_diagnostic_messages{"file_path":"Foo.lean"}',
                    },
                    "finish_reason": "stop",
                }
            ],
            "usage": {"total_tokens": 10},
        }

        adapted = json.loads(
            adapt_text_tool_response(
                json.dumps(response).encode(),
                json.dumps(request).encode(),
            )
        )

        message = adapted["choices"][0]["message"]
        self.assertEqual(message["content"], "I will inspect it.")
        self.assertEqual(
            [call["function"]["name"] for call in message["tool_calls"]],
            ["read_file", "lean-lsp_lean_diagnostic_messages"],
        )
        self.assertEqual(adapted["choices"][0]["finish_reason"], "tool_calls")

    def test_vibe_text_tool_fallback_leaves_prose_unchanged(self) -> None:
        request = {"tools": [{"type": "function", "function": {"name": "read_file"}}]}
        response = {"choices": [{"message": {"role": "assistant", "content": "No tool call needed."}}]}
        encoded = json.dumps(response).encode()

        self.assertEqual(adapt_text_tool_response(encoded, json.dumps(request).encode()), encoded)

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
            "harness.runners.shell_agent._run_setup_process_group", side_effect=results
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

    def test_normal_shell_task_rows_are_aggregatable(self) -> None:
        budget = {
            "max_attempts": None,
            "max_tool_calls": None,
            "max_turns": 20,
            "completion_token_budget": 1000,
        }
        passed = {
            "task_ref": "case/a",
            "status": "lean_passed",
            "attempts": [{"index": 1, "exit_code": 0}],
            "benchmark_budget": budget,
            "usage": {"requests": 1, "total_tokens": 100},
            "verifier_confirmed": True,
        }
        failed = {
            "task_ref": "case/b",
            "status": "failed_submitted",
            "attempts": [{"index": 1, "exit_code": 0}],
            "benchmark_budget": budget,
            "usage": {"requests": 1, "total_tokens": 100},
            "verifier_confirmed": False,
        }

        self.assertTrue(row_validity(passed, expected_budget=budget)["valid"])
        self.assertTrue(row_validity(failed, expected_budget=budget)["valid"])

    def test_untouched_shell_crash_is_not_a_gradeable_submission(self) -> None:
        self.assertEqual(
            _shell_task_status(
                verifier_passed=False,
                harness_status="harness_error",
                exit_code=1,
                editable_changed=False,
            ),
            "request_failed",
        )
        self.assertEqual(
            _shell_task_status(
                verifier_passed=False,
                harness_status="timeout",
                exit_code=124,
                editable_changed=False,
            ),
            "request_timeout",
        )

    def test_shell_crash_with_modified_candidate_remains_gradeable(self) -> None:
        self.assertEqual(
            _shell_task_status(
                verifier_passed=False,
                harness_status="harness_error",
                exit_code=1,
                editable_changed=True,
            ),
            "failed_submitted",
        )

    def test_verified_shell_candidate_wins_over_cli_exit(self) -> None:
        self.assertEqual(
            _shell_task_status(
                verifier_passed=True,
                harness_status="harness_error",
                exit_code=1,
                editable_changed=True,
            ),
            "lean_passed",
        )

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
