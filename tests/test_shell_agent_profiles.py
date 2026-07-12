from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.paths import ROOT
from harness.runners.shell_agent import _run_profile_preflights


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


if __name__ == "__main__":
    unittest.main()
