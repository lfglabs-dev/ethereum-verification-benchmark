from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from harness.budgets import BudgetProfile, budget_artifact, dependency_warm_timeout_seconds
from harness.classification import classify_run
from harness.manifests import load_group
from harness.result_validity import failure_taxonomy, row_validity
from harness.runners.lean_tools import _provider_setup_task_rows, _warm_target_modules
from harness.runners import lean_tools_mcp
from harness import cli
from scripts import aggregate_runs
from scripts import validate_v02_reference_contract as validator


class HarnessV02Tests(unittest.TestCase):
    def test_frozen_run_preflight_blocks_before_runner_or_provider(self) -> None:
        """Reference/proof drift must stop a v0.2 run before task execution."""
        with patch(
            "scripts.validate_v02_reference_contract.ensure_structural_contract",
            side_effect=ValueError("reference proof hash drift"),
        ), patch("harness.cli.run_lean_tools_mcp_group") as runner:
            with self.assertRaisesRegex(ValueError, "reference proof hash drift"):
                cli.run_group(
                    "ethereum/deposit_contract_minimal", "default", "v0.2",
                    False, True, 1, 1, 1, 1,
                )
        runner.assert_not_called()

    def test_invalid_v02_contract_files_block_before_runner_or_provider(self) -> None:
        cases = (
            ("missing manifest", "manifest", None),
            ("missing reference contract", "references", None),
            ("malformed manifest", "manifest", "{"),
            ("malformed reference contract", "references", "{"),
        )
        root = Path(__file__).resolve().parent.parent
        good_manifest = (root / "benchmark-versions/v0.2.json").read_text(encoding="utf-8")
        good_references = (root / "benchmark-versions/v0.2-references.json").read_text(encoding="utf-8")
        for label, target, contents in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as directory:
                directory = Path(directory)
                manifest = directory / "v0.2.json"
                references = directory / "v0.2-references.json"
                if target != "manifest":
                    manifest.write_text(good_manifest, encoding="utf-8")
                elif contents is not None:
                    manifest.write_text(contents, encoding="utf-8")
                if target != "references":
                    references.write_text(good_references, encoding="utf-8")
                elif contents is not None:
                    references.write_text(contents, encoding="utf-8")
                with patch.object(validator, "MANIFEST", manifest), patch.object(
                    validator, "REFERENCES", references
                ), patch("harness.cli.run_lean_tools_mcp_group") as runner, patch.object(
                    validator, "run_lean"
                ) as verifier:
                    with self.assertRaisesRegex(ValueError, "v0.2 reference preflight failed"):
                        cli.run_group(
                            "ethereum/deposit_contract_minimal", "default", "v0.2",
                            False, True, 1, 1, 1, 1,
                        )
                runner.assert_not_called()
                verifier.assert_not_called()

    def test_default_dispatches_only_to_mcp_runner_without_provider_setup(self) -> None:
        """The canonical default must not select the bespoke Lean loop or shell agents."""
        with patch("harness.cli.run_lean_tools_mcp_group", return_value=(0, Path("/tmp/mcp"))) as mcp:
            code, run_dir = cli.run_group(
                "ethereum/deposit_contract_minimal", "default", "active",
                False, True, 1, 1, 1, 4,
            )

        self.assertEqual((code, run_dir), (0, Path("/tmp/mcp")))
        mcp.assert_called_once()
        self.assertEqual(mcp.call_args.kwargs["max_turns"], 1)
        self.assertNotIn("run_lean_tools_group", cli.__dict__)
        self.assertNotIn("run_shell_group", cli.__dict__)

    def test_mcp_adapter_forwards_turn_cap(self) -> None:
        with patch.object(lean_tools_mcp.lean_tools, "run_group", return_value=(0, Path("/tmp/run"))) as runner:
            lean_tools_mcp.run_group("ethereum/deposit_contract_minimal", max_turns=7)
        self.assertEqual(runner.call_args.kwargs["max_turns"], 7)

    def test_default_profile_is_the_only_runnable_mcp_profile(self) -> None:
        root = Path(__file__).resolve().parent.parent
        profile = json.loads((root / "harness/agents/default.json").read_text(encoding="utf-8"))

        self.assertEqual(profile["command"][:3], ["python3", "-m", "harness.runners.lean_tools_mcp"])
        self.assertEqual(profile["track"], "group/lean_tools_mcp")
        self.assertEqual(profile["lean_lsp_mcp_version"], "0.28.0")
        for obsolete in ("builtin-lean-lsp.json", "grok-build.json", "vibe-lean-lsp.json", "opencode.json"):
            self.assertFalse((root / "harness/agents" / obsolete).exists())

    def test_target_warming_stops_after_first_timeout(self) -> None:
        tasks = [
            {"task_ref": "case/one", "target_module": "Target.One"},
            {"task_ref": "case/two", "target_module": "Target.Two"},
        ]
        with tempfile.TemporaryDirectory() as tmp, patch(
            "harness.runners.lean_tools._run_lean_module",
            side_effect=[(124, "timed out"), (0, "must not run")],
        ) as run:
            root = Path(tmp)
            results = _warm_target_modules(
                workspace=root,
                run_dir=root,
                tasks=tasks,
                timeout_seconds=10,
            )

        self.assertEqual(run.call_count, 1)
        self.assertEqual([item["task_ref"] for item in results], ["case/one"])
        self.assertEqual(results[0]["exit_code"], 124)

    def test_provider_preflight_failure_emits_non_reusable_task_rows(self) -> None:
        group = load_group("ethereum/deposit_contract_minimal", "active")
        budget = {
            "max_attempts": 4,
            "max_tool_calls": 40,
            "max_turns": None,
            "completion_token_budget": 0,
        }
        rows = _provider_setup_task_rows(group, budget, "model not found")

        self.assertEqual(len(rows), len(group.tasks))
        self.assertTrue(all(row["status"] == "preflight_failed" for row in rows))
        self.assertTrue(all(row["provider_setup_error"] for row in rows))
        self.assertTrue(
            all(not row_validity(row, expected_budget=budget)["valid"] for row in rows)
        )

        verifier = {
            "score": {"passed_targets": 0, "total_targets": len(rows)},
            "targets": [
                {"task_ref": row["task_ref"], "status": "verifier_infra_error"}
                for row in rows
            ],
        }
        classification = classify_run(verifier, rows)
        self.assertEqual(classification["run_class"], "INFRA_INVALID")
        self.assertFalse(classification["reusable"])
        self.assertEqual(
            classification["final_class_counts"],
            {"INFRA_INVALID": len(rows)},
        )

    def test_failure_taxonomy_uses_release_buckets(self) -> None:
        self.assertEqual(failure_taxonomy("malformed_tool_call", []), "malformed_tool_call")
        self.assertEqual(failure_taxonomy("preflight_failed", []), "provider_setup_error")
        self.assertEqual(failure_taxonomy("request_timeout", []), "request_timeout")
        self.assertEqual(
            failure_taxonomy(
                "failed_submitted",
                [{"failure_kind": "lean_unknown_name", "output": "error: unknown identifier Foo"}],
                tool_calls=2,
            ),
            "unknown_identifier",
        )
        self.assertEqual(
            failure_taxonomy(
                "failed_submitted",
                [{"failure_kind": "lean_unsolved_goals", "output": "unsolved goals"}],
                tool_calls=2,
            ),
            "lean_unsolved_goal",
        )

    def test_row_validity_rejects_setup_and_zero_usage_completion(self) -> None:
        budget = {"max_attempts": 4, "max_tool_calls": 40, "max_turns": None, "completion_token_budget": 0}
        valid = row_validity(
            {
                "status": "lean_passed",
                "usage": {"requests": 1, "total_tokens": 10},
                "tool_calls_executed": 3,
                "benchmark_budget": budget,
            },
            expected_budget=budget,
        )
        self.assertTrue(valid["valid"])
        invalid = row_validity(
            {
                "status": "lean_passed",
                "usage": {"requests": 1, "total_tokens": 0},
                "tool_calls_executed": 3,
                "benchmark_budget": budget,
            },
            expected_budget=budget,
        )
        self.assertFalse(invalid["valid"])
        setup = row_validity({"status": "preflight_failed", "provider_setup_error": True})
        self.assertFalse(setup["valid"])
        verifier_shell_pass = row_validity({"status": "lean_passed", "usage": {"requests": None}, "verifier_confirmed": True})
        self.assertTrue(verifier_shell_pass["valid"])

    def test_strict_hybrid_validity_requires_writer_and_prover_submission(self) -> None:
        row = {
            "status": "lean_passed",
            "usage": {"requests": 1, "total_tokens": 10},
            "role_metrics": {"role_config": {"strict_role_separation": True}, "prover_writer_calls": 0},
            "attempts": [{"status": "lean_passed", "prover_derived": False}],
        }
        invalid = row_validity(row)
        self.assertFalse(invalid["valid"])
        self.assertIn("strict-hybrid row has no prover writer routing", invalid["errors"])
        self.assertIn("strict-hybrid row has no prover-derived accepted submission", invalid["errors"])
        row["role_metrics"]["prover_writer_calls"] = 1
        row["attempts"][0]["prover_derived"] = True
        self.assertTrue(row_validity(row)["valid"])

    def test_budget_artifact_separates_benchmark_and_operational_limits(self) -> None:
        artifact = budget_artifact(BudgetProfile(max_attempts=4, max_tool_calls=40, max_turns=20, shell_timeout_seconds=900))
        self.assertEqual(artifact["benchmark_budget"]["max_attempts"], 4)
        self.assertIn("request_timeout_seconds", artifact["operational_budget"])
        self.assertNotIn("request_timeout_seconds", artifact["benchmark_budget"])

    def test_dependency_warm_timeout_follows_target_warm_default_and_override(self) -> None:
        with patch.dict("os.environ", {}, clear=True):
            self.assertEqual(dependency_warm_timeout_seconds(), 1800)
        with patch.dict(
            "os.environ",
            {"DEFAULT_HARNESS_DEPENDENCY_WARM_TIMEOUT_SECONDS": "2400"},
            clear=True,
        ):
            self.assertEqual(dependency_warm_timeout_seconds(), 2400)

    def test_aggregate_excludes_invalid_rows_from_pass_denominator(self) -> None:
        rows = [
            {"valid": True, "passed": True, "completion_tokens": 10, "prompt_tokens": 20, "failure_counts": {}},
            {"valid": False, "passed": False, "completion_tokens": 5, "prompt_tokens": 10, "failure_counts": {"provider_setup_error": 1}},
        ]
        summary = aggregate_runs._model_summary(rows)
        self.assertEqual(summary["tasks"], 2)
        self.assertEqual(summary["valid_tasks"], 1)
        self.assertEqual(summary["invalid_tasks"], 1)
        self.assertEqual(summary["passed"], 1)
        self.assertEqual(summary["failure_counts"], {"provider_setup_error": 1})

    def test_aggregate_accepts_verifier_clean_shell_pass_without_requests(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp) / "run"
            run_dir.mkdir()
            (run_dir / "run.json").write_text(
                json.dumps(
                    {
                        "run_id": "shell-pass",
                        "harness_id": "shell",
                        "model": "local",
                        "task_ref": "case/task",
                        "harness_status": "completed",
                        "usage": {"requests": None, "total_tokens": 123},
                        "verifier": {"score": {"passed_targets": 1, "total_targets": 1}},
                    }
                ),
                encoding="utf-8",
            )
            rows = aggregate_runs.collect_runs(Path(tmp))
        self.assertEqual(len(rows), 1)
        self.assertTrue(rows[0]["valid"])
        self.assertTrue(rows[0]["passed"])

    def test_aggregate_counts_suite_failures_as_valid_failures(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp) / "run"
            run_dir.mkdir()
            (run_dir / "run.json").write_text(
                json.dumps(
                    {
                        "run_id": "suite-failure",
                        "harness_id": "suite",
                        "model": "local",
                        "task_ref": "case/task",
                        "harness_status": "completed_with_failures",
                        "usage": {"requests": 1, "total_tokens": 123},
                        "verifier": {"score": {"passed_targets": 0, "total_targets": 1}},
                    }
                ),
                encoding="utf-8",
            )
            rows = aggregate_runs.collect_runs(Path(tmp))
        self.assertEqual(len(rows), 1)
        self.assertTrue(rows[0]["valid"])
        self.assertFalse(rows[0]["passed"])

    def test_aggregate_keeps_warm_setup_failure_out_of_provider_setup_bucket(self) -> None:
        benchmark_budget = {
            "max_attempts": 1,
            "max_tool_calls": 80,
            "max_turns": None,
            "completion_token_budget": 32768,
        }
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp) / "run"
            run_dir.mkdir()
            (run_dir / "run.json").write_text(
                json.dumps(
                    {
                        "run_id": "warm-failure",
                        "harness_id": "default",
                        "model": "local",
                        "task_ref": "case/task",
                        "harness_status": "completed_with_failures",
                        "benchmark_budget": benchmark_budget,
                        "failure_counts": {"infra_dependency_warm_failed": 1},
                        "classification": {
                            "run_class": "INFRA_INVALID",
                            "reusable": False,
                        },
                        "verifier": {
                            "score": {"passed_targets": 0, "total_targets": 1}
                        },
                    }
                ),
                encoding="utf-8",
            )
            (run_dir / "harness-response.json").write_text(
                json.dumps(
                    {
                        "tasks": [
                            {
                                "task_ref": "case/task",
                                "status": "request_failed",
                                "failure_class": "infra_dependency_warm_failed",
                                "attempts": [],
                                "benchmark_budget": benchmark_budget,
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )

            rows = aggregate_runs.collect_runs(Path(tmp))

        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["final_class"], "INFRA_INVALID")
        self.assertFalse(rows[0]["reusable"])
        self.assertNotIn("provider setup error", rows[0]["validity_errors"])
        self.assertNotIn("benchmark budget does not match manifest", rows[0]["validity_errors"])

    def test_aggregate_uses_all_child_task_validity(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp) / "run"
            run_dir.mkdir()
            (run_dir / "run.json").write_text(
                json.dumps(
                    {
                        "run_id": "group-pass",
                        "harness_id": "default",
                        "model": "local",
                        "group_id": "case/group",
                        "harness_status": "completed",
                        "usage": {"requests": 2, "total_tokens": 123},
                        "verifier": {"score": {"passed_targets": 2, "total_targets": 2}},
                    }
                ),
                encoding="utf-8",
            )
            (run_dir / "harness-response.json").write_text(
                json.dumps(
                    {
                        "tasks": [
                            {"task_ref": "case/a", "status": "lean_passed", "validity": {"valid": True, "errors": []}},
                            {
                                "task_ref": "case/b",
                                "status": "lean_passed",
                                "validity": {"valid": False, "errors": ["completed model row has no request activity"]},
                            },
                        ]
                    }
                ),
                encoding="utf-8",
            )
            rows = aggregate_runs.collect_runs(Path(tmp))
        self.assertEqual(len(rows), 1)
        self.assertFalse(rows[0]["valid"])
        self.assertFalse(rows[0]["passed"])
        self.assertIn("case/b: completed model row has no request activity", rows[0]["validity_errors"])

    def test_badge_uses_valid_task_denominator(self) -> None:
        badge = aggregate_runs._badge(
            "benchmark",
            {
                "tasks": 3,
                "valid_tasks": 2,
                "passed": 2,
                "median_completion_tokens_to_pass": None,
            },
        )
        self.assertEqual(badge["message"], "2/2")
        self.assertEqual(badge["color"], "brightgreen")


if __name__ == "__main__":
    unittest.main()
