from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from aggregate_version import aggregate, build_version_index, leaderboard_json, model_identity, public_model_identity, split_model_id
from compute_fingerprints import build_version_manifest
from plan_rerun import plan_rerun, result_key


class VersioningTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.version = json.loads((ROOT / "benchmark-versions" / "v0.1.json").read_text(encoding="utf-8"))
        cls.results = json.loads((ROOT / "results" / "manifests" / "v0.1.json").read_text(encoding="utf-8"))
        cls.complete_model = "kimi/kimi-for-coding"

    def test_fingerprints_are_stable_without_source_changes(self) -> None:
        first = build_version_manifest("0.1", created_at="2026-06-16")
        second = build_version_manifest("0.1", created_at="2026-06-16")
        self.assertEqual(first["task_set_id"], second["task_set_id"])
        self.assertEqual(first["harness_id"], second["harness_id"])
        self.assertEqual(first["environment_id"], second["environment_id"])
        self.assertEqual(
            [task["task_fingerprint"] for task in first["tasks"]],
            [task["task_fingerprint"] for task in second["tasks"]],
        )

    def test_changed_task_fingerprint_reruns_only_that_task(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        changed_ref = newer["tasks"][0]["task_ref"]
        newer["tasks"][0]["task_fingerprint"] = "sha256:" + "1" * 64
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["task_ref"], changed_ref)
        self.assertEqual(plan["rerun"][0]["reason"], "task_fingerprint changed")

    def test_harness_change_invalidates_all_tasks(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        newer["harness_id"] = "sha256:" + "2" * 64
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], self.version["task_count"])
        self.assertTrue(all(item["reason"] == "harness_id changed" for item in plan["rerun"]))

    def test_environment_change_can_be_allowed_explicitly(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        newer["environment_id"] = "sha256:" + "3" * 64
        blocked = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        allowed = plan_rerun(
            self.version,
            newer,
            model=self.complete_model,
            results_manifest=self.results,
            allow_env_compatible=True,
        )
        self.assertEqual(blocked["rerun_count"], self.version["task_count"])
        self.assertEqual(allowed["rerun_count"], 0)
        self.assertEqual(allowed["reuse_count"], self.version["task_count"])

    def test_metadata_only_change_reuses_result(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        newer["tasks"][0]["difficulty"] = "synthetic-new-label"
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], 0)
        self.assertEqual(plan["reuse_count"], self.version["task_count"])

    def test_zero_usage_result_is_not_reused(self) -> None:
        task = self.version["tasks"][0]
        model = "synthetic-zero"
        manifest = {
            "models": [
                {
                    "model_id": model,
                    "task_results": [
                        {
                            "task_ref": task["task_ref"],
                            "result_key": result_key(
                                model=model,
                                benchmark_version="0.1",
                                task_ref=task["task_ref"],
                                task_fingerprint=task["task_fingerprint"],
                                task_interface_id=task["task_interface_id"],
                                harness_id=self.version["harness_id"],
                                environment_id=self.version["environment_id"],
                                mode=self.version["mode"],
                                budget=self.version["budget"],
                            ),
                            "usage": {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0},
                            "verifier_output_present": True,
                            "artifact_status": "ok",
                        }
                    ],
                }
            ]
        }
        newer = copy.deepcopy(self.version)
        newer["tasks"] = [task]
        newer["task_count"] = 1
        plan = plan_rerun(self.version, newer, model=model, results_manifest=manifest)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["reason"], "zero usage")

    def test_explicit_zero_total_tokens_is_not_reused_even_with_component_usage(self) -> None:
        task = self.version["tasks"][0]
        model = "synthetic-zero-total"
        manifest = {
            "models": [
                {
                    "model_id": model,
                    "task_results": [
                        {
                            "task_ref": task["task_ref"],
                            "result_key": "synthetic-key",
                            "usage": {"prompt_tokens": 100, "completion_tokens": 20, "total_tokens": 0},
                            "verifier_output_present": True,
                            "artifact_status": "ok",
                        }
                    ],
                }
            ]
        }
        newer = copy.deepcopy(self.version)
        newer["tasks"] = [task]
        newer["task_count"] = 1
        plan = plan_rerun(self.version, newer, model=model, results_manifest=manifest)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["reason"], "zero usage")

    def test_completed_with_failures_result_is_reusable(self) -> None:
        task = self.version["tasks"][0]
        model = "synthetic-completed-with-failures"
        indexed_key = result_key(
            model=model,
            benchmark_version="0.1",
            task_ref=task["task_ref"],
            task_fingerprint=task["task_fingerprint"],
            task_interface_id=task["task_interface_id"],
            harness_id=self.version["harness_id"],
            environment_id=self.version["environment_id"],
            mode=self.version["mode"],
            budget=self.version["budget"],
        )
        manifest = {
            "models": [
                {
                    "model_id": model,
                    "task_results": [
                        {
                            "task_ref": task["task_ref"],
                            "result_key": indexed_key,
                            "task_fingerprint": task["task_fingerprint"],
                            "task_interface_id": task["task_interface_id"],
                            "usage": {"prompt_tokens": 100, "completion_tokens": 20, "total_tokens": 120},
                            "verifier_output_present": True,
                            "artifact_status": "ok",
                            "harness_status": "completed_with_failures",
                        }
                    ],
                }
            ]
        }
        newer = copy.deepcopy(self.version)
        newer["tasks"] = [task]
        newer["task_count"] = 1
        plan = plan_rerun(self.version, newer, model=model, results_manifest=manifest)
        self.assertEqual(plan["rerun_count"], 0)
        self.assertEqual(plan["reuse_count"], 1)

    def test_mode_change_invalidates_all_tasks(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        newer["mode"] = "synthetic-mode"
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], self.version["task_count"])
        self.assertTrue(all(item["reason"] == "mode changed" for item in plan["rerun"]))

    def test_budget_change_invalidates_all_tasks(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        newer["budget"] = "deep"
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], self.version["task_count"])
        self.assertTrue(all(item["reason"] == "budget changed" for item in plan["rerun"]))

    def test_stale_stored_fingerprint_is_not_reused(self) -> None:
        task = self.version["tasks"][0]
        model = "synthetic-stale-fingerprint"
        manifest = {
            "models": [
                {
                    "model_id": model,
                    "task_results": [
                        {
                            "task_ref": task["task_ref"],
                            "result_key": "synthetic-key",
                            "task_fingerprint": "sha256:" + "9" * 64,
                            "task_interface_id": task["task_interface_id"],
                            "usage": {"prompt_tokens": 100, "completion_tokens": 20, "total_tokens": 120},
                            "verifier_output_present": True,
                            "artifact_status": "ok",
                            "harness_status": "completed",
                        }
                    ],
                }
            ]
        }
        newer = copy.deepcopy(self.version)
        newer["tasks"] = [task]
        newer["task_count"] = 1
        plan = plan_rerun(self.version, newer, model=model, results_manifest=manifest)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["reason"], "stored task_fingerprint mismatch")

    def test_caveat_drift_is_not_reused(self) -> None:
        task = self.version["tasks"][0]
        model = "synthetic-caveat-drift"
        indexed_key = result_key(
            model=model,
            benchmark_version="0.1",
            task_ref=task["task_ref"],
            task_fingerprint=task["task_fingerprint"],
            task_interface_id=task["task_interface_id"],
            harness_id=self.version["harness_id"],
            environment_id=self.version["environment_id"],
            mode=self.version["mode"],
            budget=self.version["budget"],
            temperature_policy=None,
            provider_caveats=None,
        )
        manifest = {
            "models": [
                {
                    "model_id": model,
                    "caveats": ["provider downgraded mid-run"],
                    "task_results": [
                        {
                            "task_ref": task["task_ref"],
                            "result_key": indexed_key,
                            "task_fingerprint": task["task_fingerprint"],
                            "task_interface_id": task["task_interface_id"],
                            "usage": {"prompt_tokens": 100, "completion_tokens": 20, "total_tokens": 120},
                            "verifier_output_present": True,
                            "artifact_status": "ok",
                            "harness_status": "completed",
                        }
                    ],
                }
            ]
        }
        newer = copy.deepcopy(self.version)
        newer["tasks"] = [task]
        newer["task_count"] = 1
        plan = plan_rerun(self.version, newer, model=model, results_manifest=manifest)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["reason"], "stored result_key mismatch")

    def test_interface_change_invalidates_that_task(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        changed_ref = newer["tasks"][0]["task_ref"]
        newer["tasks"][0]["task_interface_id"] = "sha256:" + "4" * 64
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["task_ref"], changed_ref)
        self.assertEqual(plan["rerun"][0]["reason"], "task_interface_id changed")

    def test_summary_exposes_provider_and_model_for_website_consumers(self) -> None:
        summary = aggregate(self.version, self.results)
        by_id = {model["source_model_id"]: model for model in summary["models"]}
        self.assertEqual(by_id["kimi/kimi-for-coding"]["model_id"], "kimi/kimi-k2.7")
        self.assertEqual(by_id["kimi/kimi-for-coding"]["model_provider_id"], "kimi")
        self.assertEqual(by_id["kimi/kimi-for-coding"]["model_name"], "kimi-k2.7")
        self.assertEqual(by_id["kimi/kimi-for-coding"]["provider"], "kimi")
        self.assertEqual(by_id["kimi/kimi-for-coding"]["model"], "kimi-k2.7")
        self.assertEqual(by_id["kimi/kimi-for-coding"]["display_name"], "kimi-k2.7")
        self.assertEqual(by_id["openai-gpt-55"]["model_id"], "openai/gpt-5.5")
        self.assertEqual(by_id["openai-gpt-55"]["model_provider_id"], "openai")
        self.assertEqual(by_id["openai-gpt-55"]["model_name"], "gpt-5.5")
        self.assertEqual(by_id["openai-gpt-55"]["provider"], "openai")
        self.assertEqual(by_id["openai-gpt-55"]["model"], "gpt-5.5")
        self.assertEqual(by_id["openai-gpt-55"]["display_name"], "gpt-5.5")
        self.assertEqual(by_id["grok"]["provider"], "xai")
        self.assertEqual(by_id["grok"]["model"], "grok-build-0.1")
        self.assertEqual(by_id["grok"]["display_name"], "grok-build-0.1")

    def test_model_id_split_uses_known_prefixes_and_slashes(self) -> None:
        self.assertEqual(split_model_id("minimax/minimax-m3"), ("minimax", "minimax-m3"))
        self.assertEqual(split_model_id("claude-opus-4-8"), ("anthropic", "opus-4.8"))
        self.assertEqual(split_model_id("grok"), ("xai", "grok-build-0.1"))
        self.assertEqual(split_model_id("xai/grok-4.3"), ("xai", "grok-4.3"))
        self.assertEqual(split_model_id("custom-model"), ("unknown", "custom-model"))

    def test_public_model_identity_matches_website_labels(self) -> None:
        expected = {
            "openai-gpt-55": ("openai", "gpt-5.5", "gpt-5.5"),
            "zai/glm-5.2": ("zai", "glm-5.2", "glm-5.2"),
            "claude-opus-4-8": ("anthropic", "opus-4.8", "opus-4.8"),
            "grok": ("xai", "grok-build-0.1", "grok-build-0.1"),
            "minimax/minimax-m3": ("minimax", "minimax-m3", "minimax-m3"),
            "kimi/kimi-for-coding": ("kimi", "kimi-k2.7", "kimi-k2.7"),
            "xai/grok-4.3": ("xai", "grok-4.3", "grok-4.3"),
            "virtuals/deepseek-v4-flash": ("deepseek", "deepseek-v4-flash", "deepseek-v4-flash"),
            "virtuals/deepseek-v4-pro": ("deepseek", "deepseek-v4-pro", "deepseek-v4-pro"),
            "virtuals/xiaomi-mimo-v2-5": ("xiaomi", "mimo-v2.5", "mimo-v2.5"),
            "xiaomi-mimo-v2-5": ("xiaomi", "mimo-v2.5", "mimo-v2.5"),
        }
        for model_id, identity in expected.items():
            with self.subTest(model_id=model_id):
                self.assertEqual(public_model_identity(model_id), identity)

    def test_model_identity_keeps_inference_provider_separate(self) -> None:
        identity = model_identity("virtuals/deepseek-v4-flash")
        self.assertEqual(identity["model_id"], "deepseek/deepseek-v4-flash")
        self.assertEqual(identity["model_provider_id"], "deepseek")
        self.assertEqual(identity["model_name"], "deepseek-v4-flash")
        self.assertEqual(identity["inference_provider_id"], "virtuals")
        self.assertEqual(identity["inference_model_id"], "virtuals/deepseek-v4-flash")
        self.assertEqual(identity["source_model_id"], "virtuals/deepseek-v4-flash")

    def test_version_index_points_to_summary_and_manifest(self) -> None:
        summary = aggregate(self.version, self.results)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            (out / "results" / "summaries").mkdir(parents=True)
            index = build_version_index(out, latest_version="0.1", current_summary=summary)
        self.assertEqual(index["latest_version"], "0.1")
        self.assertEqual(index["versions"][0]["benchmark_version"], "0.1")
        self.assertEqual(index["versions"][0]["leaderboard_url"], "results/leaderboards/v0.1.json")
        self.assertEqual(index["versions"][0]["summary_url"], "results/summaries/v0.1.json")
        self.assertEqual(index["versions"][0]["manifest_url"], "results/manifests/v0.1.json")

    def test_leaderboard_json_is_minimal_website_table_with_tokens(self) -> None:
        summary = aggregate(self.version, self.results)
        leaderboard = leaderboard_json(summary)
        self.assertEqual(leaderboard["benchmark_version"], "0.1")
        self.assertEqual(leaderboard["source_summary_url"], "results/summaries/v0.1.json")
        self.assertEqual(leaderboard["source_manifest_url"], "results/manifests/v0.1.json")

        by_source_id = {row["source_model_id"]: row for row in leaderboard["rows"]}
        minimax = by_source_id["minimax/minimax-m3"]
        self.assertEqual(minimax["model_id"], "minimax/minimax-m3")
        self.assertEqual(minimax["model_provider_id"], "minimax")
        self.assertEqual(minimax["model_name"], "minimax-m3")
        self.assertEqual(minimax["inference_provider_id"], "minimax")
        self.assertEqual(minimax["inference_model_id"], "minimax/minimax-m3")
        self.assertEqual(minimax["provider_id"], "minimax")
        self.assertEqual(minimax["provider_model_id"], "minimax-m3")
        self.assertEqual(minimax["display_name"], "minimax-m3")
        self.assertIn("total_tokens", minimax)
        self.assertIn("avg_total_tokens_per_task", minimax)
        self.assertEqual(minimax["total"], minimax["passed"] + minimax["failed"])

        openai = by_source_id["openai-gpt-55"]
        self.assertEqual(openai["model_id"], "openai/gpt-5.5")
        self.assertEqual(openai["model_provider_id"], "openai")
        self.assertEqual(openai["model_name"], "gpt-5.5")
        self.assertEqual(openai["provider_id"], "openai")
        self.assertEqual(openai["provider_model_id"], "gpt-5.5")
        self.assertEqual(openai["display_name"], "gpt-5.5")

        deepseek = by_source_id["virtuals/deepseek-v4-flash"]
        self.assertEqual(deepseek["model_id"], "deepseek/deepseek-v4-flash")
        self.assertEqual(deepseek["model_provider_id"], "deepseek")
        self.assertEqual(deepseek["model_name"], "deepseek-v4-flash")
        self.assertEqual(deepseek["inference_provider_id"], "virtuals")
        self.assertEqual(deepseek["inference_model_id"], "virtuals/deepseek-v4-flash")
        self.assertEqual(deepseek["provider_id"], "deepseek")
        self.assertEqual(deepseek["provider_model_id"], "deepseek-v4-flash")

        xiaomi = by_source_id["virtuals/xiaomi-mimo-v2-5"]
        self.assertEqual(xiaomi["model_id"], "xiaomi/mimo-v2.5")
        self.assertEqual(xiaomi["model_provider_id"], "xiaomi")
        self.assertEqual(xiaomi["model_name"], "mimo-v2.5")
        self.assertEqual(xiaomi["inference_provider_id"], "virtuals")
        self.assertEqual(xiaomi["inference_model_id"], "virtuals/xiaomi-mimo-v2-5")
        self.assertEqual(xiaomi["provider_id"], "xiaomi")
        self.assertEqual(xiaomi["provider_model_id"], "mimo-v2.5")
        self.assertEqual(xiaomi["display_name"], "mimo-v2.5")

        complete_rows = [row for row in leaderboard["rows"] if row["status"] == "complete"]
        self.assertTrue(all(isinstance(row["rank"], int) for row in complete_rows))
        self.assertTrue(all(row["rank"] is None for row in leaderboard["rows"] if row["status"] != "complete"))


if __name__ == "__main__":
    unittest.main()
