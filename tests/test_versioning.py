from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

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

    def test_interface_change_invalidates_that_task(self) -> None:
        newer = copy.deepcopy(self.version)
        newer["benchmark_version"] = "0.2"
        changed_ref = newer["tasks"][0]["task_ref"]
        newer["tasks"][0]["task_interface_id"] = "sha256:" + "4" * 64
        plan = plan_rerun(self.version, newer, model=self.complete_model, results_manifest=self.results)
        self.assertEqual(plan["rerun_count"], 1)
        self.assertEqual(plan["rerun"][0]["task_ref"], changed_ref)
        self.assertEqual(plan["rerun"][0]["reason"], "task_interface_id changed")


if __name__ == "__main__":
    unittest.main()
