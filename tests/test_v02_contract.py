from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.task_runner import aggregate_results, discover_task_refs
from scripts import generate_v02_contract as generator
from scripts import validate_v02_reference_contract as validator


ROOT = Path(__file__).resolve().parent.parent


class V02ContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads((ROOT / "benchmark-versions/v0.2.json").read_text())
        self.references = json.loads((ROOT / "benchmark-versions/v0.2-references.json").read_text())

    def _validate(self, mutate=None, *, lean=False, escape=False) -> tuple[int, dict]:
        manifest = json.loads(json.dumps(self.manifest))
        references = json.loads(json.dumps(self.references))
        # Unit fixtures are deliberately independent of CI's checkout depth.
        # The production validator still requires the recorded baseline object.
        manifest["source"]["commit"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip()
        manifest["source"]["selector_files_sha256"] = {
            path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in manifest["source"]["selector_files_sha256"]
        }
        if mutate:
            mutate(manifest, references)
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            directory = Path(directory)
            manifest_path = directory / "v0.2.json"
            reference_path = directory / "v0.2-references.json"
            audit_path = directory / "audit.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            references["canonical_manifest_sha256"] = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
            reference_path.write_text(json.dumps(references), encoding="utf-8")
            with mock.patch.object(validator, "MANIFEST", manifest_path), mock.patch.object(
                validator, "REFERENCES", reference_path
            ), mock.patch.object(
                validator,
                "baseline_file_sha",
                side_effect=lambda _commit, path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
            ), mock.patch.object(
                validator,
                "baseline_task_metadata",
                return_value={
                    task["task_ref"]: (task["task_fingerprint"], task["task_interface_id"])
                    for task in self.manifest["tasks"]
                },
            ), mock.patch.object(validator, "ESCAPE") as matcher:
                matcher.search.return_value = object() if escape else None
                if lean:
                    context = mock.patch.object(validator, "run_lean", return_value=(False, "declaration_check_failed"))
                else:
                    context = mock.patch.object(validator, "run_lean")
                with context:
                    code = validator.validate(verify_lean=lean, audit_path=audit_path)
            return code, json.loads(audit_path.read_text())

    def test_selector_is_frozen_and_operational(self) -> None:
        self.assertEqual(discover_task_refs("v0.2"), [task["task_ref"] for task in self.manifest["tasks"]])
        self.assertEqual(self.manifest["task_count"], 240)
        self.assertEqual(self.manifest["manifest_schema_version"], 1)
        self.assertTrue(all(task["task_fingerprint"].startswith("sha256:") for task in self.manifest["tasks"]))
        self.assertTrue(all(task["task_interface_id"].startswith("sha256:") for task in self.manifest["tasks"]))

    def test_implicit_v02_aggregate_has_only_canonical_cases(self) -> None:
        summary = aggregate_results([], "v0.2")["case_summary"]
        canonical_case_ids = {
            "/".join(task["task_ref"].split("/")[:2]) for task in self.manifest["tasks"]
        }
        self.assertEqual(summary["total_cases"], 37)
        self.assertEqual({row["case_id"] for row in summary["cases"]}, canonical_case_ids)

    def test_generator_rebuilds_the_pinned_baseline_contract(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            directory = Path(directory)
            manifest_path = directory / "v0.2.json"
            references_path = directory / "v0.2-references.json"
            with mock.patch.object(generator, "MANIFEST", manifest_path), mock.patch.object(
                generator, "REFERENCES", references_path
            ):
                self.assertEqual(generator.main(), 0)
            self.assertEqual(json.loads(manifest_path.read_text()), self.manifest)
            expected_references = json.loads(json.dumps(self.references))
            expected_references["canonical_manifest_path"] = str(manifest_path.relative_to(ROOT))
            expected_references["canonical_manifest_sha256"] = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
            self.assertEqual(json.loads(references_path.read_text()), expected_references)

    def test_duplicate_mapping_is_rejected(self) -> None:
        def mutate(manifest, _references):
            manifest["tasks"][1]["task_ref"] = manifest["tasks"][0]["task_ref"]

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("duplicate", audit["errors"][0])

    def test_task_manifest_hash_drift_is_rejected(self) -> None:
        def mutate(manifest, _references):
            manifest["task_manifest_sha256"][manifest["tasks"][0]["task_ref"]] = "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("task manifest hash drift", audit["errors"][0])

    def test_task_object_metadata_drift_is_rejected(self) -> None:
        def mutate(manifest, _references):
            manifest["tasks"][0].pop("task_fingerprint")

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("version task metadata malformed", audit["errors"][0])

    def test_task_object_metadata_value_drift_is_rejected(self) -> None:
        for field in ("task_fingerprint", "task_interface_id"):
            with self.subTest(field=field):
                def mutate(manifest, _references, field=field):
                    manifest["tasks"][0][field] = "sha256:" + "0" * 64

                code, audit = self._validate(mutate)
                self.assertEqual(code, 1)
                self.assertIn("pinned baseline task metadata drift", audit["errors"][0])

    def test_coordinated_mutable_task_metadata_drift_is_rejected_against_baseline(self) -> None:
        def mutate(manifest, references):
            for field in ("task_fingerprint", "task_interface_id"):
                manifest["tasks"][0][field] = "sha256:" + "0" * 64
                references["tasks"][0][field] = "sha256:" + "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("pinned baseline task metadata drift", audit["errors"][0])

    def test_future_all_suite_task_does_not_invalidate_frozen_v02(self) -> None:
        frozen_refs = [task["task_ref"] for task in self.manifest["tasks"]]

        def select(suite: str) -> list[str]:
            return frozen_refs + ["future/case/task"] if suite == "all" else frozen_refs

        with mock.patch.object(validator, "discover_task_refs", side_effect=select):
            code, audit = self._validate()
        self.assertEqual(code, 0)
        self.assertEqual(audit["errors"], [])

    def test_baseline_selector_hash_drift_is_rejected(self) -> None:
        def mutate(manifest, _references):
            manifest["source"]["selector_files_sha256"]["scripts/run_all.sh"] = "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("baseline selector source hash drift", audit["errors"][0])

    def test_malformed_reference_is_rejected(self) -> None:
        def mutate(_manifest, references):
            references["tasks"][0]["reference_module"] = "not/a/module"

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("malformed reference", audit["errors"][0])

    def test_unverifiable_reference_is_rejected_by_lean_result(self) -> None:
        code, audit = self._validate(lean=True)
        self.assertEqual(code, 1)
        self.assertIn("declaration_check_failed", audit["errors"][0])

    def test_forbidden_escape_is_rejected(self) -> None:
        code, audit = self._validate(escape=True)
        self.assertEqual(code, 1)
        self.assertIn("forbidden reference escape hatch", audit["errors"][0])

    def test_version_manifest_consumers_accept_canonical_task_objects(self) -> None:
        """Exercise the published consumers' real CLI parse/use paths for v0.2."""
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            directory = Path(directory)
            results = directory / "results.json"
            results.write_text(json.dumps({"models": []}), encoding="utf-8")
            plan = subprocess.run(
                [
                    sys.executable,
                    "scripts/plan_rerun.py",
                    "--from", "benchmark-versions/v0.2.json",
                    "--to", "benchmark-versions/v0.2.json",
                    "--model", "compatibility-fixture",
                    "--results-manifest", str(results),
                    "--format", "json",
                ],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=True,
            )
            self.assertEqual(json.loads(plan.stdout)["rerun_count"], 240)
            out = directory / "aggregate"
            aggregate = subprocess.run(
                [
                    sys.executable,
                    "scripts/aggregate_version.py",
                    "--version", "benchmark-versions/v0.2.json",
                    "--results-manifest", str(results),
                    "--out-dir", str(out),
                ],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=True,
            )
            self.assertIn("aggregated benchmark v0.2: 0 model row(s)", aggregate.stdout)
            self.assertEqual(json.loads((out / "results.json").read_text())["task_count"], 240)
