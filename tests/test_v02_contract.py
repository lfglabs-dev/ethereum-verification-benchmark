from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.task_runner import aggregate_results, discover_task_refs
from harness import canonical_contract
from scripts import generate_v02_contract as generator
from scripts import validate_v02_reference_contract as validator
from scripts import compute_fingerprints


ROOT = Path(__file__).resolve().parent.parent


class V02ContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads((ROOT / "benchmark-versions/v0.2.json").read_text())
        self.references = json.loads((ROOT / "benchmark-versions/v0.2-references.json").read_text())

    def _baseline_references(self) -> dict[str, dict[str, str]]:
        return {
            entry["task_ref"]: {
                field: entry[field]
                for field in ("reference_module", "reference_declaration", "reference_module_path", "reference_module_sha256")
            }
            for entry in self.references["tasks"]
        }

    def _validate(self, mutate=None, *, lean=False, escape=False, baseline=None, current=None, baseline_error=None) -> tuple[int, dict]:
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
            references["source_commit"] = manifest["source"]["commit"]
            reference_path.write_text(json.dumps(references), encoding="utf-8")
            with mock.patch.object(validator, "MANIFEST", manifest_path), mock.patch.object(
                validator, "REFERENCES", reference_path
            ), mock.patch.object(
                validator,
                "baseline_file_sha",
                side_effect=lambda _commit, path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
            ), mock.patch.object(
                compute_fingerprints,
                "baseline_contract_entries",
                side_effect=baseline_error,
                return_value=(
                    baseline if baseline is not None else {task["task_ref"]: task for task in self.manifest["tasks"]},
                    self._baseline_references(),
                ),
            ), mock.patch.object(
                compute_fingerprints,
                "task_entries",
                return_value=current if current is not None else {task["task_ref"]: task for task in self.manifest["tasks"]},
            ), mock.patch.object(validator, "ESCAPE") as matcher:
                matcher.search.return_value = object() if escape else None
                if lean:
                    context = mock.patch.object(validator, "run_lean", return_value=(False, "declaration_check_failed"))
                else:
                    context = mock.patch.object(validator, "run_lean")
                with context:
                    code = validator.validate(verify_lean=lean, audit_path=audit_path)
            return code, json.loads(audit_path.read_text())

    def _load_refs(self, mutate=None, *, baseline=None, current=None) -> None:
        manifest = json.loads(json.dumps(self.manifest))
        if mutate:
            mutate(manifest)
        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            path = Path(directory) / "v0.2.json"
            path.write_text(json.dumps(manifest), encoding="utf-8")
            metadata = baseline or {task["task_ref"]: task for task in self.manifest["tasks"]}
            current_metadata = current or metadata
            with mock.patch.object(canonical_contract, "CANONICAL_V02_PATH", path), mock.patch(
                "scripts.compute_fingerprints.baseline_task_entries", return_value=metadata
            ), mock.patch(
                "scripts.compute_fingerprints.task_entries", return_value=current_metadata
            ):
                return canonical_contract.load_v02_task_refs(require_pinned_source=True)

    def test_selector_is_frozen_and_operational(self) -> None:
        self.assertEqual(discover_task_refs("v0.2"), [task["task_ref"] for task in self.manifest["tasks"]])
        self.assertEqual(self.manifest["task_count"], 240)
        self.assertEqual(self.manifest["manifest_schema_version"], 1)
        self.assertTrue(all(task["task_fingerprint"].startswith("sha256:") for task in self.manifest["tasks"]))
        self.assertTrue(all(task["task_interface_id"].startswith("sha256:") for task in self.manifest["tasks"]))

    def test_source_archive_can_list_v02_without_git_history(self) -> None:
        """The frozen selector is usable by shallow checkouts/source archives."""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source"
            shutil.copytree(
                ROOT,
                source,
                ignore=shutil.ignore_patterns(".git", ".lake", "__pycache__", "artifacts", "tmp*"),
            )
            self.assertFalse((source / ".git").exists())
            listed = subprocess.run(
                [sys.executable, "harness/task_runner.py", "list", "--suite", "v0.2"],
                cwd=source,
                text=True,
                capture_output=True,
                check=True,
            )
        self.assertEqual(listed.stdout.splitlines(), [task["task_ref"] for task in self.manifest["tasks"]])

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
                self.assertIn("pinned baseline canonical task entry drift", audit["errors"][0])

    def test_canonical_selector_rejects_tampered_fingerprint_string(self) -> None:
        def mutate(manifest):
            manifest["tasks"][0]["task_fingerprint"] = "sha256:" + "0" * 64

        with self.assertRaisesRegex(ValueError, "canonical task entry drift"):
            self._load_refs(mutate)

    def test_canonical_selector_detects_source_drift_with_unchanged_yaml(self) -> None:
        current = {task["task_ref"]: json.loads(json.dumps(task)) for task in self.manifest["tasks"]}
        ref = self.manifest["tasks"][0]["task_ref"]
        # Model a Lean/source input changing while its task YAML mapping remains intact.
        current[ref]["task_fingerprint"] = "sha256:" + "1" * 64
        with self.assertRaisesRegex(ValueError, "source canonical entry drift"):
            self._load_refs(current=current)

    def test_canonical_selector_rejects_coordinated_mutable_self_comparison(self) -> None:
        def mutate(manifest):
            for field in ("task_fingerprint", "task_interface_id"):
                manifest["tasks"][0][field] = "sha256:" + "2" * 64

        # The immutable baseline metadata remains original, so a matching mutable
        # checkout cannot make this coordinated update pass.
        with self.assertRaisesRegex(ValueError, "canonical task entry drift"):
            mutable = {task["task_ref"]: json.loads(json.dumps(task)) for task in self.manifest["tasks"]}
            mutable[self.manifest["tasks"][0]["task_ref"]]["task_fingerprint"] = "sha256:" + "2" * 64
            mutable[self.manifest["tasks"][0]["task_ref"]]["task_interface_id"] = "sha256:" + "2" * 64
            self._load_refs(mutate, current=mutable)

    def test_coordinated_mutable_task_metadata_drift_is_rejected_against_baseline(self) -> None:
        def mutate(manifest, references):
            for field in ("task_fingerprint", "task_interface_id"):
                manifest["tasks"][0][field] = "sha256:" + "0" * 64
                references["tasks"][0][field] = "sha256:" + "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("pinned baseline canonical task entry drift", audit["errors"][0])

    def test_future_all_suite_task_does_not_invalidate_frozen_v02(self) -> None:
        frozen_refs = [task["task_ref"] for task in self.manifest["tasks"]]
        metadata = {task["task_ref"]: task for task in self.manifest["tasks"]}
        metadata["future/case/task"] = {"task_ref": "future/case/task"}

        code, audit = self._validate(current=metadata)
        self.assertEqual(code, 0)
        self.assertEqual(audit["errors"], [])

        self.assertEqual(self._load_refs(current=metadata), frozen_refs)

    def test_missing_frozen_current_task_fails_closed(self) -> None:
        metadata = {task["task_ref"]: task for task in self.manifest["tasks"]}
        metadata.pop(self.manifest["tasks"][0]["task_ref"])

        code, audit = self._validate(current=metadata)
        self.assertEqual(code, 1)
        self.assertIn("current frozen task missing", audit["errors"][0])
        with self.assertRaisesRegex(ValueError, "current frozen task missing"):
            self._load_refs(current=metadata)

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
        self.assertIn("pinned reference reference_module drift", audit["errors"][0])

    def test_regenerated_reference_hash_cannot_mask_changed_proof(self) -> None:
        def mutate(_manifest, references):
            references["tasks"][0]["reference_module_sha256"] = "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("pinned reference reference_module_sha256 drift", audit["errors"][0])

    def test_unavailable_pinned_source_is_infra_failure(self) -> None:
        code, audit = self._validate(baseline_error=ValueError("pinned source unavailable (infra): missing"))
        self.assertEqual(code, 1)
        self.assertIn("pinned source unavailable (infra)", audit["errors"][0])
        self.assertEqual(audit["classification"], "infra_unavailable")

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
