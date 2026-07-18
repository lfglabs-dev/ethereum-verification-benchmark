from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness.task_runner import discover_task_refs
from scripts import validate_v02_reference_contract as validator


ROOT = Path(__file__).resolve().parent.parent


class V02ContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads((ROOT / "benchmark-versions/v0.2.json").read_text())
        self.references = json.loads((ROOT / "benchmark-versions/v0.2-references.json").read_text())

    def _validate(self, mutate=None, *, lean=False, escape=False) -> tuple[int, dict]:
        manifest = json.loads(json.dumps(self.manifest))
        references = json.loads(json.dumps(self.references))
        if mutate:
            mutate(manifest, references)
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            manifest_path = directory / "v0.2.json"
            reference_path = directory / "v0.2-references.json"
            audit_path = directory / "audit.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            references["canonical_manifest_sha256"] = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
            reference_path.write_text(json.dumps(references), encoding="utf-8")
            with mock.patch.object(validator, "MANIFEST", manifest_path), mock.patch.object(
                validator, "REFERENCES", reference_path
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
        self.assertEqual(discover_task_refs("v0.2"), self.manifest["tasks"])
        self.assertEqual(self.manifest["task_count"], 240)

    def test_duplicate_mapping_is_rejected(self) -> None:
        def mutate(manifest, _references):
            manifest["tasks"][1] = manifest["tasks"][0]

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("duplicate", audit["errors"][0])

    def test_task_manifest_hash_drift_is_rejected(self) -> None:
        def mutate(manifest, _references):
            manifest["task_manifest_sha256"][manifest["tasks"][0]] = "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("task manifest hash drift", audit["errors"][0])

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
