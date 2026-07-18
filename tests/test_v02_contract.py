from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import nullcontext
from pathlib import Path
from unittest import mock

from harness.task_runner import aggregate_results, discover_task_refs
from harness import canonical_contract, task_runner
from scripts import generate_v02_contract as generator
from scripts import validate_v02_reference_contract as validator
from scripts import compute_fingerprints


ROOT = Path(__file__).resolve().parent.parent


def trusted_closure_functions():
    """Exercise the helper only through the production trust boundary."""
    namespace = compute_fingerprints.trusted_closure_helper_namespace()
    return namespace["collect_reference_closure"], namespace["module_path"]


class V02ContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads((ROOT / "benchmark-versions/v0.2.json").read_text())
        self.references = json.loads((ROOT / "benchmark-versions/v0.2-references.json").read_text())

    def _baseline_references(self) -> dict[str, dict[str, str]]:
        return {
            entry["task_ref"]: {
                field: entry[field]
                for field in ("reference_module", "reference_declaration", "reference_module_path", "reference_module_sha256", "reference_import_closure")
            }
            for entry in self.references["tasks"]
        }

    def _baseline_version_metadata(self) -> dict[str, object]:
        """The immutable pinned-source result used by the structural fixtures."""
        return {
            key: value
            for key, value in self.manifest.items()
            if key
            in {
                "benchmark",
                "benchmark_version",
                "created_at",
                "git_sha",
                "manifest_schema_version",
                "task_count",
                "task_set_id",
                "harness_id",
                "environment_id",
                "mode",
                "budget",
            }
        }

    def _validate(
        self,
        mutate=None,
        *,
        lean=False,
        escape: bool | None = None,
        baseline=None,
        current=None,
        baseline_error=None,
        forbid_baseline_or_task_work: bool = False,
    ) -> tuple[int, dict]:
        manifest = json.loads(json.dumps(self.manifest))
        references = json.loads(json.dumps(self.references))
        # Fixtures use a synthetic reviewed root matching this checkout; Git
        # reads below are mocked so they remain independent of checkout depth.
        manifest["source"]["commit"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip()
        manifest["source"]["selector_files_sha256"] = {
            path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in manifest["source"]["selector_files_sha256"]
        }
        pinned_commit = manifest["source"]["commit"]
        references["source_commit"] = pinned_commit
        fixture_source = json.loads(json.dumps(manifest["source"]))
        if mutate:
            mutate(manifest, references)
        def forbidden_work(*_args, **_kwargs):
            raise AssertionError("candidate source drift reached baseline or task work")

        with tempfile.TemporaryDirectory(dir=ROOT) as directory:
            directory = Path(directory)
            manifest_path = directory / "v0.2.json"
            reference_path = directory / "v0.2-references.json"
            audit_path = directory / "audit.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            references["canonical_manifest_path"] = str(manifest_path.relative_to(ROOT))
            references["canonical_manifest_sha256"] = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
            reference_path.write_text(json.dumps(references), encoding="utf-8")
            with mock.patch.object(validator, "MANIFEST", manifest_path), mock.patch.object(
                validator, "REFERENCES", reference_path
            ), mock.patch.object(validator, "RELEASE_SOURCE", fixture_source), mock.patch.object(
                validator, "BASELINE_COMMIT", pinned_commit
            ), mock.patch.object(
                validator,
                "baseline_file_sha",
                side_effect=(
                    forbidden_work
                    if forbid_baseline_or_task_work
                    else lambda _commit, path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                ),
            ), mock.patch.object(
                compute_fingerprints,
                "baseline_contract_entries",
                side_effect=forbidden_work if forbid_baseline_or_task_work else baseline_error,
                return_value=None
                if forbid_baseline_or_task_work or baseline_error is not None
                else (
                    baseline if baseline is not None else {task["task_ref"]: task for task in self.manifest["tasks"]},
                    self._baseline_references(),
                ),
            ), mock.patch.object(
                compute_fingerprints,
                "task_entries",
                side_effect=forbidden_work if forbid_baseline_or_task_work else None,
                return_value=None
                if forbid_baseline_or_task_work
                else current if current is not None else {task["task_ref"]: task for task in self.manifest["tasks"]},
            ), mock.patch.object(
                validator,
                "baseline_version_metadata",
                side_effect=forbidden_work if forbid_baseline_or_task_work else None,
                return_value=None if forbid_baseline_or_task_work else self._baseline_version_metadata(),
            ), (mock.patch.object(validator, "ESCAPE") if escape is not None else nullcontext()) as matcher:
                if matcher is not None:
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
        closure_records = [member for task in self.references["tasks"] for member in task["reference_import_closure"]]
        self.assertEqual(len(closure_records), 241)
        self.assertEqual(len({member["module"] for member in closure_records}), 38)

    def test_mutable_full_selector_includes_later_task_while_v02_stays_240(self) -> None:
        """A post-release task belongs to ``all``, never to frozen v0.2."""
        frozen_refs = [task["task_ref"] for task in self.manifest["tasks"]]
        future_ref = "future/case/later_task"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for task_ref in [*frozen_refs, future_ref]:
                project, case, task = task_ref.split("/")
                task_path = root / ("backlog" if task_ref == future_ref else "cases") / project / case / "tasks" / f"{task}.yaml"
                task_path.parent.mkdir(parents=True, exist_ok=True)
                task_path.write_text("task_id: placeholder\n", encoding="utf-8")

            with mock.patch.object(task_runner, "ROOT", root), mock.patch.object(
                task_runner, "load_v02_task_refs", return_value=frozen_refs
            ), mock.patch.object(task_runner, "load_task_record", return_value={}):
                self.assertIn(future_ref, task_runner.discover_task_refs("all"))
                self.assertEqual(task_runner.discover_task_refs("v0.2"), frozen_refs)
                self.assertEqual(len(task_runner.discover_task_refs("v0.2")), 240)

    def test_run_all_defaults_to_mutable_selector_and_exposes_v02_flag(self) -> None:
        runner = (ROOT / "scripts/run_all.sh").read_text(encoding="utf-8")
        self.assertIn('suite="all"', runner)
        self.assertIn('"--suite" && "$2" == "v0.2"', runner)
        self.assertIn('list --suite "$suite"', runner)

    def test_source_archive_v02_list_fails_closed_without_pinned_source(self) -> None:
        """Scored frozen selection never falls back to mutable self-validation."""
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
            )
        self.assertNotEqual(listed.returncode, 0)
        self.assertIn("pinned source unavailable", listed.stderr)

    def test_reference_closure_is_case_local_cycle_safe_and_path_contained(self) -> None:
        collect_reference_closure, _ = trusted_closure_functions()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "Benchmark/Cases/Example/Case"
            case.mkdir(parents=True)
            (case / "Proofs.lean").write_text("import Benchmark.Cases.Example.Case.HelperProof\n", encoding="utf-8")
            (case / "HelperProof.lean").write_text("import Benchmark.Cases.Example.Case.Proofs\n", encoding="utf-8")
            closure = collect_reference_closure(root, "Benchmark.Cases.Example.Case.Proofs")
            self.assertEqual([member["path"] for member in closure], [
                "Benchmark/Cases/Example/Case/HelperProof.lean",
                "Benchmark/Cases/Example/Case/Proofs.lean",
            ])
            (case / "Proofs.lean").write_text("import ../outside\n", encoding="utf-8")
            self.assertEqual(collect_reference_closure(root, "Benchmark.Cases.Example.Case.Proofs"), [
                {"module": "Benchmark.Cases.Example.Case.Proofs", "path": "Benchmark/Cases/Example/Case/Proofs.lean", "sha256": hashlib.sha256((case / "Proofs.lean").read_bytes()).hexdigest()},
            ])

    def test_reference_closure_rejects_missing_helper_and_path_escape(self) -> None:
        collect_reference_closure, module_path = trusted_closure_functions()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "Benchmark/Cases/Example/Case"
            case.mkdir(parents=True)
            (case / "Proofs.lean").write_text("import Benchmark.Cases.Example.Case.HelperProof\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "helper missing"):
                collect_reference_closure(root, "Benchmark.Cases.Example.Case.Proofs")
            with self.assertRaisesRegex(ValueError, "malformed Lean import"):
                module_path(root, "Benchmark.Cases.Example.Case...outside")

    def test_malicious_candidate_helper_cannot_execute_during_validation(self) -> None:
        """Validation rejects mutable helper bytes before their top-level code runs."""
        helper = ROOT / "scripts/v02_reference_closure.py"
        original = helper.read_bytes()
        cases = {
            "exit": b"import sys\nsys.exit(1)\n",
            "monkeypatch": b"import hashlib, subprocess\nhashlib.sha256 = lambda *_: None\nsubprocess.run = lambda *_a, **_k: None\n",
            "file-write": b"from pathlib import Path\nPath('candidate-helper-sentinel').write_text('executed')\n",
        }
        try:
            for name, payload in cases.items():
                with self.subTest(name=name):
                    sentinel = ROOT / "candidate-helper-sentinel"
                    sentinel.unlink(missing_ok=True)
                    helper.write_bytes(payload)
                    with tempfile.TemporaryDirectory(dir=ROOT) as directory:
                        audit = Path(directory) / "audit.json"
                        result = subprocess.run(
                            [sys.executable, "scripts/validate_v02_reference_contract.py", "--no-lean", "--audit", str(audit)],
                            cwd=ROOT,
                            text=True,
                            capture_output=True,
                        )
                        self.assertEqual(result.returncode, 1, result.stderr)
                        self.assertTrue(audit.is_file(), result.stderr)
                        self.assertIn("trusted closure helper digest drift", json.loads(audit.read_text())["errors"][0])
                    self.assertFalse(sentinel.exists(), name)
        finally:
            helper.write_bytes(original)
            (ROOT / "candidate-helper-sentinel").unlink(missing_ok=True)

    def test_baseline_recomputation_rejects_mutable_closure_helper(self) -> None:
        """A regenerated contract cannot redefine the closure boundary."""
        helper = ROOT / "scripts/v02_reference_closure.py"
        original = helper.read_bytes()
        try:
            helper.write_bytes(original + b"\n# coordinated candidate tampering\n")
            with self.assertRaisesRegex(ValueError, "trusted closure helper.*drift"):
                compute_fingerprints.trusted_closure_helper_source()
        finally:
            helper.write_bytes(original)

    def test_coordinated_helper_and_contract_regeneration_is_rejected(self) -> None:
        """Changing both the helper and its advertised manifest data cannot pass."""
        helper = ROOT / "scripts/v02_reference_closure.py"
        original = helper.read_bytes()
        try:
            helper.write_bytes(original + b"\n# coordinated candidate tampering\n")
            with tempfile.TemporaryDirectory(dir=ROOT) as directory:
                directory = Path(directory)
                with mock.patch.object(generator, "MANIFEST", directory / "v0.2.json"), mock.patch.object(
                    generator, "REFERENCES", directory / "v0.2-references.json"
                ):
                    with self.assertRaisesRegex(ValueError, "trusted closure helper.*drift"):
                        generator.main()
            code, audit = self._validate()
        finally:
            helper.write_bytes(original)
        self.assertEqual(code, 1)
        self.assertIn("trusted closure helper digest drift", audit["errors"][0])

    def test_baseline_recomputation_rejects_missing_closure_helper(self) -> None:
        helper = ROOT / "scripts/v02_reference_closure.py"
        original = helper.read_bytes()
        try:
            helper.unlink()
            with self.assertRaisesRegex(ValueError, "trusted closure helper.*missing"):
                compute_fingerprints.trusted_closure_helper_source()
        finally:
            helper.write_bytes(original)

    def test_baseline_recomputation_fails_closed_for_missing_trusted_helper_blob(self) -> None:
        missing_blob = "0" * 40
        with mock.patch.object(compute_fingerprints, "TRUSTED_CLOSURE_HELPER_BLOB", missing_blob):
            with self.assertRaisesRegex(ValueError, "trusted closure helper blob is not reachable"):
                compute_fingerprints.trusted_closure_helper_source()

    def test_trusted_helper_survives_squash_equivalent_bare_shallow_clone(self) -> None:
        """Only final-tree blobs, never an intermediate PR commit, are required."""
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            source = directory / "squash-source"
            bare = directory / "final-tree.git"
            shallow = directory / "shallow"
            source.mkdir()
            with (directory / "tree.tar").open("wb") as archive:
                subprocess.run(["git", "archive", "--format=tar", "HEAD"], cwd=ROOT, check=True, stdout=archive)
            # The archive has no history; committing it once models a squash
            # merge whose bare remote is then fetched at depth one.
            subprocess.run(["tar", "-xf", str(directory / "tree.tar"), "-C", str(source)], check=True)
            subprocess.run(["git", "init"], cwd=source, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.email", "tests@example.invalid"], cwd=source, check=True)
            subprocess.run(["git", "config", "user.name", "tests"], cwd=source, check=True)
            subprocess.run(["git", "add", "."], cwd=source, check=True)
            subprocess.run(["git", "commit", "-m", "squash equivalent"], cwd=source, check=True, capture_output=True)
            subprocess.run(["git", "clone", "--bare", str(source), str(bare)], check=True, capture_output=True)
            subprocess.run(["git", "clone", "--depth", "1", "--no-local", bare.as_uri(), str(shallow)], check=True, capture_output=True)
            self.assertNotEqual(
                subprocess.run(["git", "cat-file", "-e", "14ec558d0afb9adcf97efd2706eb5b0827fb961d^{commit}"], cwd=shallow, capture_output=True).returncode,
                0,
            )
            completed = subprocess.run(
                [sys.executable, "-c", "from scripts.compute_fingerprints import trusted_closure_helper_source; print(len(trusted_closure_helper_source()))"],
                cwd=shallow,
                text=True,
                capture_output=True,
                check=True,
            )
            self.assertGreater(int(completed.stdout), 0)

    def test_transitive_helper_mutation_and_axiom_are_rejected(self) -> None:
        wildcat = next(entry for entry in self.references["tasks"] if entry["task_ref"] == "wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity")
        helper = ROOT / "Benchmark/Cases/Wildcat/BorrowLiquiditySafety/Slot0Proof.lean"
        self.assertIn(str(helper.relative_to(ROOT)), [member["path"] for member in wildcat["reference_import_closure"]])
        original = helper.read_text(encoding="utf-8")
        try:
            helper.write_text(original + "\naxiom injected_helper_escape : True\n", encoding="utf-8")
            code, audit = self._validate()
        finally:
            helper.write_text(original, encoding="utf-8")
        self.assertEqual(code, 1)
        self.assertIn("forbidden reference escape hatch", audit["errors"][0])

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

    def test_checked_in_reference_contract_hashes_the_frozen_manifest(self) -> None:
        """The checked-in contract must track its immutable manifest, not a stale regeneration."""
        self.assertEqual(
            self.references["canonical_manifest_sha256"],
            hashlib.sha256((ROOT / "benchmark-versions/v0.2.json").read_bytes()).hexdigest(),
        )

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

    def test_canonical_selector_rejects_coordinated_source_commit_regeneration(self) -> None:
        """Candidate JSON cannot redirect the frozen baseline to a reachable commit."""
        def mutate(manifest):
            manifest["source"]["commit"] = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
            ).strip()

        with self.assertRaisesRegex(ValueError, "release trust-root source drift"):
            self._load_refs(mutate)

    def test_coordinated_task_and_reference_manifest_regeneration_cannot_retarget_source(self) -> None:
        """Regenerating both candidate contracts cannot select another reachable commit."""
        original = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        helper_path = self.manifest["source"]["closure_helper"]["path"]
        reachable = subprocess.check_output(["git", "rev-list", original], cwd=ROOT, text=True).splitlines()
        alternate = next(
            (
                commit
                for commit in reachable
                if commit != original
                and subprocess.run(
                    ["git", "cat-file", "-e", f"{commit}:{helper_path}"], cwd=ROOT, check=False
                ).returncode
                == 0
            ),
            None,
        )
        self.assertIsNotNone(alternate, "expected a reachable commit containing the closure helper")
        assert alternate is not None
        self.assertNotEqual(alternate, original)
        self.assertEqual(
            subprocess.run(
                ["git", "cat-file", "-e", f"{alternate}:{helper_path}"], cwd=ROOT, check=False
            ).returncode,
            0,
        )

        def mutate(manifest, references):
            manifest["source"]["commit"] = alternate
            manifest["source"]["selector_files_sha256"] = {
                path: hashlib.sha256(
                    subprocess.check_output(["git", "show", f"{alternate}:{path}"], cwd=ROOT)
                ).hexdigest()
                for path in manifest["source"]["selector_files_sha256"]
            }
            manifest["source"]["closure_helper"] = {
                "blob": subprocess.check_output(
                    ["git", "rev-parse", f"{alternate}:{helper_path}"], cwd=ROOT, text=True
                ).strip(),
                "path": helper_path,
                "sha256": hashlib.sha256(
                    subprocess.check_output(["git", "show", f"{alternate}:{helper_path}"], cwd=ROOT)
                ).hexdigest(),
            }
            references["source_commit"] = alternate
            # ``_validate`` recomputes the reference manifest hash after this
            # mutation.  Task inputs remain unchanged: the only attempted
            # change is selecting a different reachable baseline.

        code, audit = self._validate(mutate, forbid_baseline_or_task_work=True)
        self.assertEqual(code, 1)
        self.assertIn("release trust-root source provenance drift", audit["errors"][0])

    def test_coordinated_mutable_task_metadata_drift_is_rejected_against_baseline(self) -> None:
        def mutate(manifest, references):
            for field in ("task_fingerprint", "task_interface_id"):
                manifest["tasks"][0][field] = "sha256:" + "0" * 64
                references["tasks"][0][field] = "sha256:" + "0" * 64

        code, audit = self._validate(mutate)
        self.assertEqual(code, 1)
        self.assertIn("pinned baseline canonical task entry drift", audit["errors"][0])

    def test_coordinated_version_metadata_drift_is_rejected_against_baseline(self) -> None:
        # Regenerating the mutable reference hash must not make a changed release
        # identity self-authenticating.  Every build_version_manifest field is
        # pinned to the source revision used to freeze v0.2.
        for field, value in self._baseline_version_metadata().items():
            with self.subTest(field=field):
                def mutate(manifest, _references, field=field, value=value):
                    manifest[field] = "tampered" if isinstance(value, str) else value + 1

                code, audit = self._validate(mutate)
                self.assertEqual(code, 1)
                self.assertIn("release trust-root version metadata drift", audit["errors"][0])

    def test_coordinated_source_provenance_drift_is_rejected_against_baseline(self) -> None:
        for field in ("commit", "entrypoint", "selector_command", "selector_files_sha256", "closure_helper"):
            with self.subTest(field=field):
                def mutate(manifest, _references, field=field):
                    if field in ("selector_files_sha256", "closure_helper"):
                        manifest["source"][field] = {"tampered": "0" * 64}
                    else:
                        manifest["source"][field] = "tampered"

                code, audit = self._validate(mutate)
                self.assertEqual(code, 1)
                self.assertIn("release trust-root source provenance drift", audit["errors"][0])

    def test_coordinated_reference_metadata_drift_is_rejected_against_baseline(self) -> None:
        fields = (
            "benchmark",
            "benchmark_version",
            "contract_kind",
            "schema_version",
            "source_commit",
            "task_count",
            "task_set_sha256",
        )
        for field in fields:
            with self.subTest(field=field):
                def mutate(_manifest, references, field=field):
                    value = references[field]
                    references[field] = "tampered" if isinstance(value, str) else value + 1

                code, audit = self._validate(mutate)
                self.assertEqual(code, 1)
                self.assertIn("pinned baseline reference metadata drift", audit["errors"][0])

    def test_environment_identity_is_frozen_for_v02_but_recomputed_for_new_versions(self) -> None:
        # A dependency update changes a newly generated version's environment ID;
        # it must not rewrite the frozen v0.2 release identity.
        with mock.patch.object(compute_fingerprints, "environment_id", return_value="sha256:" + "e" * 64):
            newer = compute_fingerprints.build_version_manifest("0.3", suite="all")
        self.assertEqual(newer["environment_id"], "sha256:" + "e" * 64)
        self.assertNotEqual(newer["environment_id"], self.manifest["environment_id"])

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
        self.assertIn("release trust-root source provenance drift", audit["errors"][0])

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

    def test_invalid_candidate_json_always_records_audit_and_fails_preflight(self) -> None:
        cases = (
            ("missing manifest", "manifest", None),
            ("missing reference contract", "references", None),
            ("malformed manifest", "manifest", "{"),
            ("malformed reference contract", "references", "{"),
        )
        for label, target, contents in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory(dir=ROOT) as directory:
                directory = Path(directory)
                manifest = directory / "v0.2.json"
                references = directory / "v0.2-references.json"
                audit = directory / "audit.json"
                if target != "manifest":
                    manifest.write_text(json.dumps(self.manifest), encoding="utf-8")
                elif contents is not None:
                    manifest.write_text(contents, encoding="utf-8")
                if target != "references":
                    references.write_text(json.dumps(self.references), encoding="utf-8")
                elif contents is not None:
                    references.write_text(contents, encoding="utf-8")
                with mock.patch.object(validator, "MANIFEST", manifest), mock.patch.object(
                    validator, "REFERENCES", references
                ), mock.patch.object(validator, "run_lean") as run_lean:
                    self.assertEqual(validator.validate(verify_lean=False, audit_path=audit), 1)
                    recorded = json.loads(audit.read_text(encoding="utf-8"))
                    self.assertTrue(recorded["errors"])
                    if contents is None:
                        self.assertIsNone(
                            recorded["manifest_sha256" if target == "manifest" else "reference_contract_sha256"]
                        )
                    with self.assertRaisesRegex(ValueError, "v0.2 reference preflight failed"):
                        validator.ensure_structural_contract()
                run_lean.assert_not_called()

    def test_unwritable_audit_path_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            audit_parent = Path(directory) / "not-a-directory"
            audit_parent.write_text("block audit directory", encoding="utf-8")
            with mock.patch.object(validator, "run_lean") as run_lean:
                self.assertEqual(validator.validate(verify_lean=False, audit_path=audit_parent / "audit.json"), 1)
            run_lean.assert_not_called()

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
