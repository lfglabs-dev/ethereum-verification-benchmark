import importlib.util
import hashlib
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

PATH = Path(__file__).parents[1] / "scripts" / "run_strat50.py"
SPEC = importlib.util.spec_from_file_location("run_strat50", PATH)
assert SPEC and SPEC.loader
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


def args(tmp_path: Path, **overrides):
    values = dict(
        panel=tmp_path / "panel.json",
        workdir=tmp_path,
        benchmark_head="head",
        benchmark_manifest=tmp_path / "manifest.json",
        models=["model-a"],
        output=tmp_path / "out",
        max_attempts=16,
        max_tool_calls=120,
        recovery_delay=0,
        infra_threshold=1,
        max_recovery_cycles=1,
        omit_stop_model=[],
        omit_sampling_model=[],
        reasoning_effort=[],
    )
    values.update(overrides)
    return type("Args", (), values)()


class RunStrat50Tests(unittest.TestCase):
    def test_benchmark_identity_records_manifest_and_rejects_unknown_tasks(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "v0.3.json"
            manifest.write_text(
                '{"benchmark_version":"0.3","git_sha":"head",'
                '"task_set_id":"tasks","environment_id":"env",'
                '"harness_id":"harness","tasks":[{"task_ref":"known"}]}\n'
            )
            canonical = {
                "0.3": {
                    "benchmark_head": "head",
                    "benchmark_manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
                    "panel_sha256": "panel",
                    "task_set_id": "tasks",
                    "environment_id": "env",
                    "harness_id": "harness",
                }
            }
            identity = RUNNER.benchmark_identity(
                manifest, "head", ["known"], canonical
            )
            self.assertEqual(identity["benchmark_version"], "0.3")
            self.assertEqual(identity["task_set_id"], "tasks")
            self.assertEqual(identity["canonical_panel_sha256"], "panel")
            with self.assertRaisesRegex(SystemExit, "absent"):
                RUNNER.benchmark_identity(manifest, "head", ["unknown"], canonical)
            with self.assertRaisesRegex(SystemExit, "not canonical"):
                RUNNER.benchmark_identity(manifest, "head", ["known"])

    def test_benchmark_identity_rejects_commit_mismatch(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "v0.3.json"
            manifest.write_text(
                '{"benchmark_version":"0.3","git_sha":"other",'
                '"task_set_id":"tasks","environment_id":"env",'
                '"harness_id":"harness","tasks":[]}\n'
            )
            with self.assertRaisesRegex(SystemExit, "commit mismatch"):
                RUNNER.benchmark_identity(manifest, "head", [])

    def test_panel_identity_accepts_canonical_expected_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            panel = Path(directory) / "panel.json"
            panel.write_text('["v0.3/task"]\n')
            expected = hashlib.sha256(panel.read_bytes()).hexdigest()
            self.assertEqual(RUNNER.validate_panel_identity(panel, expected), expected)

    def test_panel_identity_rejects_mismatch(self):
        with tempfile.TemporaryDirectory() as directory:
            panel = Path(directory) / "panel.json"
            panel.write_text('["v0.3/task"]\n')
            with self.assertRaisesRegex(SystemExit, "frozen STRAT-50 identity"):
                RUNNER.validate_panel_identity(panel, "0" * 64)

    def test_rejects_duplicate_models(self):
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            with mock.patch.object(RUNNER, "parse_args", return_value=args(tmp_path, models=["m", "m"])):
                with self.assertRaisesRegex(SystemExit, "duplicate"):
                    RUNNER.main()

    def test_rejects_non_p4_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            with mock.patch.object(RUNNER, "parse_args", return_value=args(tmp_path, max_attempts=15)):
                with self.assertRaisesRegex(SystemExit, "p4_normal"):
                    RUNNER.main()

    def test_rejects_dirty_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            with (
                mock.patch.object(RUNNER, "parse_args", return_value=args(tmp_path)),
                mock.patch.object(RUNNER.subprocess, "check_output", side_effect=["head\n", " M file\n"]),
            ):
                with self.assertRaisesRegex(SystemExit, "clean"):
                    RUNNER.main()

    def test_cohort_environment_filter_never_captures_secrets(self):
        with mock.patch.dict(os.environ, {"DEFAULT_HARNESS_STREAMING": "0", "DEFAULT_HARNESS_API_KEY": "must-not-be-recorded"}, clear=False):
            captured = {
                key: value
                for key, value in sorted(RUNNER.os.environ.items())
                if key.startswith("DEFAULT_HARNESS_")
                and not any(marker in key for marker in RUNNER.SECRET_ENV_MARKERS)
            }
        self.assertEqual(captured["DEFAULT_HARNESS_STREAMING"], "0")
        self.assertNotIn("DEFAULT_HARNESS_API_KEY", captured)


if __name__ == "__main__":
    unittest.main()
