from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from package_benchmark_release import filter_dirs_by_result_manifest, selected_run_ids_by_model


class ReleasePackagingPolicyTests(unittest.TestCase):
    def test_selected_run_ids_accept_run_id_or_artifact_id(self) -> None:
        manifest = {
            "models": [
                {
                    "model_id": "provider/model",
                    "task_results": [
                        {"task_ref": "case/task-a", "run_id": "run-a"},
                        {"task_ref": "case/task-b", "artifact_id": "run-b"},
                    ],
                }
            ]
        }
        self.assertEqual(selected_run_ids_by_model(manifest), {"provider/model": {"run-a", "run-b"}})

    def test_filter_fails_closed_when_selected_artifact_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            present = root / "run-a"
            present.mkdir()
            by_model = {"provider/model": [present]}
            manifest = {
                "models": [
                    {
                        "model_id": "provider/model",
                        "task_results": [
                            {"task_ref": "case/task-a", "run_id": "run-a"},
                            {"task_ref": "case/task-b", "run_id": "run-b"},
                        ],
                    }
                ]
            }

            filtered, errors = filter_dirs_by_result_manifest(by_model, manifest)

        self.assertEqual(filtered, {"provider/model": [present]})
        self.assertEqual(errors, ["provider/model: selected manifest run_id is missing from runs-dir: run-b"])

    def test_filter_omits_unselected_extra_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            selected = root / "run-selected"
            extra = root / "run-extra"
            selected.mkdir()
            extra.mkdir()
            by_model = {"provider/model": [extra, selected]}
            manifest = {
                "models": [
                    {
                        "model_id": "provider/model",
                        "task_results": [{"task_ref": "case/task", "run_id": "run-selected"}],
                    }
                ]
            }

            filtered, errors = filter_dirs_by_result_manifest(by_model, manifest)

        self.assertEqual(errors, [])
        self.assertEqual(filtered, {"provider/model": [selected]})


if __name__ == "__main__":
    unittest.main()
