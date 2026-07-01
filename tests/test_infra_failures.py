from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import classify_failures
from classify_failures import classify_runs_dir, load_taxonomy
from infra_failures import provider_failure_reason, transport_failure_summary
from plan_rerun import reusable_result
from recover_version_results import build_model_entry

MODEL = "openai-gpt-55-pro"


def _write(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def _make_run_dir(
    root: Path,
    task_ref: str,
    *,
    points_earned: int,
    verifier_status: str,
    harness_task_status: str,
    failure_class: str | None,
    conv_records: list[dict[str, object]],
    harness_status: str = "completed",
) -> dict[str, object]:
    run_id = task_ref.replace("/", "__")
    run_dir = root / run_id
    verifier = {
        "score": {"points_earned": points_earned, "points_possible": 1},
        "targets": [{"task_ref": task_ref, "status": verifier_status, "output": ""}],
    }
    run = {
        "run_id": run_id,
        "model": MODEL,
        "task_ref": task_ref,
        "harness_status": harness_status,
        "usage": {"completion_tokens": 10, "prompt_tokens": 100, "requests": 3, "total_tokens": 110},
        "verifier": verifier,
    }
    _write(run_dir / "run.json", run)
    task_entry: dict[str, object] = {"task_ref": task_ref, "status": harness_task_status}
    if failure_class is not None:
        task_entry["failure_class"] = failure_class
    _write(run_dir / "harness-response.json", {"status": harness_status, "tasks": [task_entry]})
    conv = run_dir / "conversations" / f"{run_id}.jsonl"
    conv.parent.mkdir(parents=True, exist_ok=True)
    conv.write_text("\n".join(json.dumps(r) for r in conv_records) + "\n", encoding="utf-8")
    run["_artifact_dir"] = run_id
    run["_artifact_path"] = str(run_dir)
    return run


def _terminal_524() -> list[dict[str, object]]:
    return [
        {"status": "request_retry", "request_index": 4, "error": {"kind": "http_transient", "last_status": 524}},
        {"status": "request_failed", "request_index": 4, "error": {"kind": "http_transient", "last_status": 524}},
    ]


def _recovered_524() -> list[dict[str, object]]:
    return [
        {"status": "request_retry", "request_index": 4, "error": {"kind": "http_transient", "last_status": 524}},
        {"status": "request_retry_succeeded", "request_index": 4, "attempt": 2},
    ]


class InfraFailureDetectorTests(unittest.TestCase):
    def test_terminal_transport_failure_is_infra_invalid(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run = _make_run_dir(
                Path(tmp), "grp/iface/terminal",
                points_earned=0, verifier_status="no_submission",
                harness_task_status="request_failed", failure_class="provider_or_context_failure",
                conv_records=_terminal_524(),
            )
            reason = provider_failure_reason(run, Path(run["_artifact_path"]))
            self.assertIsNotNone(reason)
            self.assertIn("request_failed", reason)

    def test_recovered_transient_is_not_infra_invalid(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run = _make_run_dir(
                Path(tmp), "grp/iface/recovered",
                points_earned=0, verifier_status="lean_check_failed",
                harness_task_status="failed_submitted", failure_class="proof_unsolved_goals",
                conv_records=_recovered_524(),
            )
            self.assertIsNone(provider_failure_reason(run, Path(run["_artifact_path"])))

    def test_pass_is_never_infra_invalid_even_with_retries(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run = _make_run_dir(
                Path(tmp), "grp/iface/passed",
                points_earned=1, verifier_status="passed",
                harness_task_status="passed", failure_class=None,
                conv_records=_recovered_524(),
            )
            # detector may see nothing; recover treats passes as genuine regardless.
            self.assertIsNone(provider_failure_reason(run, Path(run["_artifact_path"])))

    def test_transport_summary_counts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run = _make_run_dir(
                Path(tmp), "grp/iface/terminal",
                points_earned=0, verifier_status="no_submission",
                harness_task_status="request_failed", failure_class="provider_or_context_failure",
                conv_records=_terminal_524(),
            )
            summary = transport_failure_summary(Path(run["_artifact_path"]))
            self.assertEqual(summary["terminal"], 1)
            self.assertEqual(summary["retries"], 1)

    def test_missing_dir_is_safe(self) -> None:
        self.assertIsNone(provider_failure_reason({}, None))
        self.assertEqual(transport_failure_summary(None), {"retries": 0, "recovered": 0, "terminal": 0})


def _version_for(tasks: list[dict[str, object]]) -> dict[str, object]:
    return {
        "benchmark_version": "0.1",
        "harness_id": "default",
        "environment_id": "env-1",
        "mode": "fair",
        "budget": "normal",
        "tasks": [
            {
                "task_ref": t["task_ref"],
                "task_fingerprint": f"sha256:{'a' * 64}",
                "task_interface_id": "iface-1",
            }
            for t in tasks
        ],
    }


class RecoverScoringTests(unittest.TestCase):
    def _build(self, runs: list[dict[str, object]]) -> dict[str, object]:
        version = _version_for(runs)
        return build_model_entry(model_id=MODEL, version=version, previous_manifest={"models": []}, runs=runs)

    def test_infra_invalid_excluded_from_failed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            passed = _make_run_dir(
                root, "grp/iface/passed", points_earned=1, verifier_status="passed",
                harness_task_status="passed", failure_class=None, conv_records=[],
            )
            genuine_fail = _make_run_dir(
                root, "grp/iface/genfail", points_earned=0, verifier_status="lean_check_failed",
                harness_task_status="failed_submitted", failure_class="proof_unsolved_goals",
                conv_records=_recovered_524(),
            )
            infra = _make_run_dir(
                root, "grp/iface/infra", points_earned=0, verifier_status="no_submission",
                harness_task_status="request_failed", failure_class="provider_or_context_failure",
                conv_records=_terminal_524(),
            )
            entry = self._build([passed, genuine_fail, infra])

        self.assertEqual(entry["passed"], 1)
        self.assertEqual(entry["failed"], 1, "only the genuine non-pass should count as failed")
        self.assertEqual(entry["invalid_count"], 1)
        self.assertEqual(entry["valid_count"], 2)
        by_ref = {r["task_ref"]: r for r in entry["task_results"]}
        self.assertTrue(by_ref["grp/iface/infra"]["provider_invalid"])
        self.assertFalse(by_ref["grp/iface/infra"]["reusable"])
        self.assertIn("provider_failure_reason", by_ref["grp/iface/infra"])
        self.assertFalse(by_ref["grp/iface/genfail"]["provider_invalid"])
        self.assertTrue(by_ref["grp/iface/genfail"]["reusable"])

    def test_reusable_result_forces_rerun_of_infra_invalid(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            infra = _make_run_dir(
                Path(tmp), "grp/iface/infra", points_earned=0, verifier_status="no_submission",
                harness_task_status="request_failed", failure_class="provider_or_context_failure",
                conv_records=_terminal_524(),
            )
            entry = self._build([infra])
        row = entry["task_results"][0]
        ok, reason = reusable_result(row)
        self.assertFalse(ok)
        self.assertEqual(reason, "provider/transport failure")

    def test_genuine_fail_row_is_reusable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            genuine = _make_run_dir(
                Path(tmp), "grp/iface/genfail", points_earned=0, verifier_status="lean_check_failed",
                harness_task_status="failed_submitted", failure_class="proof_unsolved_goals",
                conv_records=_recovered_524(),
            )
            entry = self._build([genuine])
        ok, _ = reusable_result(entry["task_results"][0])
        self.assertTrue(ok)


class ClassifyOverrideTests(unittest.TestCase):
    def test_classify_runs_dir_marks_infra_invalid(self) -> None:
        taxonomy = load_taxonomy()
        with tempfile.TemporaryDirectory() as tmp:
            run = _make_run_dir(
                Path(tmp), "grp/iface/infra", points_earned=0, verifier_status="no_submission",
                harness_task_status="request_failed", failure_class="provider_or_context_failure",
                conv_records=_terminal_524(),
            )
            rows = classify_runs_dir(Path(run["_artifact_path"]), taxonomy=taxonomy)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["outcome"], "infra_invalid")
        self.assertFalse(rows[0]["is_pass"])

    def test_classify_runs_dir_keeps_genuine_failure(self) -> None:
        taxonomy = load_taxonomy()
        with tempfile.TemporaryDirectory() as tmp:
            run = _make_run_dir(
                Path(tmp), "grp/iface/genfail", points_earned=0, verifier_status="lean_check_failed",
                harness_task_status="failed_submitted", failure_class="proof_unsolved_goals",
                conv_records=_recovered_524(),
            )
            rows = classify_runs_dir(Path(run["_artifact_path"]), taxonomy=taxonomy)
        self.assertEqual(rows[0]["outcome"], "lean_check_failed")


if __name__ == "__main__":
    unittest.main()
