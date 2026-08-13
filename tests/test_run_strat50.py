import importlib.util
from pathlib import Path
from unittest import mock

import pytest

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


def test_rejects_duplicate_models(tmp_path):
    with mock.patch.object(RUNNER, "parse_args", return_value=args(tmp_path, models=["m", "m"])):
        with pytest.raises(SystemExit, match="duplicate"):
            RUNNER.main()


def test_rejects_non_p4_budget(tmp_path):
    with mock.patch.object(RUNNER, "parse_args", return_value=args(tmp_path, max_attempts=15)):
        with pytest.raises(SystemExit, match="p4_normal"):
            RUNNER.main()


def test_rejects_dirty_checkout(tmp_path):
    with (
        mock.patch.object(RUNNER, "parse_args", return_value=args(tmp_path)),
        mock.patch.object(RUNNER.subprocess, "check_output", side_effect=["head\n", " M file\n"]),
    ):
        with pytest.raises(SystemExit, match="clean"):
            RUNNER.main()


def test_cohort_environment_filter_never_captures_secrets(monkeypatch):
    monkeypatch.setenv("DEFAULT_HARNESS_STREAMING", "0")
    monkeypatch.setenv("DEFAULT_HARNESS_API_KEY", "must-not-be-recorded")
    captured = {
        key: value
        for key, value in sorted(RUNNER.os.environ.items())
        if key.startswith("DEFAULT_HARNESS_")
        and not any(marker in key for marker in RUNNER.SECRET_ENV_MARKERS)
    }
    assert captured["DEFAULT_HARNESS_STREAMING"] == "0"
    assert "DEFAULT_HARNESS_API_KEY" not in captured
