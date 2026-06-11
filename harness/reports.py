from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def write_run_report(run_dir: Path, run: dict[str, Any]) -> None:
    score = run.get("verifier", {}).get("score", {})
    lines = [
        f"# Run {run.get('run_id')}",
        "",
        f"- harness: {run.get('harness_id')}",
        f"- track: {run.get('track')}",
        f"- run mode: {run.get('run_mode')}",
        f"- harness mode: {run.get('mode')}",
        f"- group: {run.get('group_id')}",
        f"- score: {score.get('points_earned', 0)} / {score.get('points_possible', 0)} points",
        f"- targets: {score.get('passed_targets', 0)} / {score.get('total_targets', 0)} passed",
        "",
        "## Targets",
        "",
    ]
    for target in run.get("verifier", {}).get("targets", []):
        lines.append(f"- `{target.get('task_ref')}`: {target.get('status')}")
    (run_dir / "report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def compare_runs(paths: list[Path]) -> dict[str, Any]:
    rows = []
    by_track: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for path in paths:
        run_path = path / "run.json" if path.is_dir() else path
        if not run_path.is_file():
            continue
        run = json.loads(run_path.read_text(encoding="utf-8"))
        score = run.get("verifier", {}).get("score", {})
        targets = run.get("verifier", {}).get("targets", [])
        if run.get("harness_status") in {"harness_error", "timeout"}:
            failure_modes = Counter({str(run.get("harness_status")): int(score.get("total_targets", 1) or 1)})
        else:
            failure_modes = Counter(
                str(target.get("status"))
                for target in targets
                if isinstance(target, dict) and target.get("status") != "passed"
            )
        row = {
            "run_id": run.get("run_id"),
            "harness": run.get("harness_id"),
            "model": run.get("model"),
            "track": run.get("track"),
            "mode": run.get("mode"),
            "harness_status": run.get("harness_status"),
            "group": run.get("group_id"),
            "task_ref": run.get("task_ref"),
            "points_earned": score.get("points_earned", 0),
            "points_possible": score.get("points_possible", 0),
            "passed_targets": score.get("passed_targets", 0),
            "total_targets": score.get("total_targets", 0),
            "failure_modes": dict(sorted(failure_modes.items())),
            "usage": run.get("usage"),
            "duration_seconds": run.get("duration_seconds"),
            "artifact": str(run_path),
        }
        rows.append(row)
        by_track[str(row["track"])].append(row)
    return {
        "schema_version": 1,
        "runs": rows,
        "tracks": {track: sorted(track_rows, key=lambda item: (-item["points_earned"], str(item["harness"]))) for track, track_rows in sorted(by_track.items())},
        "track_failure_modes": {
            track: dict(
                sorted(
                    sum((Counter(row["failure_modes"]) for row in track_rows), Counter()).items()
                )
            )
            for track, track_rows in sorted(by_track.items())
        },
        "cross_track_note": "Tracks are capability labels, not a flat fair-ranking surface.",
    }
