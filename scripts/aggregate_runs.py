#!/usr/bin/env python3
"""Aggregate benchmark run artifacts into README-facing results.

Scans directories containing harness run artifacts (run.json +
harness-response.json) and emits:

- results.json     canonical per-model x per-task results with token usage
- leaderboard.md   markdown table (pass rate, attempts, tokens-to-success)
- badges/<slug>.json and badges/overall.json  shields.io endpoint payloads

Usage:
  python3 scripts/aggregate_runs.py --runs-dir results/runs --out out \
      --names "builtin/smart=MiniMax,grok=Grok Code" \
      --meta budget=normal --meta sha=abc123
"""
from __future__ import annotations

import argparse
import json
import statistics
from datetime import datetime, timezone
from pathlib import Path


def _slug(model: str) -> str:
    return "".join(ch if ch.isalnum() else "-" for ch in model).strip("-").lower()


def _parse_names(raw: str) -> dict[str, str]:
    names: dict[str, str] = {}
    for pair in raw.split(","):
        pair = pair.strip()
        if not pair:
            continue
        if "=" in pair:
            model, name = pair.split("=", 1)
            names[model.strip()] = name.strip()
        else:
            names[pair] = pair
    return names


def collect_runs(runs_dir: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for run_path in sorted(runs_dir.glob("**/run.json")):
        try:
            run = json.loads(run_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        score = run.get("verifier", {}).get("score", {})
        attempts = None
        tool_calls = None
        response_path = run_path.parent / "harness-response.json"
        if response_path.is_file():
            try:
                response = json.loads(response_path.read_text(encoding="utf-8"))
                tasks = response.get("tasks") or []
                if tasks and isinstance(tasks[0], dict):
                    attempts = len(tasks[0].get("attempts") or [])
                    tool_calls = tasks[0].get("tool_calls_executed")
            except (OSError, json.JSONDecodeError):
                pass
        usage = run.get("usage") or {}
        rows.append(
            {
                "run_id": run.get("run_id"),
                "harness": run.get("harness_id"),
                "usage_source": run.get("usage_source", "in-loop"),
                "model": run.get("model"),
                "task_ref": run.get("task_ref") or run.get("group_id"),
                "mode": run.get("mode"),
                "passed": score.get("passed_targets", 0) == score.get("total_targets", 0) and score.get("total_targets", 0) > 0,
                "passed_targets": score.get("passed_targets", 0),
                "total_targets": score.get("total_targets", 0),
                "attempts": attempts,
                "tool_calls": tool_calls,
                "prompt_tokens": usage.get("prompt_tokens"),
                "completion_tokens": usage.get("completion_tokens"),
                "duration_seconds": run.get("duration_seconds"),
                "started_at": run.get("started_at"),
            }
        )
    return rows


def _dedupe_latest(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    """Keep only the latest run per (model, task_ref)."""
    latest: dict[tuple[str, str, str], dict[str, object]] = {}
    for row in sorted(rows, key=lambda item: str(item.get("started_at") or "")):
        latest[(str(row["harness"]), str(row["model"]), str(row["task_ref"]))] = row
    return list(latest.values())


def _model_summary(rows: list[dict[str, object]]) -> dict[str, object]:
    passed = [row for row in rows if row["passed"]]
    completion = [row["completion_tokens"] for row in passed if isinstance(row["completion_tokens"], (int, float))]
    attempts = [row["attempts"] for row in passed if isinstance(row["attempts"], int)]
    return {
        "tasks": len(rows),
        "passed": len(passed),
        "pass_rate": round(len(passed) / len(rows), 3) if rows else 0.0,
        "median_attempts_to_pass": statistics.median(attempts) if attempts else None,
        "median_completion_tokens_to_pass": int(statistics.median(completion)) if completion else None,
        "total_completion_tokens": sum(int(row["completion_tokens"]) for row in rows if isinstance(row["completion_tokens"], (int, float))),
    }


def _badge(label: str, summary: dict[str, object]) -> dict[str, object]:
    passed = summary["passed"]
    tasks = summary["tasks"]
    tokens = summary["median_completion_tokens_to_pass"]
    message = f"{passed}/{tasks}"
    if tokens:
        message += f" · {round(tokens / 1000, 1)}k tok"
    if tasks == 0:
        color = "lightgrey"
    elif passed == tasks:
        color = "brightgreen"
    elif passed > 0:
        color = "yellow"
    else:
        color = "red"
    return {"schemaVersion": 1, "label": label, "message": message, "color": color}


def _leaderboard_markdown(summaries: dict[str, dict[str, object]], names: dict[str, str], meta: dict[str, str]) -> str:
    lines = [
        "# Verity Benchmark Leaderboard",
        "",
        f"Generated {meta.get('date')} · commit `{meta.get('sha', 'unknown')[:9]}` · budget `{meta.get('budget', '?')}`",
        "",
        "| Harness | Model | Pass | Median attempts to pass | Median completion tokens to pass | Total completion tokens |",
        "|---|---|---|---|---|---|",
    ]
    def sort_key(item: tuple[str, dict[str, object]]) -> tuple[float, float]:
        summary = item[1]
        tokens = summary["median_completion_tokens_to_pass"]
        return (-float(summary["pass_rate"]), float(tokens) if tokens else float("inf"))

    for combo, summary in sorted(summaries.items(), key=sort_key):
        harness, _, model = combo.partition(":")
        harness_display = "builtin (fair)" if harness == "default" else harness
        display = names.get(model, model)
        tokens = summary["median_completion_tokens_to_pass"]
        lines.append(
            f"| {harness_display} | {display} | {summary['passed']}/{summary['tasks']} | "
            f"{summary['median_attempts_to_pass'] if summary['median_attempts_to_pass'] is not None else '—'} | "
            f"{f'{tokens:,}' if tokens else '—'} | {summary['total_completion_tokens']:,} |"
        )
    lines.extend(
        [
            "",
            "Pass/fail is decided by the independent verifier. Tokens are completion tokens",
            "reported by the provider across the whole agent loop for the task.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs-dir", type=Path, default=Path("results/runs"))
    parser.add_argument("--out", type=Path, default=Path("out"))
    parser.add_argument("--names", default="", help="model=Display Name,comma separated")
    parser.add_argument("--meta", action="append", default=[], help="key=value metadata, repeatable")
    args = parser.parse_args()

    names = _parse_names(args.names)
    meta = {"date": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%MZ")}
    for pair in args.meta:
        if "=" in pair:
            key, value = pair.split("=", 1)
            meta[key] = value

    rows = _dedupe_latest(collect_runs(args.runs_dir))
    combos = sorted({(str(row["harness"]), str(row["model"])) for row in rows})
    summaries = {
        f"{harness}:{model}": _model_summary([row for row in rows if row["harness"] == harness and row["model"] == model])
        for harness, model in combos
    }

    out = args.out
    badges = out / "badges"
    badges.mkdir(parents=True, exist_ok=True)
    (out / "results.json").write_text(
        json.dumps({"meta": meta, "names": names, "summaries": summaries, "runs": rows}, indent=2) + "\n",
        encoding="utf-8",
    )
    (out / "leaderboard.md").write_text(_leaderboard_markdown(summaries, names, meta), encoding="utf-8")
    for harness, model in combos:
        key = f"{harness}:{model}"
        label = names.get(model, model)
        if harness != "default":
            label = f"{label} ({harness})"
        slug = _slug(model) if harness == "default" else f"{_slug(harness)}--{_slug(model)}"
        (badges / f"{slug}.json").write_text(json.dumps(_badge(label, summaries[key])) + "\n", encoding="utf-8")
    total = _model_summary(rows)
    (badges / "overall.json").write_text(json.dumps(_badge("verity bench", total)) + "\n", encoding="utf-8")
    print(f"aggregated {len(rows)} runs for {len(combos)} harness-model combo(s) into {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
