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


def _parse_prices(raw: str) -> dict[str, tuple[float, float]]:
    """Parse "model=input_per_M/output_per_M" pairs (USD per million tokens)."""
    prices: dict[str, tuple[float, float]] = {}
    for pair in raw.split(","):
        pair = pair.strip()
        if not pair or "=" not in pair:
            continue
        model, rate = pair.split("=", 1)
        if "/" not in rate:
            continue
        input_rate, output_rate = rate.split("/", 1)
        try:
            prices[model.strip()] = (float(input_rate), float(output_rate))
        except ValueError:
            continue
    return prices


def _openrouter_prices(mapping_raw: str) -> dict[str, tuple[float, float]]:
    """Fetch live USD-per-token pricing from the OpenRouter models API.

    mapping_raw maps local model ids to OpenRouter ids, e.g.
    "builtin/smart=minimax/minimax-m3,gpt55=openai/gpt-5.5".
    Returns USD per million tokens. Fails soft (empty dict) when offline.
    """
    mapping: dict[str, str] = {}
    for pair in mapping_raw.split(","):
        pair = pair.strip()
        if pair and "=" in pair:
            local, remote = pair.split("=", 1)
            mapping[local.strip()] = remote.strip()
    if not mapping:
        return {}
    import urllib.request

    try:
        request = urllib.request.Request(
            "https://openrouter.ai/api/v1/models", headers={"User-Agent": "verity-benchmark-harness/1.0"}
        )
        with urllib.request.urlopen(request, timeout=30) as response:
            models = json.loads(response.read().decode("utf-8")).get("data", [])
    except Exception as exc:  # noqa: BLE001 - pricing is best-effort decoration
        print(f"warning: could not fetch OpenRouter pricing ({exc}); cost columns omitted")
        return {}
    by_id = {model.get("id"): model.get("pricing", {}) for model in models if isinstance(model, dict)}
    prices: dict[str, tuple[float, float]] = {}
    for local, remote in mapping.items():
        pricing = by_id.get(remote)
        if not pricing:
            print(f"warning: OpenRouter id {remote!r} not found; no pricing for {local}")
            continue
        try:
            prices[local] = (float(pricing["prompt"]) * 1_000_000, float(pricing["completion"]) * 1_000_000)
        except (KeyError, TypeError, ValueError):
            continue
    return prices


def _row_cost(row: dict[str, object], prices: dict[str, tuple[float, float]]) -> float | None:
    rates = prices.get(str(row.get("model")))
    if not rates:
        return None
    prompt = row.get("prompt_tokens")
    completion = row.get("completion_tokens")
    if not isinstance(prompt, (int, float)) or not isinstance(completion, (int, float)):
        return None
    return prompt * rates[0] / 1_000_000 + completion * rates[1] / 1_000_000


def _fmt_cost(value: object) -> str:
    if not isinstance(value, (int, float)):
        return "—"
    return f"${value:.2f}" if value >= 0.10 else f"${value:.3f}"


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
                "total_tokens": usage.get("total_tokens"),
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
    costs = [row["cost_usd"] for row in passed if isinstance(row.get("cost_usd"), (int, float))]
    all_costs = [row["cost_usd"] for row in rows if isinstance(row.get("cost_usd"), (int, float))]
    completion = [row["completion_tokens"] for row in passed if isinstance(row["completion_tokens"], (int, float))]
    prompt = [row["prompt_tokens"] for row in passed if isinstance(row["prompt_tokens"], (int, float))]
    attempts = [row["attempts"] for row in passed if isinstance(row["attempts"], int) and row["attempts"] > 0]
    return {
        "tasks": len(rows),
        "passed": len(passed),
        "pass_rate": round(len(passed) / len(rows), 3) if rows else 0.0,
        "median_attempts_to_pass": statistics.median(attempts) if attempts else None,
        "median_completion_tokens_to_pass": int(statistics.median(completion)) if completion else None,
        "median_prompt_tokens_to_pass": int(statistics.median(prompt)) if prompt else None,
        "total_completion_tokens": sum(int(row["completion_tokens"]) for row in rows if isinstance(row["completion_tokens"], (int, float))),
        "total_prompt_tokens": sum(int(row["prompt_tokens"]) for row in rows if isinstance(row["prompt_tokens"], (int, float))),
        "median_cost_to_pass_usd": round(statistics.median(costs), 4) if costs else None,
        "total_cost_usd": round(sum(all_costs), 4) if all_costs else None,
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


def _fmt_tokens(value: object) -> str:
    if not isinstance(value, (int, float)) or not value:
        return "—"
    if value >= 1_000_000:
        return f"{value / 1_000_000:.1f}M"
    if value >= 1_000:
        return f"{value / 1_000:.1f}k"
    return str(int(value))


def _harness_display(harness: str) -> str:
    return "builtin (fair)" if harness == "default" else harness


def _leaderboard_markdown(
    summaries: dict[str, dict[str, object]],
    rows: list[dict[str, object]],
    names: dict[str, str],
    meta: dict[str, str],
) -> str:
    lines = [
        "# Verity Benchmark Leaderboard",
        "",
        f"Generated {meta.get('date')} · commit `{meta.get('sha', 'unknown')[:9]}` · budget `{meta.get('budget', '?')}`",
        "",
        "**Headline metric: tokens to a verified proof.** All combos run the same task set;",
        "pass/fail is decided by the independent verifier; tokens are counted across the",
        "whole agent loop (builtin: in-loop accounting; shell harnesses: metered at the API",
        "boundary by the harness proxy).",
        "",
        "| Harness | Model | Pass | Median completion tok / pass | Median prompt tok / pass | Median cost / pass | Total completion tok | Total prompt tok | Total cost |",
        "|---|---|---|---|---|---|---|---|---|",
    ]

    def sort_key(item: tuple[str, dict[str, object]]) -> tuple[float, float]:
        summary = item[1]
        tokens = summary["median_completion_tokens_to_pass"]
        return (-float(summary["pass_rate"]), float(tokens) if tokens else float("inf"))

    for combo, summary in sorted(summaries.items(), key=sort_key):
        harness, _, model = combo.partition(":")
        display = names.get(model, model)
        lines.append(
            f"| {_harness_display(harness)} | {display} | {summary['passed']}/{summary['tasks']} | "
            f"{_fmt_tokens(summary['median_completion_tokens_to_pass'])} | "
            f"{_fmt_tokens(summary['median_prompt_tokens_to_pass'])} | "
            f"{_fmt_cost(summary.get('median_cost_to_pass_usd'))} | "
            f"{_fmt_tokens(summary['total_completion_tokens'])} | {_fmt_tokens(summary['total_prompt_tokens'])} | "
            f"{_fmt_cost(summary.get('total_cost_usd'))} |"
        )

    # Per-task matrix: one row per task, one column per harness x model combo,
    # cell = pass/fail with completion tokens spent on that task.
    combos = sorted({(str(row["harness"]), str(row["model"])) for row in rows})
    tasks = sorted({str(row["task_ref"]) for row in rows})
    by_key = {(str(r["harness"]), str(r["model"]), str(r["task_ref"])): r for r in rows}
    header = " | ".join(f"{_harness_display(h)}<br>{names.get(m, m)}" for h, m in combos)
    lines.extend(
        [
            "",
            "## Per-task completion tokens",
            "",
            "Cell = ✅/❌ with completion tokens spent on that task (including failed attempts).",
            "",
            f"| Task | {header} |",
            "|---" * (len(combos) + 1) + "|",
        ]
    )
    for task in tasks:
        cells = []
        for harness, model in combos:
            row = by_key.get((harness, model, task))
            if row is None:
                cells.append("·")
            else:
                mark = "✅" if row["passed"] else "❌"
                cost = row.get("cost_usd")
                suffix = f" ({_fmt_cost(cost)})" if isinstance(cost, (int, float)) else ""
                tokens = row["completion_tokens"]
                if not isinstance(tokens, (int, float)):
                    total = row.get("total_tokens")
                    cells.append(f"{mark} ≈{_fmt_tokens(total)} total{suffix}" if isinstance(total, (int, float)) else f"{mark} —{suffix}")
                else:
                    cells.append(f"{mark} {_fmt_tokens(tokens)}{suffix}")
        lines.append(f"| `{task}` | " + " | ".join(cells) + " |")
    lines.extend(
        [
            "",
            "Notes: completion tokens are what the model generated (the main cost driver per",
            "provider pricing); prompt tokens show how context-hungry each harness is. Shell",
            "harness rows have no attempt counts because iteration happens inside the CLI.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs-dir", type=Path, default=Path("results/runs"))
    parser.add_argument("--out", type=Path, default=Path("out"))
    parser.add_argument("--names", default="", help="model=Display Name,comma separated")
    parser.add_argument("--prices", default="", help="model=input_per_M/output_per_M USD, comma separated (overrides --openrouter)")
    parser.add_argument("--openrouter", default="", help="local_model=openrouter_id pairs; fetches live pricing from the OpenRouter API")
    parser.add_argument("--meta", action="append", default=[], help="key=value metadata, repeatable")
    args = parser.parse_args()

    names = _parse_names(args.names)
    meta = {"date": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%MZ")}
    for pair in args.meta:
        if "=" in pair:
            key, value = pair.split("=", 1)
            meta[key] = value

    prices = _openrouter_prices(args.openrouter)
    prices.update(_parse_prices(args.prices))
    rows = _dedupe_latest(collect_runs(args.runs_dir))
    for row in rows:
        cost = _row_cost(row, prices)
        if cost is not None:
            row["cost_usd"] = round(cost, 4)
    combos = sorted({(str(row["harness"]), str(row["model"])) for row in rows})
    summaries = {
        f"{harness}:{model}": _model_summary([row for row in rows if row["harness"] == harness and row["model"] == model])
        for harness, model in combos
    }

    out = args.out
    badges = out / "badges"
    badges.mkdir(parents=True, exist_ok=True)
    (out / "results.json").write_text(
        json.dumps({"meta": meta, "names": names, "prices_usd_per_M": {k: {"input": v[0], "output": v[1]} for k, v in prices.items()}, "summaries": summaries, "runs": rows}, indent=2) + "\n",
        encoding="utf-8",
    )
    (out / "leaderboard.md").write_text(_leaderboard_markdown(summaries, rows, names, meta), encoding="utf-8")
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
