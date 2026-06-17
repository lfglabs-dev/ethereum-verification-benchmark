#!/usr/bin/env python3
"""Aggregate a benchmark version manifest and result manifest."""
from __future__ import annotations

import argparse
import json
import statistics
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def slug(value: str) -> str:
    return "".join(ch if ch.isalnum() else "-" for ch in value).strip("-").lower()


def split_model_id(model_id: str) -> tuple[str, str]:
    if "/" in model_id:
        provider, model = model_id.split("/", 1)
        return provider, model
    known_aliases = {
        "grok": ("xai", "grok-build-0.1"),
    }
    if model_id in known_aliases:
        return known_aliases[model_id]
    known_prefixes = {
        "anthropic-": "anthropic",
        "claude-": "anthropic",
        "deepseek-": "deepseek",
        "gemini-": "google",
        "grok-": "xai",
        "kimi-": "moonshot",
        "minimax-": "minimax",
        "openai-": "openai",
        "spark-": "spark",
        "venice-": "venice",
        "xiaomi-": "xiaomi",
        "xai-": "xai",
        "zai-": "zai",
        "zai-org-": "zai",
    }
    for prefix, provider in sorted(known_prefixes.items(), key=lambda item: len(item[0]), reverse=True):
        if model_id.startswith(prefix):
            return provider, model_id[len(prefix) :]
    return "unknown", model_id


def model_summary(model: dict[str, Any]) -> dict[str, Any]:
    tasks = model.get("task_results", [])
    passed = [task for task in tasks if task.get("passed")]
    usage = [task.get("usage") for task in tasks if isinstance(task.get("usage"), dict)]
    completion_passed = [int((task.get("usage") or {}).get("completion_tokens") or 0) for task in passed]
    prompt_passed = [int((task.get("usage") or {}).get("prompt_tokens") or 0) for task in passed]
    provider, model_name = split_model_id(model["model_id"])
    return {
        "model_id": model["model_id"],
        "provider": model.get("provider", provider),
        "model": model.get("model", model_name),
        "display_name": model.get("display_name", model["model_id"]),
        "status": model.get("status", "invalid"),
        "task_count": model.get("task_count", len(tasks)),
        "valid_count": model.get("valid_count", len(tasks)),
        "passed": model.get("passed", len(passed)),
        "failed": model.get("failed", len(tasks) - len(passed)),
        "pass_rate": round((model.get("passed", len(passed)) / model.get("task_count", len(tasks))), 3) if model.get("task_count", len(tasks)) else 0.0,
        "prompt_tokens": sum(int(item.get("prompt_tokens") or 0) for item in usage),
        "completion_tokens": sum(int(item.get("completion_tokens") or 0) for item in usage),
        "total_tokens": sum(int(item.get("total_tokens") or 0) for item in usage),
        "median_completion_tokens_to_pass": int(statistics.median(completion_passed)) if completion_passed else None,
        "median_prompt_tokens_to_pass": int(statistics.median(prompt_passed)) if prompt_passed else None,
        "caveats": model.get("caveats", []),
        "archive": model.get("archive"),
    }


def badge(label: str, summary: dict[str, Any]) -> dict[str, Any]:
    message = f"{summary['passed']}/{summary['task_count']}"
    if summary.get("status") == "partial":
        message += " partial"
    color = "brightgreen" if summary["passed"] == summary["task_count"] and summary["task_count"] else "yellow" if summary["passed"] else "red"
    if summary.get("status") != "complete":
        color = "lightgrey" if summary["passed"] == 0 else "yellow"
    return {"schemaVersion": 1, "label": label, "message": message, "color": color}


def leaderboard(version: dict[str, Any], summaries: list[dict[str, Any]]) -> str:
    lines = [
        "# Verity Benchmark Leaderboard",
        "",
        f"Benchmark version `{version['benchmark_version']}` · generated {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%MZ')}",
        "",
        "Complete rows are eligible for rank comparisons. Partial rows are shown for transparency and excluded from complete-rank comparisons.",
        "",
        "| Rank | Model | Status | Verified | Prompt tok | Completion tok | Caveats |",
        "|---:|---|---|---:|---:|---:|---|",
    ]
    complete = [item for item in summaries if item["status"] == "complete"]
    complete_rank = {item["model_id"]: rank for rank, item in enumerate(sorted(complete, key=lambda item: (-item["pass_rate"], item["completion_tokens"], item["model_id"])), 1)}
    for item in sorted(summaries, key=lambda item: (item["status"] != "complete", -item["pass_rate"], item["completion_tokens"], item["model_id"])):
        rank = str(complete_rank[item["model_id"]]) if item["model_id"] in complete_rank else "partial"
        caveats = ", ".join(str(c) for c in item.get("caveats") or []) or "-"
        lines.append(
            f"| {rank} | {item['display_name']} | `{item['status']}` | {item['passed']}/{item['task_count']} | "
            f"{item['prompt_tokens']} | {item['completion_tokens']} | {caveats} |"
        )
    return "\n".join(lines) + "\n"


def aggregate(version: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    summaries = [model_summary(model) for model in manifest.get("models", [])]
    return {
        "schema_version": 1,
        "benchmark": version["benchmark"],
        "benchmark_version": version["benchmark_version"],
        "task_count": version["task_count"],
        "task_set_id": version["task_set_id"],
        "harness_id": version["harness_id"],
        "environment_id": version["environment_id"],
        "models": summaries,
    }


def build_version_index(out: Path, latest_version: str, current_summary: dict[str, Any]) -> dict[str, Any]:
    summaries_dir = out / "results" / "summaries"
    versions: dict[str, dict[str, Any]] = {}
    for path in sorted(summaries_dir.glob("v*.json")):
        try:
            summary = load_json(path)
        except json.JSONDecodeError:
            continue
        version_name = str(summary.get("benchmark_version") or path.stem.removeprefix("v"))
        versions[version_name] = {
            "benchmark_version": version_name,
            "tag": f"benchmark-v{version_name}",
            "label": f"v{version_name}",
            "task_count": int(summary.get("task_count") or 0),
            "summary_url": f"results/summaries/v{version_name}.json",
            "manifest_url": f"results/manifests/v{version_name}.json",
        }
    version_name = str(current_summary["benchmark_version"])
    versions[version_name] = {
        "benchmark_version": version_name,
        "tag": f"benchmark-v{version_name}",
        "label": f"v{version_name}",
        "task_count": int(current_summary["task_count"]),
        "summary_url": f"results/summaries/v{version_name}.json",
        "manifest_url": f"results/manifests/v{version_name}.json",
    }
    return {
        "schema_version": 1,
        "benchmark": current_summary["benchmark"],
        "latest_version": latest_version,
        "versions": [versions[key] for key in sorted(versions)],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", type=Path, required=True)
    parser.add_argument("--results-manifest", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, default=Path("."))
    args = parser.parse_args()

    version = load_json(args.version)
    manifest = load_json(args.results_manifest)
    summary = aggregate(version, manifest)
    out = args.out_dir
    version_name = str(version["benchmark_version"])
    summaries_dir = out / "results" / "summaries"
    badges_dir = out / "badges"
    summaries_dir.mkdir(parents=True, exist_ok=True)
    badges_dir.mkdir(parents=True, exist_ok=True)
    (summaries_dir / f"v{version_name}.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out / "results.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out / "leaderboard.md").write_text(leaderboard(version, summary["models"]), encoding="utf-8")
    (out / "results" / "index.json").write_text(
        json.dumps(build_version_index(out, latest_version=version_name, current_summary=summary), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    for item in summary["models"]:
        (badges_dir / f"{slug(item['model_id'])}.json").write_text(json.dumps(badge(item["display_name"], item)) + "\n", encoding="utf-8")
    complete_runs = sum(item["task_count"] for item in summary["models"] if item["status"] == "complete")
    all_runs = sum(item["task_count"] for item in summary["models"])
    (badges_dir / "overall.json").write_text(
        json.dumps({"schemaVersion": 1, "label": "verity bench", "message": f"{complete_runs}/{all_runs} complete-version runs", "color": "brightgreen" if complete_runs == all_runs and all_runs else "yellow"}) + "\n",
        encoding="utf-8",
    )
    print(f"aggregated benchmark v{version_name}: {len(summary['models'])} model row(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
