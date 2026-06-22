#!/usr/bin/env python3
"""Aggregate a benchmark version manifest and result manifest."""
from __future__ import annotations

import argparse
import json
import statistics
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from release_config import BADGE_LABEL, BENCHMARK_TITLE


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def slug(value: str) -> str:
    return "".join(ch if ch.isalnum() else "-" for ch in value).strip("-").lower()


PUBLIC_MODEL_ALIASES: dict[str, dict[str, str]] = {
    "claude-opus-4-8": {
        "model_provider_id": "anthropic",
        "model_name": "opus-4.8",
        "display_name": "opus-4.8",
    },
    "grok": {
        "model_provider_id": "xai",
        "model_name": "grok-build-0.1",
        "display_name": "grok-build-0.1",
    },
    "kimi/kimi-for-coding": {
        "model_provider_id": "kimi",
        "model_name": "kimi-k2.7",
        "display_name": "kimi-k2.7",
    },
    "openai-gpt-55": {
        "model_provider_id": "openai",
        "model_name": "gpt-5.5",
        "display_name": "gpt-5.5",
    },
    "openai-gpt-55-pro": {
        "model_provider_id": "openai",
        "model_name": "gpt-5.5-pro",
        "display_name": "gpt-5.5-pro",
    },
    "virtuals/deepseek-v4-flash": {
        "model_provider_id": "deepseek",
        "model_name": "deepseek-v4-flash",
        "display_name": "deepseek-v4-flash",
        "inference_provider_id": "virtuals",
        "inference_model_id": "virtuals/deepseek-v4-flash",
    },
    "virtuals/deepseek-v4-pro": {
        "model_provider_id": "deepseek",
        "model_name": "deepseek-v4-pro",
        "display_name": "deepseek-v4-pro",
        "inference_provider_id": "virtuals",
        "inference_model_id": "virtuals/deepseek-v4-pro",
    },
    "virtuals/xiaomi-mimo-v2-5": {
        "model_provider_id": "xiaomi",
        "model_name": "mimo-v2.5",
        "display_name": "mimo-v2.5",
        "inference_provider_id": "virtuals",
        "inference_model_id": "virtuals/xiaomi-mimo-v2-5",
    },
    "xiaomi-mimo-v2-5": {
        "model_provider_id": "xiaomi",
        "model_name": "mimo-v2.5",
        "display_name": "mimo-v2.5",
    },
}


def model_identity(source_model_id: str, display_name: str | None = None) -> dict[str, str]:
    """Return public model identity and serving-route identity separately."""
    source_provider, source_model_name = split_model_id(source_model_id)
    if source_model_id in PUBLIC_MODEL_ALIASES:
        alias = dict(PUBLIC_MODEL_ALIASES[source_model_id])
    else:
        alias = {
            "model_provider_id": source_provider,
            "model_name": source_model_name,
            "display_name": display_name or source_model_name,
        }
        if "/" in source_model_id and (not display_name or display_name == source_model_id or "/" in display_name):
            alias["display_name"] = source_model_name
    alias.setdefault("inference_provider_id", source_provider)
    alias.setdefault("inference_model_id", source_model_id)
    alias["model_id"] = f"{alias['model_provider_id']}/{alias['model_name']}"
    alias["source_model_id"] = source_model_id
    return alias


def public_model_identity(model_id: str, display_name: str | None = None) -> tuple[str, str, str]:
    """Return website-facing provider, model, and display label."""
    identity = model_identity(model_id, display_name)
    return identity["model_provider_id"], identity["model_name"], identity["display_name"]


def split_model_id(model_id: str) -> tuple[str, str]:
    if "/" in model_id:
        provider, model = model_id.split("/", 1)
        return provider, model
    known_aliases = {
        key: (identity["model_provider_id"], identity["model_name"])
        for key, identity in PUBLIC_MODEL_ALIASES.items()
        if "/" not in key or key == "kimi/kimi-for-coding"
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
    identity = model_identity(model["model_id"], model.get("display_name"))
    return {
        "model_id": identity["model_id"],
        "source_model_id": identity["source_model_id"],
        "model_provider_id": identity["model_provider_id"],
        "model_name": identity["model_name"],
        "inference_provider_id": identity["inference_provider_id"],
        "inference_model_id": identity["inference_model_id"],
        "provider": identity["model_provider_id"],
        "model": identity["model_name"],
        "display_name": identity["display_name"],
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


def leaderboard_json(summary: dict[str, Any]) -> dict[str, Any]:
    """Build a website-oriented leaderboard table from a version summary."""
    rows: list[dict[str, Any]] = []
    complete_rows = [item for item in summary["models"] if item.get("status") == "complete"]
    complete_rank = {
        item["model_id"]: rank
        for rank, item in enumerate(
            sorted(complete_rows, key=lambda item: (-item["pass_rate"], item["completion_tokens"], item["model_id"])),
            1,
        )
    }
    sorted_rows = sorted(
        summary["models"],
        key=lambda item: (item.get("status") != "complete", -item["pass_rate"], item["completion_tokens"], item["model_id"]),
    )
    for item in sorted_rows:
        task_count = int(item.get("task_count") or 0)
        total_tokens = int(item.get("total_tokens") or 0)
        rows.append(
            {
                "rank": complete_rank.get(item["model_id"]),
                "model_id": item["model_id"],
                "source_model_id": item["source_model_id"],
                "model_provider_id": item["model_provider_id"],
                "model_name": item["model_name"],
                "inference_provider_id": item["inference_provider_id"],
                "inference_model_id": item["inference_model_id"],
                "display_name": item["display_name"],
                "status": item["status"],
                "pass_rate": item["pass_rate"],
                "passed": int(item["passed"]),
                "failed": int(item["failed"]),
                "total": task_count,
                "valid_count": int(item.get("valid_count", task_count)),
                "prompt_tokens": int(item.get("prompt_tokens") or 0),
                "completion_tokens": int(item.get("completion_tokens") or 0),
                "total_tokens": total_tokens,
                "avg_total_tokens_per_task": round(total_tokens / task_count, 1) if task_count else None,
                "caveats": item.get("caveats") or [],
            }
        )
    version_name = str(summary["benchmark_version"])
    return {
        "schema_version": 1,
        "benchmark": summary["benchmark"],
        "benchmark_version": version_name,
        "task_count": int(summary["task_count"]),
        "source_summary_url": f"results/summaries/v{version_name}.json",
        "source_manifest_url": f"results/manifests/v{version_name}.json",
        "ranking_policy": "complete rows ranked by pass_rate desc, completion_tokens asc, model_id asc; partial/invalid rows have null rank",
        "rows": rows,
    }


def leaderboard(version: dict[str, Any], summaries: list[dict[str, Any]]) -> str:
    lines = [
        f"# {BENCHMARK_TITLE} Leaderboard",
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
            "leaderboard_url": f"results/leaderboards/v{version_name}.json",
            "summary_url": f"results/summaries/v{version_name}.json",
            "manifest_url": f"results/manifests/v{version_name}.json",
        }
    version_name = str(current_summary["benchmark_version"])
    versions[version_name] = {
        "benchmark_version": version_name,
        "tag": f"benchmark-v{version_name}",
        "label": f"v{version_name}",
        "task_count": int(current_summary["task_count"]),
        "leaderboard_url": f"results/leaderboards/v{version_name}.json",
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
    leaderboards_dir = out / "results" / "leaderboards"
    badges_dir = out / "badges"
    summaries_dir.mkdir(parents=True, exist_ok=True)
    leaderboards_dir.mkdir(parents=True, exist_ok=True)
    badges_dir.mkdir(parents=True, exist_ok=True)
    (summaries_dir / f"v{version_name}.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (leaderboards_dir / f"v{version_name}.json").write_text(json.dumps(leaderboard_json(summary), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out / "results.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out / "leaderboard.md").write_text(leaderboard(version, summary["models"]), encoding="utf-8")
    (out / "results" / "index.json").write_text(
        json.dumps(build_version_index(out, latest_version=version_name, current_summary=summary), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    for item in summary["models"]:
        (badges_dir / f"{slug(item['source_model_id'])}.json").write_text(json.dumps(badge(item["display_name"], item)) + "\n", encoding="utf-8")
    complete_runs = sum(item["task_count"] for item in summary["models"] if item["status"] == "complete")
    all_runs = sum(item["task_count"] for item in summary["models"])
    (badges_dir / "overall.json").write_text(
        json.dumps({"schemaVersion": 1, "label": BADGE_LABEL, "message": f"{complete_runs}/{all_runs} complete-version runs", "color": "brightgreen" if complete_runs == all_runs and all_runs else "yellow"}) + "\n",
        encoding="utf-8",
    )
    print(f"aggregated benchmark v{version_name}: {len(summary['models'])} model row(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
