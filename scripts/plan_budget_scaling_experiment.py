#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import csv
import json
import os
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


REPO = Path(__file__).resolve().parents[1]
WORKSPACE = REPO.parent
DEFAULT_OUTPUT = REPO / "analysis" / "budget_scaling_minimax_50"
DEFAULT_MODEL = "minimax/minimax-m3"


@dataclass(frozen=True)
class BudgetProfile:
    name: str
    max_attempts: int
    max_tool_calls: int
    max_turns: int
    shell_timeout_seconds: int


PROFILES = [
    BudgetProfile("p01_ultra_tiny", 1, 6, 6, 240),
    BudgetProfile("p02_tiny", 1, 10, 8, 300),
    BudgetProfile("p03_ultra_cheap", 2, 16, 10, 450),
    BudgetProfile("p04_cheap", 2, 24, 12, 600),
    BudgetProfile("p05_quick_minus", 3, 32, 16, 750),
    BudgetProfile("p06_quick", 4, 40, 20, 900),
    BudgetProfile("p07_medium", 8, 80, 35, 1500),
    BudgetProfile("p08_normal", 16, 120, 50, 2400),
    BudgetProfile("p09_high", 32, 240, 80, 4800),
    BudgetProfile("p10_ultra_high", 64, 500, 140, 9600),
]


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def iter_jsonl(paths: Iterable[Path]) -> Iterable[dict]:
    for path in paths:
        if not path.is_file():
            continue
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.strip():
                item = json.loads(line)
                item["_summary_path"] = str(path)
                yield item


def passed(item: dict) -> bool:
    score = item.get("score") or item.get("verifier", {}).get("score") or {}
    return int(score.get("passed_targets", 0)) > 0 and int(score.get("passed_targets", 0)) == int(score.get("total_targets", 1))


def run_usage(run_dir: str | None) -> dict:
    if not run_dir:
        return {}
    path = Path(run_dir) / "run.json"
    if not path.is_file():
        return {}
    return load_json(path).get("usage") or {}


def enrich(item: dict) -> dict:
    usage = item.get("usage") or run_usage(item.get("run_dir")) or {}
    return {
        "task_ref": item["task_ref"],
        "model": item.get("model"),
        "passed": passed(item),
        "run_dir": item.get("run_dir"),
        "prompt_tokens": int(usage.get("prompt_tokens", 0) or 0),
        "completion_tokens": int(usage.get("completion_tokens", 0) or 0),
        "total_tokens": int(usage.get("total_tokens", 0) or 0),
        "requests": int(usage.get("requests", 0) or 0),
        "summary_path": item.get("_summary_path"),
    }


def latest_by_task(items: Iterable[dict]) -> dict[str, dict]:
    latest: dict[str, dict] = {}
    for item in items:
        task_ref = item.get("task_ref")
        if not task_ref:
            continue
        enriched = enrich(item)
        previous = latest.get(task_ref)
        if previous is None:
            latest[task_ref] = enriched
            continue
        # Prefer entries with usage; otherwise the later summary path wins.
        if enriched["total_tokens"] >= previous["total_tokens"]:
            latest[task_ref] = enriched
    return latest


def task_metadata() -> dict[str, dict]:
    version = load_json(REPO / "benchmark-versions" / "v0.1.json")
    return {task["task_ref"]: task for task in version["tasks"]}


def choose_tasks() -> tuple[list[dict], dict]:
    logs = WORKSPACE / "output" / "bench-logs"
    minimax_paths = sorted(logs.glob("part-*-minimax-minimax-m3/minimax-minimax-m3-local-summary.jsonl"))
    gpt_paths = sorted(logs.glob("virtuals-openai-gpt-55*/openai-gpt-55-local-summary.jsonl"))
    gpt_paths.extend(sorted(logs.glob("recovery-compute-acp-openai/openai-gpt-55-local-summary.jsonl")))

    minimax = latest_by_task(iter_jsonl(minimax_paths))
    gpt = latest_by_task(iter_jsonl(gpt_paths))
    meta = task_metadata()

    minimax_passed = [item for item in minimax.values() if item["passed"]]
    minimax_passed.sort(key=lambda item: (item["total_tokens"] or 10**18, item["requests"], item["task_ref"]))

    gpt_only = [
        item
        for task_ref, item in gpt.items()
        if item["passed"] and not minimax.get(task_ref, {}).get("passed", False)
    ]
    gpt_only.sort(key=lambda item: (item["total_tokens"] or 10**18, item["requests"], item["task_ref"]))

    selected: list[dict] = []
    for source, item in [("minimax_passed", item) for item in minimax_passed]:
        selected.append({"selection_source": source, **item})
    need = max(0, 50 - len(selected))
    for item in gpt_only[:need]:
        selected.append({"selection_source": "gpt55_only_passed", **item})

    selected = selected[:50]
    for rank, item in enumerate(selected, start=1):
        item["rank"] = rank
        task = meta.get(item["task_ref"], {})
        item["difficulty"] = task.get("difficulty")
        item["property_class"] = task.get("property_class")
        item["proof_family"] = task.get("proof_family")

    stats = {
        "minimax_summary_files": [str(path) for path in minimax_paths],
        "gpt55_summary_files": [str(path) for path in gpt_paths],
        "minimax_passed": len(minimax_passed),
        "gpt55_passed": sum(1 for item in gpt.values() if item["passed"]),
        "gpt55_only_passed": len(gpt_only),
        "selected": len(selected),
    }
    return selected, stats


def command_for(task_ref: str, profile: BudgetProfile, model: str = DEFAULT_MODEL) -> str:
    return (
        f"DEFAULT_HARNESS_MODEL='{model}' "
        f"python3 -m harness.cli run-task {task_ref} --harness default "
        f"--max-attempts {profile.max_attempts} "
        f"--max-tool-calls {profile.max_tool_calls} "
        f"--max-turns {profile.max_turns} "
        f"--shell-timeout-seconds {profile.shell_timeout_seconds}"
    )


def command_args(task_ref: str, profile: BudgetProfile) -> list[str]:
    return [
        "python3",
        "-m",
        "harness.cli",
        "run-task",
        task_ref,
        "--harness",
        "default",
        "--max-attempts",
        str(profile.max_attempts),
        "--max-tool-calls",
        str(profile.max_tool_calls),
        "--max-turns",
        str(profile.max_turns),
        "--shell-timeout-seconds",
        str(profile.shell_timeout_seconds),
    ]


def write_outputs(output: Path) -> None:
    output.mkdir(parents=True, exist_ok=True)
    selected, stats = choose_tasks()

    (output / "profiles.json").write_text(json.dumps([asdict(profile) for profile in PROFILES], indent=2) + "\n", encoding="utf-8")
    (output / "selected_tasks.json").write_text(json.dumps(selected, indent=2) + "\n", encoding="utf-8")
    (output / "selection_stats.json").write_text(json.dumps(stats, indent=2) + "\n", encoding="utf-8")

    with (output / "selected_tasks.csv").open("w", encoding="utf-8", newline="") as handle:
        fieldnames = [
            "rank",
            "task_ref",
            "selection_source",
            "total_tokens",
            "completion_tokens",
            "requests",
            "difficulty",
            "property_class",
            "proof_family",
            "run_dir",
        ]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for item in selected:
            writer.writerow({name: item.get(name) for name in fieldnames})

    lines = [
        "#!/usr/bin/env bash",
        "set -euo pipefail",
        'cd "$(dirname "$0")/../.."',
        "",
        "# This is the non-cascading command matrix: every profile runs every selected task.",
        "# For the cheaper cascading execution, use this script with --execute.",
        "",
    ]
    for profile in PROFILES:
        lines.append(f"# {profile.name}")
        for item in selected:
            lines.append(command_for(item["task_ref"], profile))
        lines.append("")
    command_path = output / "commands_full_matrix.sh"
    command_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    command_path.chmod(0o755)

    readme = [
        "# Budget Scaling Experiment: minimax/minimax-m3 on 50 tasks",
        "",
        "Selection rule:",
        f"- {stats['minimax_passed']} tasks were solved by Minimax in the current v0.1 local summaries.",
        f"- The selected panel starts with those Minimax-solved tasks sorted by observed total tokens.",
        f"- It is topped up to 50 with GPT 5.5-only solved tasks; available GPT-only pool: {stats['gpt55_only_passed']}.",
        "",
        "Recommended graph:",
        "- x: budget profile",
        "- y: cumulative solve rate",
        "- bars or annotations: newly solved tasks at each profile",
        "- secondary x or separate plot: cumulative total tokens / completion tokens",
        "",
        "Generated after cascade execution:",
        "- `cascade_summary.csv/json`: cumulative solves plus prompt/completion/total token effort.",
        "- `cascade_solve_rate.svg`: x = budget profile, y = cumulative solve rate.",
        "- `cascade_effort_solve_rate.svg`: x = cumulative total tokens, y = cumulative solve rate.",
        "",
        "Harness note:",
        "- For `--harness default`, the effective proof-search knobs are `max_attempts` and `max_tool_calls`.",
        "- `max_turns` and `shell_timeout_seconds` are still recorded in the profile so the same ladder can be reused for shell-agent harnesses, where those knobs are binding.",
        "",
        "Run cascade:",
        "```bash",
        "python3 scripts/plan_budget_scaling_experiment.py --execute --jobs 4",
        "```",
        "",
        "For the official MiniMax OpenAI-compatible endpoint, pass the base URL and model explicitly:",
        "```bash",
        "DEFAULT_HARNESS_API_KEY=... python3 scripts/plan_budget_scaling_experiment.py --execute --jobs 4 --base-url https://api.minimax.io/v1 --model MiniMax-M3",
        "```",
        "",
        "The cascade executes each profile only on tasks not solved by earlier profiles.",
        "Use `commands_full_matrix.sh` only for independent budget scaling where every profile is evaluated from scratch.",
        "",
    ]
    (output / "README.md").write_text("\n".join(readme), encoding="utf-8")


def load_selected(output: Path) -> list[dict]:
    path = output / "selected_tasks.json"
    if not path.is_file():
        write_outputs(output)
    return load_json(path)


def is_solved_run(run_dir: Path) -> bool:
    run = load_json(run_dir / "run.json")
    score = run.get("verifier", {}).get("score", {})
    return int(score.get("passed_targets", 0)) > 0 and int(score.get("passed_targets", 0)) == int(score.get("total_targets", 1))


def usage_from_run_dir(run_dir: Path) -> dict:
    run = load_json(run_dir / "run.json")
    usage = run.get("usage") or {}
    return {
        "prompt_tokens": int(usage.get("prompt_tokens", 0) or 0),
        "completion_tokens": int(usage.get("completion_tokens", 0) or 0),
        "total_tokens": int(usage.get("total_tokens", 0) or 0),
        "requests": int(usage.get("requests", 0) or 0),
    }


def row_from_run_dir(task_ref: str, profile: BudgetProfile, run_dir: str, *, recovered: bool = False) -> dict | None:
    run_path = Path(run_dir)
    if not run_path.is_dir() or not (run_path / "run.json").is_file():
        return None
    row = {
        "profile": profile.name,
        "task_ref": task_ref,
        "returncode": 0,
        "run_dir": str(run_path),
        "skipped_already_solved": False,
        "passed": is_solved_run(run_path),
    }
    if recovered:
        row["recovered_from_logs"] = True
    row.update(usage_from_run_dir(run_path))
    return row


def run_dir_from_stdout(stdout: str) -> str | None:
    for line in reversed(stdout.splitlines()):
        stripped = line.strip()
        if stripped.startswith("/") and "/results/runs/" in stripped:
            return stripped
    return None


def recover_rows_from_logs(output: Path, selected: list[dict], profiles: list[BudgetProfile]) -> list[dict]:
    task_by_safe_name = {item["task_ref"].replace("/", "__"): item["task_ref"] for item in selected}
    rows: list[dict] = []
    for profile in profiles:
        profile_dir = output / "runs" / profile.name
        if not profile_dir.is_dir():
            continue
        for stdout_path in sorted(profile_dir.glob("*.stdout.txt")):
            safe_name = stdout_path.name.removesuffix(".stdout.txt")
            task_ref = task_by_safe_name.get(safe_name)
            if not task_ref:
                continue
            run_dir = run_dir_from_stdout(stdout_path.read_text(encoding="utf-8", errors="replace"))
            if not run_dir:
                continue
            row = row_from_run_dir(task_ref, profile, run_dir, recovered=True)
            if row is not None:
                rows.append(row)
    rows.sort(
        key=lambda row: (
            next((index for index, profile in enumerate(profiles) if profile.name == row["profile"]), 10**9),
            next((index for index, item in enumerate(selected) if item["task_ref"] == row["task_ref"]), 10**9),
        )
    )
    deduped: dict[tuple[str, str], dict] = {}
    for row in rows:
        deduped[(row["profile"], row["task_ref"])] = row
    return list(deduped.values())


def run_one_task(
    task_ref: str,
    profile: BudgetProfile,
    profile_dir: Path,
    model: str,
    base_url: str | None,
    retries: int = 3,
) -> dict:
    env = os.environ.copy()
    env["DEFAULT_HARNESS_MODEL"] = model
    if base_url:
        env["DEFAULT_HARNESS_BASE_URL"] = base_url
    safe_name = task_ref.replace("/", "__")
    row: dict = {}
    stdout_chunks: list[str] = []
    stderr_chunks: list[str] = []
    for attempt in range(1, retries + 2):
        try:
            result = subprocess.run(
                command_args(task_ref, profile),
                cwd=REPO,
                env=env,
                text=True,
                capture_output=True,
                check=False,
                timeout=profile.shell_timeout_seconds + 30,
            )
            stdout = result.stdout
            stderr = result.stderr
            returncode = result.returncode
            timed_out = False
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode("utf-8", errors="replace")
            if isinstance(stderr, bytes):
                stderr = stderr.decode("utf-8", errors="replace")
            returncode = 124
            timed_out = True
            stderr += f"\nexternal timeout after {profile.shell_timeout_seconds + 30}s\n"
        stdout_chunks.append(f"--- runner attempt {attempt} ---\n{stdout}")
        stderr_chunks.append(f"--- runner attempt {attempt} ---\n{stderr}")
        run_dir = run_dir_from_stdout(stdout) or ""
        row = {
            "profile": profile.name,
            "task_ref": task_ref,
            "returncode": returncode,
            "run_dir": run_dir,
            "skipped_already_solved": False,
            "runner_attempts": attempt,
        }
        if timed_out:
            row["external_timeout"] = True
        run_row = row_from_run_dir(task_ref, profile, run_dir) if run_dir else None
        if run_row is not None:
            run_row["returncode"] = returncode
            run_row["runner_attempts"] = attempt
            row.update(run_row)
            break
        if timed_out:
            break
        if attempt <= retries:
            time.sleep(min(60, 2 ** attempt))
    (profile_dir / f"{safe_name}.stdout.txt").write_text("\n".join(stdout_chunks), encoding="utf-8")
    (profile_dir / f"{safe_name}.stderr.txt").write_text("\n".join(stderr_chunks), encoding="utf-8")
    return row


def execute_cascade(
    output: Path,
    limit_profiles: int | None = None,
    limit_tasks: int | None = None,
    jobs: int = 1,
    model: str = DEFAULT_MODEL,
    base_url: str | None = None,
    task_refs: list[str] | None = None,
    retries: int = 3,
    resume: bool = True,
) -> None:
    output.mkdir(parents=True, exist_ok=True)
    selected = load_selected(output)
    if task_refs:
        selected = [{"task_ref": task_ref, "rank": index} for index, task_ref in enumerate(task_refs, start=1)]
    if limit_tasks is not None:
        selected = selected[:limit_tasks]
    profiles = PROFILES[: limit_profiles or len(PROFILES)]
    rows: list[dict] = recover_rows_from_logs(output, selected, profiles) if resume else []
    jobs = max(1, jobs)

    for profile in profiles:
        solved_before_profile: set[str] = {
            row["task_ref"]
            for row in rows
            if row.get("passed")
            and next((index for index, candidate in enumerate(profiles) if candidate.name == row["profile"]), 10**9)
            < next((index for index, candidate in enumerate(profiles) if candidate.name == profile.name), 10**9)
        }
        already_executed = {
            row["task_ref"]
            for row in rows
            if row.get("profile") == profile.name and not row.get("skipped_already_solved")
        }
        profile_dir = output / "runs" / profile.name
        profile_dir.mkdir(parents=True, exist_ok=True)
        pending: list[str] = []
        for item in selected:
            task_ref = item["task_ref"]
            if task_ref in solved_before_profile:
                continue
            if task_ref in already_executed:
                continue
            pending.append(task_ref)
        if not pending:
            (output / "cascade_results.json").write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
            write_cascade_summary(output)
            continue
        if jobs == 1:
            completed_rows = [run_one_task(task_ref, profile, profile_dir, model, base_url, retries) for task_ref in pending]
        else:
            completed_rows = []
            with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
                futures = {
                    pool.submit(run_one_task, task_ref, profile, profile_dir, model, base_url, retries): task_ref
                    for task_ref in pending
                }
                for future in concurrent.futures.as_completed(futures):
                    completed_rows.append(future.result())
        completed_rows.sort(key=lambda row: next((index for index, item in enumerate(selected) if item["task_ref"] == row["task_ref"]), 10**9))
        for row in completed_rows:
            rows.append(row)
        (output / "cascade_results.json").write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
        write_cascade_summary(output)


def write_cascade_summary(output: Path) -> None:
    results_path = output / "cascade_results.json"
    if not results_path.is_file():
        return
    rows = load_json(results_path)
    selected = load_selected(output)
    task_count = len({row["task_ref"] for row in rows if row.get("task_ref")}) or len(selected)
    solved: set[str] = set()
    summary: list[dict] = []
    cumulative_prompt_tokens = 0
    cumulative_completion_tokens = 0
    cumulative_total_tokens = 0
    cumulative_requests = 0
    for profile in PROFILES:
        profile_rows = [row for row in rows if row.get("profile") == profile.name]
        newly_solved = sorted(
            row["task_ref"]
            for row in profile_rows
            if row.get("passed") and row.get("task_ref") not in solved
        )
        solved.update(newly_solved)
        profile_prompt_tokens = sum(int(row.get("prompt_tokens", 0) or 0) for row in profile_rows)
        profile_completion_tokens = sum(int(row.get("completion_tokens", 0) or 0) for row in profile_rows)
        profile_total_tokens = sum(int(row.get("total_tokens", 0) or 0) for row in profile_rows)
        profile_requests = sum(int(row.get("requests", 0) or 0) for row in profile_rows)
        cumulative_prompt_tokens += profile_prompt_tokens
        cumulative_completion_tokens += profile_completion_tokens
        cumulative_total_tokens += profile_total_tokens
        cumulative_requests += profile_requests
        summary.append(
            {
                "profile": profile.name,
                "max_attempts": profile.max_attempts,
                "max_tool_calls": profile.max_tool_calls,
                "max_turns": profile.max_turns,
                "shell_timeout_seconds": profile.shell_timeout_seconds,
                "executed_tasks": sum(1 for row in profile_rows if not row.get("skipped_already_solved")),
                "newly_solved": len(newly_solved),
                "cumulative_solved": len(solved),
                "solve_rate": round(len(solved) / task_count, 4) if task_count else 0,
                "profile_prompt_tokens": profile_prompt_tokens,
                "profile_completion_tokens": profile_completion_tokens,
                "profile_total_tokens": profile_total_tokens,
                "profile_requests": profile_requests,
                "cumulative_prompt_tokens": cumulative_prompt_tokens,
                "cumulative_completion_tokens": cumulative_completion_tokens,
                "cumulative_total_tokens": cumulative_total_tokens,
                "cumulative_requests": cumulative_requests,
            }
        )

    with (output / "cascade_summary.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(summary[0].keys()))
        writer.writeheader()
        writer.writerows(summary)
    (output / "cascade_summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    (output / "cascade_solve_rate.svg").write_text(render_solve_rate_svg(summary), encoding="utf-8")
    (output / "cascade_effort_solve_rate.svg").write_text(render_effort_solve_rate_svg(summary), encoding="utf-8")


def render_solve_rate_svg(summary: list[dict]) -> str:
    width, height = 1120, 640
    left, right, top, bottom = 82, 32, 56, 96
    plot_w = width - left - right
    plot_h = height - top - bottom
    max_y = 1.0
    points: list[tuple[float, float]] = []
    for index, row in enumerate(summary):
        x = left + (plot_w * index / max(1, len(summary) - 1))
        y = top + plot_h * (1 - float(row["solve_rate"]) / max_y)
        points.append((x, y))
    polyline = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    circles = []
    labels = []
    for (x, y), row in zip(points, summary):
        circles.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="7" fill="#2563eb" />')
        labels.append(
            f'<text x="{x:.1f}" y="{height - 48}" text-anchor="middle" '
            f'font-family="Arial" font-size="12" transform="rotate(-35 {x:.1f} {height - 48})">{row["profile"]}</text>'
        )
        labels.append(
            f'<text x="{x:.1f}" y="{y - 14:.1f}" text-anchor="middle" '
            f'font-family="Arial" font-size="12">{row["cumulative_solved"]}/50</text>'
        )
    grid = []
    for tick in range(0, 6):
        rate = tick / 5
        y = top + plot_h * (1 - rate)
        grid.append(f'<line x1="{left}" x2="{width - right}" y1="{y:.1f}" y2="{y:.1f}" stroke="#e5e7eb" />')
        grid.append(f'<text x="{left - 12}" y="{y + 4:.1f}" text-anchor="end" font-family="Arial" font-size="12">{rate:.0%}</text>')
    return "\n".join(
        [
            '<svg xmlns="http://www.w3.org/2000/svg" width="1120" height="640" viewBox="0 0 1120 640">',
            '<rect width="1120" height="640" fill="#ffffff" />',
            '<text x="40" y="36" font-family="Arial" font-size="24" font-weight="700">Cumulative solve rate by budget profile</text>',
            '<text x="40" y="60" font-family="Arial" font-size="13" fill="#4b5563">Minimax cascade on selected 50-task panel; solved tasks are skipped at later profiles.</text>',
            *grid,
            f'<line x1="{left}" x2="{left}" y1="{top}" y2="{height - bottom}" stroke="#111827" />',
            f'<line x1="{left}" x2="{width - right}" y1="{height - bottom}" y2="{height - bottom}" stroke="#111827" />',
            f'<polyline points="{polyline}" fill="none" stroke="#2563eb" stroke-width="3" />',
            *circles,
            *labels,
            '<text x="22" y="320" text-anchor="middle" font-family="Arial" font-size="13" transform="rotate(-90 22 320)">cumulative solve rate</text>',
            "</svg>",
        ]
    )


def render_effort_solve_rate_svg(summary: list[dict]) -> str:
    width, height = 1120, 640
    left, right, top, bottom = 98, 44, 56, 88
    plot_w = width - left - right
    plot_h = height - top - bottom
    max_x = max(1, max(int(row.get("cumulative_total_tokens", 0) or 0) for row in summary))
    points: list[tuple[float, float]] = []
    for row in summary:
        effort = int(row.get("cumulative_total_tokens", 0) or 0)
        x = left + plot_w * (effort / max_x if max_x else 0)
        y = top + plot_h * (1 - float(row["solve_rate"]))
        points.append((x, y))
    polyline = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    circles = []
    labels = []
    for (x, y), row in zip(points, summary):
        circles.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="7" fill="#0f766e" />')
        labels.append(
            f'<text x="{x:.1f}" y="{y - 14:.1f}" text-anchor="middle" '
            f'font-family="Arial" font-size="12">{row["profile"].split("_", 1)[0]}</text>'
        )
    grid = []
    for tick in range(0, 6):
        rate = tick / 5
        y = top + plot_h * (1 - rate)
        grid.append(f'<line x1="{left}" x2="{width - right}" y1="{y:.1f}" y2="{y:.1f}" stroke="#e5e7eb" />')
        grid.append(f'<text x="{left - 12}" y="{y + 4:.1f}" text-anchor="end" font-family="Arial" font-size="12">{rate:.0%}</text>')
    for tick in range(0, 6):
        effort = max_x * tick / 5
        x = left + plot_w * tick / 5
        label = f"{effort / 1_000_000:.1f}M" if max_x >= 1_000_000 else f"{effort / 1_000:.0f}k"
        grid.append(f'<line x1="{x:.1f}" x2="{x:.1f}" y1="{top}" y2="{height - bottom}" stroke="#f3f4f6" />')
        grid.append(f'<text x="{x:.1f}" y="{height - 50}" text-anchor="middle" font-family="Arial" font-size="12">{label}</text>')
    return "\n".join(
        [
            '<svg xmlns="http://www.w3.org/2000/svg" width="1120" height="640" viewBox="0 0 1120 640">',
            '<rect width="1120" height="640" fill="#ffffff" />',
            '<text x="40" y="36" font-family="Arial" font-size="24" font-weight="700">Cumulative solve rate by consumed effort</text>',
            '<text x="40" y="60" font-family="Arial" font-size="13" fill="#4b5563">Minimax cascade on selected 50-task panel; x-axis is cumulative total tokens from executed runs.</text>',
            *grid,
            f'<line x1="{left}" x2="{left}" y1="{top}" y2="{height - bottom}" stroke="#111827" />',
            f'<line x1="{left}" x2="{width - right}" y1="{height - bottom}" y2="{height - bottom}" stroke="#111827" />',
            f'<polyline points="{polyline}" fill="none" stroke="#0f766e" stroke-width="3" />',
            *circles,
            *labels,
            '<text x="28" y="320" text-anchor="middle" font-family="Arial" font-size="13" transform="rotate(-90 28 320)">cumulative solve rate</text>',
            f'<text x="{left + plot_w / 2:.1f}" y="{height - 18}" text-anchor="middle" font-family="Arial" font-size="13">cumulative total tokens</text>',
            "</svg>",
        ]
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Plan or execute a 10-profile Minimax budget scaling experiment.")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--execute", action="store_true", help="Run the cascading experiment; otherwise only writes the plan artifacts.")
    parser.add_argument("--limit-profiles", type=int)
    parser.add_argument("--limit-tasks", type=int)
    parser.add_argument("--jobs", type=int, default=1, help="Parallel tasks per profile during cascade execution.")
    parser.add_argument("--model", default=DEFAULT_MODEL, help="Model id for DEFAULT_HARNESS_MODEL during execution.")
    parser.add_argument("--base-url", help="Optional DEFAULT_HARNESS_BASE_URL override during execution.")
    parser.add_argument("--task-ref", action="append", help="Override selected_tasks.json during execution; may be repeated. Useful for smoke tests.")
    parser.add_argument("--retries", type=int, default=3, help="External retries for runner failures that do not produce run.json.")
    parser.add_argument("--no-resume", action="store_true", help="Ignore existing per-profile logs and start a fresh cascade for this output directory.")
    args = parser.parse_args()

    write_outputs(args.output)
    if args.execute:
        execute_cascade(args.output, args.limit_profiles, args.limit_tasks, args.jobs, args.model, args.base_url, args.task_ref, args.retries, not args.no_resume)
    else:
        write_cascade_summary(args.output)
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
