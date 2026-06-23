#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import csv
import json
import os
import re
import signal
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO / "output" / "budget_scaling_minimax_remaining_85"
PUBLISHED_OUTPUT = REPO / "analysis" / "budget_scaling_minimax_50"
DEFAULT_MODEL = "MiniMax-M3"
DEFAULT_BASE_URL = "https://api.minimax.io/v1"
EXTERNAL_TIMEOUT_FLOOR_SECONDS = int(os.environ.get("MINIMAX_CASCADE_EXTERNAL_TIMEOUT_FLOOR_SECONDS", "21600"))
RATE_LIMIT_SLEEP_SECONDS = int(os.environ.get("MINIMAX_CASCADE_RATE_LIMIT_SLEEP_SECONDS", "1800"))
TRANSIENT_SLEEP_SECONDS = int(os.environ.get("MINIMAX_CASCADE_TRANSIENT_SLEEP_SECONDS", "300"))


class FatalProviderSetupError(RuntimeError):
    pass


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


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def git_json(path: str) -> object:
    result = subprocess.run(
        ["git", "show", f"v0.1:{path}"],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=True,
    )
    return json.loads(result.stdout)


def write_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def task_metadata() -> dict[str, dict]:
    version = git_json("benchmark-versions/v0.1.json")
    return {task["task_ref"]: task for task in version["tasks"]}  # type: ignore[index]


def published_selected() -> list[dict]:
    local_path = PUBLISHED_OUTPUT / "selected_tasks.json"
    if local_path.is_file():
        return load_json(local_path)  # type: ignore[return-value]
    return git_json("analysis/budget_scaling_minimax_50/selected_tasks.json")  # type: ignore[return-value]


def published_results() -> list[dict]:
    local_path = PUBLISHED_OUTPUT / "cascade_results.json"
    if local_path.is_file():
        return load_json(local_path)  # type: ignore[return-value]
    return git_json("analysis/budget_scaling_minimax_50/cascade_results.json")  # type: ignore[return-value]


def complement_tasks() -> list[dict]:
    selected = {item["task_ref"] for item in published_selected()}
    meta = task_metadata()
    remaining = [item for task_ref, item in sorted(meta.items()) if task_ref not in selected]
    for index, item in enumerate(remaining, start=1):
        item["rank"] = index
        item["selection_source"] = "v0.1_complement_of_published_50"
    return remaining


def is_solved_run(run_dir: Path) -> bool:
    run = load_json(run_dir / "run.json")
    score = run.get("verifier", {}).get("score", {})  # type: ignore[union-attr]
    return int(score.get("passed_targets", 0)) > 0 and int(score.get("passed_targets", 0)) == int(score.get("total_targets", 1))


def usage_from_run_dir(run_dir: Path) -> dict:
    run = load_json(run_dir / "run.json")
    usage = run.get("usage") or {}  # type: ignore[union-attr]
    return {
        "prompt_tokens": int(usage.get("prompt_tokens", 0) or 0),
        "completion_tokens": int(usage.get("completion_tokens", 0) or 0),
        "total_tokens": int(usage.get("total_tokens", 0) or 0),
        "requests": int(usage.get("requests", 0) or 0),
    }


def harness_response_from_run_dir(run_dir: Path) -> dict:
    response_path = run_dir / "harness-response.json"
    if not response_path.is_file():
        return {}
    response = load_json(response_path)
    return response if isinstance(response, dict) else {}


def provider_setup_error_text(text: str) -> str | None:
    lowered = text.lower()
    fatal_markers = (
        "http_error 401",
        "http 401",
        " 401 ",
        "unauthorized",
        "login fail",
        "api secret key",
        "authorization",
        "http_error 403",
        "http 403",
        " 403 ",
        "forbidden",
        "invalid api key",
        "invalid_api_key",
        "insufficient balance",
        "quota exceeded",
    )
    if any(marker in lowered for marker in fatal_markers) and not is_rate_limited(text):
        return "provider_setup_error"
    return None


def provider_setup_error_from_run_dir(run_dir: Path) -> str | None:
    response = harness_response_from_run_dir(run_dir)
    if response.get("status") != "harness_error":
        return None
    return provider_setup_error_text(json.dumps(response, sort_keys=True))


def is_valid_model_row(row: dict) -> bool:
    if row.get("skipped_already_solved"):
        return True
    if row.get("provider_setup_error"):
        return False
    if int(row.get("requests", 0) or 0) > 0:
        return True
    return bool(row.get("passed"))


def row_from_run_dir(task_ref: str, profile: BudgetProfile, run_dir: str, *, recovered: bool = False) -> dict | None:
    path = Path(run_dir)
    if not path.is_dir() or not (path / "run.json").is_file():
        return None
    setup_error = provider_setup_error_from_run_dir(path)
    row = {
        "profile": profile.name,
        "task_ref": task_ref,
        "returncode": 0,
        "run_dir": str(path),
        "skipped_already_solved": False,
        "passed": is_solved_run(path),
    }
    if recovered:
        row["recovered_from_logs"] = True
    row.update(usage_from_run_dir(path))
    if setup_error:
        row["provider_setup_error"] = setup_error
    return row


def run_dir_from_stdout(stdout: str) -> str | None:
    for line in reversed(stdout.splitlines()):
        stripped = line.strip()
        if stripped.startswith("/") and "/results/runs/" in stripped:
            return stripped
    return None


def retry_after_seconds(text: str) -> int | None:
    match = re.search(r"retry-after['\"]?\s*[:=]\s*['\"]?(\d+)", text, re.IGNORECASE)
    if not match:
        return None
    return int(match.group(1))


def is_rate_limited(text: str) -> bool:
    lowered = text.lower()
    return any(
        marker in lowered
        for marker in (
            "http 429",
            "error 429",
            " 429 ",
            "too many requests",
            "rate limit",
            "rate_limit",
            "ratelimit",
            "retry-after",
        )
    )


def is_transient_failure(text: str, returncode: int) -> bool:
    lowered = text.lower()
    if returncode == 124:
        return True
    return any(
        marker in lowered
        for marker in (
            "request_timeout",
            "timed out",
            "timeout",
            "temporarily unavailable",
            "connection reset",
            "connection aborted",
            "remote end closed connection",
            "http 408",
            "http 409",
            "http 425",
            "http 500",
            "http 502",
            "http 503",
            "http 504",
            "http 520",
            "http 521",
            "http 522",
            "http 523",
            "http 524",
        )
    )


def is_retryable_harness_response(response: dict, returncode: int) -> bool:
    """Classify only harness/provider failures as retryable.

    A completed harness response with a failed proof is a benchmark result, even
    when the Lean diagnostic contains words like "timeout". Retrying those rows
    forever biases the scaling cascade and can prevent profile checkpoints.
    """
    if response.get("status") == "completed":
        return False
    response_text = json.dumps(response, sort_keys=True)
    return is_rate_limited(response_text) or is_transient_failure(response_text, returncode)


def sleep_for_retry(combined_output: str, returncode: int, runner_attempt: int) -> None:
    if is_rate_limited(combined_output):
        delay = max(retry_after_seconds(combined_output) or 0, RATE_LIMIT_SLEEP_SECONDS)
    elif is_transient_failure(combined_output, returncode):
        delay = min(3600, TRANSIENT_SLEEP_SECONDS * runner_attempt)
    else:
        delay = min(300, 2**runner_attempt)
    print(f"retrying after {delay}s (attempt={runner_attempt}, returncode={returncode})", flush=True)
    time.sleep(delay)


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


def minimax_env(model: str, base_url: str) -> dict[str, str]:
    env = os.environ.copy()
    explicit_key = env.get("MINIMAX_API_KEY") or env.get("DEFAULT_HARNESS_MINIMAX_API_KEY")
    if explicit_key:
        env["DEFAULT_HARNESS_API_KEY"] = explicit_key
    env["DEFAULT_HARNESS_MODEL"] = model
    env["DEFAULT_HARNESS_BASE_URL"] = base_url
    env.pop("DEFAULT_HARNESS_PROVIDER", None)
    env.pop("GAZELLA_API_KEY", None)
    env.pop("OPENAI_API_KEY", None)
    return env


def preflight_provider(model: str, base_url: str) -> None:
    env = minimax_env(model, base_url)
    if not env.get("DEFAULT_HARNESS_API_KEY"):
        raise FatalProviderSetupError("MINIMAX_API_KEY or DEFAULT_HARNESS_API_KEY must be set before running MiniMax cascade")
    smoke_code = (
        "import json\n"
        "from harness.transport import endpoint_smoke, DEFAULT_BASE_URL, DEFAULT_MODEL\n"
        "data = endpoint_smoke(DEFAULT_BASE_URL, DEFAULT_MODEL)\n"
        "print(json.dumps({'choices': len(data.get('choices', [])), 'usage': data.get('usage')}))\n"
    )
    result = subprocess.run(
        ["python3", "-c", smoke_code],
        cwd=REPO,
        env=env,
        text=True,
        capture_output=True,
        timeout=180,
        check=False,
    )
    combined = f"{result.stdout}\n{result.stderr}"
    if result.returncode != 0:
        setup_error = provider_setup_error_text(combined) or "provider_preflight_failed"
        raise FatalProviderSetupError(f"{setup_error}; MiniMax smoke test failed before cascade launch")
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise FatalProviderSetupError(f"provider_preflight_failed; smoke test returned non-JSON: {exc}") from exc
    if not isinstance(payload, dict) or not payload.get("choices"):
        raise FatalProviderSetupError("provider_preflight_failed; smoke test returned no choices")


def target_module(task_ref: str) -> str | None:
    inventory = load_json(REPO / "benchmark-inventory.json")
    for task in inventory.get("tasks", []):  # type: ignore[union-attr]
        if task.get("task_ref") != task_ref:
            continue
        editable_files = task.get("editable_files") or []
        if len(editable_files) != 1:
            return None
        path = Path(editable_files[0])
        if path.suffix != ".lean":
            return None
        return ".".join(path.with_suffix("").parts)
    return None


def cleanup_detached_task_build(task_ref: str) -> None:
    # The harness is launched in its own process group, so killing that group is
    # the safe cleanup boundary. Avoid process-argument scans: provider keys can
    # be present in benchmark environments on shared machines.
    _ = task_ref


def recover_rows(output: Path, selected: list[dict], profiles: list[BudgetProfile]) -> list[dict]:
    by_safe_name = {item["task_ref"].replace("/", "__"): item["task_ref"] for item in selected}
    rows: dict[tuple[str, str], dict] = {}
    for profile in profiles:
        profile_dir = output / "runs" / profile.name
        if not profile_dir.is_dir():
            continue
        for stdout_path in sorted(profile_dir.glob("*.stdout.txt")):
            task_ref = by_safe_name.get(stdout_path.name.removesuffix(".stdout.txt"))
            if not task_ref:
                continue
            run_dir = run_dir_from_stdout(stdout_path.read_text(encoding="utf-8", errors="replace"))
            if not run_dir:
                continue
            row = row_from_run_dir(task_ref, profile, run_dir, recovered=True)
            if row:
                rows[(profile.name, task_ref)] = row
    existing = output / "cascade_results.json"
    if existing.is_file():
        for row in load_json(existing):  # type: ignore[union-attr]
            rows[(row["profile"], row["task_ref"])] = row
    return sorted(rows.values(), key=lambda row: (profile_index(row["profile"]), task_index(selected, row["task_ref"])))


def profile_index(profile_name: str) -> int:
    return next((index for index, profile in enumerate(PROFILES) if profile.name == profile_name), 10**9)


def task_index(selected: list[dict], task_ref: str) -> int:
    return next((index for index, item in enumerate(selected) if item["task_ref"] == task_ref), 10**9)


def run_one_task(
    task_ref: str,
    profile: BudgetProfile,
    profile_dir: Path,
    model: str,
    base_url: str,
    retries: int,
    retry_forever: bool,
) -> dict:
    env = minimax_env(model, base_url)
    safe_name = task_ref.replace("/", "__")
    stdout_chunks: list[str] = []
    stderr_chunks: list[str] = []
    row: dict = {
        "profile": profile.name,
        "task_ref": task_ref,
        "returncode": 1,
        "run_dir": "",
        "skipped_already_solved": False,
        "passed": False,
    }
    attempt = 0
    while True:
        attempt += 1
        process = subprocess.Popen(
            command_args(task_ref, profile),
            cwd=REPO,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
        external_timeout = max(profile.shell_timeout_seconds + 3600, EXTERNAL_TIMEOUT_FLOOR_SECONDS)
        try:
            stdout, stderr = process.communicate(timeout=external_timeout)
            returncode = process.returncode
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                stdout, stderr = process.communicate()
            cleanup_detached_task_build(task_ref)
            returncode = 124
            stderr += f"\nexternal timeout after {external_timeout}s\n"
        stdout_chunks.append(f"--- runner attempt {attempt} ---\n{stdout}")
        stderr_chunks.append(f"--- runner attempt {attempt} ---\n{stderr}")
        run_dir = run_dir_from_stdout(stdout) or ""
        row.update({"returncode": returncode, "run_dir": run_dir, "runner_attempts": attempt})
        run_row = row_from_run_dir(task_ref, profile, run_dir) if run_dir else None
        if run_row:
            run_row["returncode"] = returncode
            run_row["runner_attempts"] = attempt
            if run_row.get("provider_setup_error"):
                raise FatalProviderSetupError(
                    f"{task_ref} {profile.name}: provider setup failed; inspect {run_dir}/harness-response.json"
                )
            response = harness_response_from_run_dir(Path(run_dir))
            if is_retryable_harness_response(response, returncode):
                response_text = json.dumps(response, sort_keys=True)
                row.update(run_row)
                row["rate_limited"] = is_rate_limited(response_text)
                retryable = True
                attempts_left = retry_forever or attempt <= retries
                if attempts_left:
                    sleep_for_retry(response_text, returncode, attempt)
                    continue
                row["retry_exhausted"] = True
                break
            row.update(run_row)
            break
        combined_output = f"{stdout}\n{stderr}"
        setup_error = provider_setup_error_text(combined_output)
        if setup_error:
            raise FatalProviderSetupError(f"{task_ref} {profile.name}: {setup_error}")
        if is_rate_limited(combined_output):
            row["rate_limited"] = True
        if returncode == 124:
            row["external_timeout"] = True
        retryable = is_rate_limited(combined_output) or is_transient_failure(combined_output, returncode)
        attempts_left = retry_forever or attempt <= retries
        if retryable and attempts_left:
            sleep_for_retry(combined_output, returncode, attempt)
            continue
        if retryable:
            row["retry_exhausted"] = True
            break
        if attempt <= retries:
            sleep_for_retry(combined_output, returncode, attempt)
            continue
        break
    (profile_dir / f"{safe_name}.stdout.txt").write_text("\n".join(stdout_chunks), encoding="utf-8")
    (profile_dir / f"{safe_name}.stderr.txt").write_text("\n".join(stderr_chunks), encoding="utf-8")
    return row


def write_selected(output: Path, selected: list[dict]) -> None:
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "profiles.json", [asdict(profile) for profile in PROFILES])
    write_json(output / "selected_tasks.json", selected)
    with (output / "selected_tasks.csv").open("w", encoding="utf-8", newline="") as handle:
        fields = ["rank", "task_ref", "selection_source", "difficulty", "property_class", "proof_family"]
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for item in selected:
            writer.writerow({field: item.get(field) for field in fields})


def write_summary(output: Path, rows: list[dict], selected: list[dict], *, name: str = "cascade") -> list[dict]:
    task_count = len(selected)
    solved: set[str] = set()
    summary: list[dict] = []
    cumulative_prompt = cumulative_completion = cumulative_total = cumulative_requests = 0
    for profile in PROFILES:
        profile_rows = [row for row in rows if row.get("profile") == profile.name]
        newly_solved = sorted(row["task_ref"] for row in profile_rows if row.get("passed") and row["task_ref"] not in solved)
        solved.update(newly_solved)
        profile_prompt = sum(int(row.get("prompt_tokens", 0) or 0) for row in profile_rows)
        profile_completion = sum(int(row.get("completion_tokens", 0) or 0) for row in profile_rows)
        profile_total = sum(int(row.get("total_tokens", 0) or 0) for row in profile_rows)
        profile_requests = sum(int(row.get("requests", 0) or 0) for row in profile_rows)
        cumulative_prompt += profile_prompt
        cumulative_completion += profile_completion
        cumulative_total += profile_total
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
                "task_count": task_count,
                "solve_rate": round(len(solved) / task_count, 4) if task_count else 0,
                "profile_prompt_tokens": profile_prompt,
                "profile_completion_tokens": profile_completion,
                "profile_total_tokens": profile_total,
                "profile_requests": profile_requests,
                "cumulative_prompt_tokens": cumulative_prompt,
                "cumulative_completion_tokens": cumulative_completion,
                "cumulative_total_tokens": cumulative_total,
                "cumulative_requests": cumulative_requests,
            }
        )
    with (output / f"{name}_summary.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(summary[0].keys()))
        writer.writeheader()
        writer.writerows(summary)
    write_json(output / f"{name}_summary.json", summary)
    return summary


def solve_events(rows: list[dict], selected: list[dict]) -> list[dict]:
    events: list[dict] = []
    for item in selected:
        task_ref = item["task_ref"]
        task_rows = sorted([row for row in rows if row.get("task_ref") == task_ref], key=lambda row: profile_index(row["profile"]))
        solved_row = next((row for row in task_rows if row.get("passed")), None)
        spent_total = sum(int(row.get("total_tokens", 0) or 0) for row in task_rows if solved_row is None or profile_index(row["profile"]) <= profile_index(solved_row["profile"]))
        spent_completion = sum(int(row.get("completion_tokens", 0) or 0) for row in task_rows if solved_row is None or profile_index(row["profile"]) <= profile_index(solved_row["profile"]))
        events.append(
            {
                "task_ref": task_ref,
                "solved": bool(solved_row),
                "solved_profile": solved_row.get("profile") if solved_row else "",
                "observed_total_tokens_to_solve": spent_total,
                "observed_completion_tokens_to_solve": spent_completion,
                "attempted_profiles": len(task_rows),
            }
        )
    return events


def write_events(output: Path, rows: list[dict], selected: list[dict], name: str) -> None:
    events = solve_events(rows, selected)
    with (output / f"{name}_solve_events.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(events[0].keys()))
        writer.writeheader()
        writer.writerows(events)
    write_json(output / f"{name}_solve_events.json", events)


def write_combined(output: Path, complement_rows: list[dict], complement_selected: list[dict]) -> None:
    published_rows = published_results()
    published_tasks = published_selected()
    combined_rows = [*published_rows, *complement_rows]
    combined_selected = [*published_tasks, *complement_selected]
    write_json(output / "combined_135_cascade_results.json", combined_rows)
    write_summary(output, combined_rows, combined_selected, name="combined_135_cascade")
    write_events(output, combined_rows, combined_selected, "combined_135_cascade")


def execute(args: argparse.Namespace) -> None:
    output = Path(args.output)
    preflight_provider(args.model, args.base_url)
    selected = complement_tasks()
    if args.limit_tasks:
        selected = selected[: args.limit_tasks]
    profiles = PROFILES[: args.limit_profiles or len(PROFILES)]
    write_selected(output, selected)
    rows = recover_rows(output, selected, profiles) if args.resume else []
    invalid_rows = [row for row in rows if not is_valid_model_row(row)]
    if invalid_rows:
        raise FatalProviderSetupError(
            f"refusing to resume with {len(invalid_rows)} invalid provider/setup rows; "
            f"move or delete {output / 'cascade_results.json'} and rerun after preflight passes"
        )
    for profile in profiles:
        solved_before = {row["task_ref"] for row in rows if row.get("passed") and profile_index(row["profile"]) < profile_index(profile.name)}
        executed_here = {row["task_ref"] for row in rows if row.get("profile") == profile.name and not row.get("skipped_already_solved")}
        pending = [item["task_ref"] for item in selected if item["task_ref"] not in solved_before and item["task_ref"] not in executed_here]
        profile_dir = output / "runs" / profile.name
        profile_dir.mkdir(parents=True, exist_ok=True)
        if pending and args.execute:
            if args.jobs == 1:
                for task in pending:
                    row = run_one_task(task, profile, profile_dir, args.model, args.base_url, args.retries, args.retry_forever)
                    rows.append(row)
                    write_json(output / "cascade_results.json", rows)
            else:
                with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
                    futures = {
                        pool.submit(
                            run_one_task,
                            task,
                            profile,
                            profile_dir,
                            args.model,
                            args.base_url,
                            args.retries,
                            args.retry_forever,
                        ): task
                        for task in pending
                    }
                    for future in concurrent.futures.as_completed(futures):
                        rows.append(future.result())
                        rows.sort(key=lambda row: (profile_index(row["profile"]), task_index(selected, row["task_ref"])))
                        write_json(output / "cascade_results.json", rows)
        write_json(output / "cascade_results.json", rows)
        write_summary(output, rows, selected)
        write_events(output, rows, selected, "cascade")
        write_combined(output, rows, selected)
        print(f"{profile.name}: pending={len(pending)} rows={len(rows)} solved={sum(1 for item in solve_events(rows, selected) if item['solved'])}/{len(selected)}", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL)
    parser.add_argument("--retries", type=int, default=1)
    parser.add_argument("--retry-forever", action="store_true")
    parser.add_argument("--limit-profiles", type=int)
    parser.add_argument("--limit-tasks", type=int)
    parser.add_argument("--no-resume", dest="resume", action="store_false")
    args = parser.parse_args()
    execute(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
