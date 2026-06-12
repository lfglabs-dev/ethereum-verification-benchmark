"""Profile-driven shell-agent harness runner.

Runs a generic coding-agent CLI (opencode, ...) against a generated group
workspace, metering all model traffic through a local OpenAI-compatible
proxy so token usage and budgets are comparable with the builtin harness.
The independent verifier scores the result exactly like every other harness.

Profiles live in harness/agents/<id>.json with `"adapter": "shell"`:

  {
    "agent_id": "opencode",
    "adapter": "shell",
    "track": "group/shell",
    "command": ["opencode", "run", "--model", "verity/{model}", "{prompt}"],
    "env": {"OPENCODE_CONFIG": "{workspace}/opencode.json"},
    "config_files": {"opencode.json": "{...template with {proxy_url}/{model}...}"},
    "version_command": ["opencode", "--version"]
  }

Placeholders available in command/env/config templates:
  {model} {workspace} {prompt} {prompt_file} {proxy_url} {proxy_key} {home}
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
import shutil
import signal
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

try:
    from ..manifests import Group, filter_group_to_task, group_id_from_task_ref, group_to_json, load_group
    from ..metering_proxy import MeteringProxy
    from ..paths import RESULTS_DIR, ROOT
    from ..reports import write_run_report
    from ..verifier import verify_group
    from ..workspace_builder import agent_group_to_json, assert_workspace_isolated, build_group_workspace
except ImportError:
    from manifests import Group, filter_group_to_task, group_id_from_task_ref, group_to_json, load_group
    from metering_proxy import MeteringProxy
    from paths import RESULTS_DIR, ROOT
    from reports import write_run_report
    from verifier import verify_group
    from workspace_builder import agent_group_to_json, assert_workspace_isolated, build_group_workspace


def load_profile(harness_id: str) -> dict[str, object]:
    path = ROOT / "harness" / "agents" / f"{harness_id}.json"
    profile = json.loads(path.read_text(encoding="utf-8"))
    if profile.get("adapter") != "shell":
        raise ValueError(f"agent profile {harness_id} is not a shell adapter")
    return profile


def _prompt(group: Group) -> str:
    return (
        "You are solving a Verity Lean benchmark group inside this workspace.\n"
        "Start by reading harness/TASK_SUMMARY.md; it contains the target theorem, editable files, policy, "
        "the current editable theorem skeleton, and harness/PROOF_PATTERNS.md documents the Verity proving recipe.\n"
        "Edit only files listed as editable in harness/TASKS.json. Keep the theorem statement byte-identical; "
        "only replace the proof after := by (helper lemmas in the same file are allowed).\n"
        "Do not import hidden Proofs modules or Benchmark/GeneratedPreview. Do not use sorry, admit, or axiom.\n"
        "Check your proof by running: lake env lean <editable-file.lean> (fast) or ./harness/check.sh (full).\n"
        "Iterate until Lean reports no errors, then stop.\n"
    )


def _expand(value: str, substitutions: dict[str, str]) -> str:
    for key, replacement in substitutions.items():
        value = value.replace("{" + key + "}", replacement)
    return value


def run_group(
    group_id: str,
    *,
    harness_id: str,
    model: str,
    suite: str = "active",
    keep_workspace: bool = False,
    timeout_seconds: int = 2400,
    token_budget: int = 0,
    task_ref: str | None = None,
    dry_run: bool = False,
) -> tuple[int, Path]:
    profile = load_profile(harness_id)
    start = time.time()
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_subject = task_ref or group_id
    model_slug = "".join(ch if ch.isalnum() else "-" for ch in model).strip("-").lower()
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{harness_id}-{model_slug}-{run_subject.replace('/', '__')}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    group = load_group(group_id, suite)
    if task_ref:
        group = filter_group_to_task(group, task_ref)
    # Refuse to benchmark from a dirty source tree: a previous harness escape
    # (or manual edit) could pre-solve the editable file and contaminate runs.
    dirty = [
        rel
        for task in group.tasks
        for rel in task.editable_files
        if subprocess.run(["git", "diff", "--quiet", "HEAD", "--", rel], cwd=ROOT, check=False).returncode != 0
    ]
    if dirty:
        raise RuntimeError(f"editable files modified in source repo (restore before benchmarking): {', '.join(dirty)}")
    built = build_group_workspace(group, run_id=run_id)
    assert_workspace_isolated(built.path)
    initial_editable: dict[str, str] = {}
    for task in group.tasks:
        for rel in task.editable_files:
            path = built.path / rel
            if path.is_file():
                initial_editable[rel] = path.read_text(encoding="utf-8")

    # Warm the Lean build once so agent check latency measures proofs, not deps.
    warm: dict[str, object] = {"status": "skipped_dry_run"}
    if not dry_run:
        warm_started = time.time()
        warm_timeout = int(os.environ.get("DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS", "1800"))
        completed = subprocess.run(
            ["./harness/check.sh"], cwd=built.path, capture_output=True, text=True, check=False, timeout=warm_timeout
        )
        warm = {
            "status": "passed" if completed.returncode == 0 else "failed",
            "exit_code": completed.returncode,
            "duration_seconds": round(time.time() - warm_started, 3),
        }

    upstream = os.environ.get("DEFAULT_HARNESS_BASE_URL", "")
    api_key = os.environ.get("DEFAULT_HARNESS_API_KEY")
    proxy = MeteringProxy(
        upstream,
        api_key,
        usage_path=run_dir / "usage.json",
        completion_token_budget=token_budget,
        user_agent=os.environ.get("DEFAULT_HARNESS_HTTP_USER_AGENT", "verity-benchmark-harness/1.0"),
    )
    proxy.start()
    fake_home = Path(tempfile.mkdtemp(prefix=f"verity-{harness_id}-home-"))
    prompt_file = built.path / "harness" / f"PROMPT.{harness_id}.md"
    prompt_file.write_text(_prompt(group), encoding="utf-8")
    substitutions = {
        "model": model,
        "workspace": str(built.path),
        "prompt": _prompt(group),
        "prompt_file": str(prompt_file),
        "proxy_url": proxy.base_url,
        "proxy_key": proxy.local_key,
        "home": str(fake_home),
    }
    for rel, template in (profile.get("config_files") or {}).items():
        rel = _expand(str(rel), substitutions)
        # "~/..." config files land in the isolated HOME (auth/config the agent
        # should use but not see in its workspace); everything else in the workspace.
        target = (fake_home / rel[2:]) if rel.startswith("~/") else (built.path / rel)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(_expand(str(template), substitutions), encoding="utf-8")
    host_auth = profile.get("host_auth")
    auth_mode = "proxy"
    if isinstance(host_auth, dict):
        flag = str(host_auth.get("env_flag") or "")
        source = Path(str(host_auth.get("source") or "")).expanduser()
        if flag and os.environ.get(flag) == "1" and source.is_file():
            dest = fake_home / str(host_auth.get("dest") or source.name)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, dest)
            auth_mode = "host-auth"
        else:
            proxy.stop()
            shutil.rmtree(fake_home, ignore_errors=True)
            raise RuntimeError(
                f"harness {harness_id} requires host auth: set {flag}=1 with {source} present"
            )
    command = [_expand(str(part), substitutions) for part in profile["command"]]
    env = os.environ.copy()
    env["HOME"] = str(fake_home)
    env["PWD"] = str(built.path)  # some CLIs trust $PWD over getcwd
    env["OLDPWD"] = str(built.path)
    for key in list(env):
        if key.startswith(("DEFAULT_HARNESS_", "OPENAI_", "GAZELLA_", "OPENCODE_")):
            env.pop(key)
    for key, template in (profile.get("env") or {}).items():
        env[str(key)] = _expand(str(template), substitutions)

    def _run_cli(cli_command: list[str], remaining_seconds: float) -> tuple[int, str, str]:
        process: subprocess.Popen[str] | None = None
        try:
            process = subprocess.Popen(
                cli_command,
                cwd=built.path,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                env=env,
                start_new_session=True,
            )
            out, err = process.communicate(timeout=max(30, remaining_seconds))
            return process.returncode, out, err
        except subprocess.TimeoutExpired:
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                out, err = process.communicate()
                return 124, out, err
            return 124, "", ""

    def _quick_check() -> tuple[bool, str]:
        completed = subprocess.run(
            ["./harness/check.sh"], cwd=built.path, capture_output=True, text=True, check=False, timeout=600
        )
        output = (completed.stdout + completed.stderr).strip()
        return completed.returncode == 0, output[-1500:]

    stdout = stderr = ""
    return_code = 0
    harness_status = "dry_run"
    invocations: list[dict[str, object]] = []
    max_invocations = int(os.environ.get("SHELL_AGENT_MAX_INVOCATIONS", "6"))
    continue_template = profile.get("continue_command")
    if not dry_run:
        deadline = time.time() + timeout_seconds
        for invocation_index in range(1, max_invocations + 1):
            cli_command = command
            if invocation_index > 1 and isinstance(continue_template, list):
                passed, check_tail = _quick_check()
                if passed:
                    harness_status = "completed"
                    break
                continue_subs = substitutions | {
                    "continue_prompt": (
                        "The Lean check still fails. Latest output tail:\n"
                        f"{check_tail}\n"
                        "Continue fixing the proof in the editable file until ./harness/check.sh passes. "
                        "Keep the theorem statement byte-identical; no sorry/admit/axiom."
                    )
                }
                cli_command = [_expand(str(part), continue_subs) for part in continue_template]
            elif invocation_index > 1:
                break
            started_invocation = time.time()
            return_code, out, err = _run_cli(cli_command, deadline - time.time())
            stdout += out
            stderr += err
            invocations.append(
                {
                    "index": invocation_index,
                    "exit_code": return_code,
                    "duration_seconds": round(time.time() - started_invocation, 3),
                }
            )
            harness_status = "completed" if return_code == 0 else ("timeout" if return_code == 124 else "harness_error")
            if return_code == 124 or time.time() >= deadline or proxy.budget_exhausted():
                break
            # A non-zero exit only ends the loop when there is no configured
            # continue path; otherwise the next iteration re-checks and resumes.
            if return_code != 0 and not isinstance(continue_template, list):
                break
    proxy.stop()
    shutil.rmtree(fake_home, ignore_errors=True)

    usage = dict(proxy.usage)
    usage_source = "metered"
    usage_pattern = profile.get("usage_pattern")
    if isinstance(usage_pattern, str) and usage["total_tokens"] == 0:
        import re

        total = 0
        for match in re.finditer(usage_pattern, stdout + "\n" + stderr):
            total += int(re.sub(r"[^\d]", "", match.group(1)))
        if total:
            usage = {"prompt_tokens": None, "completion_tokens": None, "total_tokens": total, "requests": None}
            usage_source = "self-reported"

    (run_dir / "stdout.txt").write_text(stdout or "", encoding="utf-8")
    (run_dir / "stderr.txt").write_text(stderr or "", encoding="utf-8")
    shutil.copy2(built.manifest_path, run_dir / "workspace-manifest.json")
    shutil.copy2(built.path / "harness" / "TASK_SUMMARY.md", run_dir / "TASK_SUMMARY.md")

    chunks: list[str] = []
    submitted_dir = run_dir / "submitted"
    for task in group.tasks:
        for rel in task.editable_files:
            src = built.path / rel
            after = src.read_text(encoding="utf-8") if src.is_file() else ""
            before = initial_editable.get(rel, "")
            if before != after:
                chunks.extend(
                    difflib.unified_diff(
                        before.splitlines(keepends=True), after.splitlines(keepends=True), fromfile=f"a/{rel}", tofile=f"b/{rel}"
                    )
                )
            if src.is_file():
                dst = submitted_dir / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
    (run_dir / "workspace.diff").write_text("".join(chunks), encoding="utf-8")

    verifier_result = verify_group(group, built.path, artifact_dir=run_dir / "verifier")
    version = None
    version_command = profile.get("version_command")
    if isinstance(version_command, list):
        probe = subprocess.run([str(part) for part in version_command], capture_output=True, text=True, check=False)
        version = (probe.stdout or probe.stderr).strip().splitlines()[0] if (probe.stdout or probe.stderr).strip() else None
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": harness_id,
        "harness_version": version,
        "model": model,
        "provider": "proxy",
        "track": profile.get("track", "group/shell"),
        "mode": "shell",
        "run_mode": "task" if task_ref else "group",
        "group_id": group_id,
        "task_ref": task_ref,
        "suite": suite,
        "started_at": started_at,
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": harness_status,
        "harness_exit_code": return_code,
        "invocations": invocations,
        "timeout_seconds": timeout_seconds,
        "warm_build": warm,
        "auth_mode": auth_mode,
        "usage": usage,
        "usage_source": usage_source,
        "token_budget": token_budget,
        "workspace": str(built.path) if keep_workspace else None,
        "verifier": verifier_result,
    }
    (run_dir / "harness-response.json").write_text(
        json.dumps({"status": harness_status, "command": command, "tasks": [{"task_ref": task_ref or group_id, "usage": usage}]}, indent=2) + "\n",
        encoding="utf-8",
    )
    (run_dir / "harness-request.json").write_text(
        json.dumps({"group": agent_group_to_json(group), "command": command, "model": model, "timeout_seconds": timeout_seconds}, indent=2) + "\n",
        encoding="utf-8",
    )
    (run_dir / "run.json").write_text(json.dumps(run, indent=2) + "\n", encoding="utf-8")
    write_run_report(run_dir, run)
    if not keep_workspace:
        shutil.rmtree(built.path, ignore_errors=True)
    score = verifier_result["score"]
    return (0 if score["passed_targets"] == score["total_targets"] and score["total_targets"] > 0 else 1), run_dir


def main() -> int:
    parser = argparse.ArgumentParser(description="Run a shell-agent harness on a benchmark group/task")
    parser.add_argument("group_id", nargs="?")
    parser.add_argument("--harness", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--task-ref")
    parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    parser.add_argument("--keep-workspace", action="store_true")
    parser.add_argument("--timeout-seconds", type=int, default=2400)
    parser.add_argument("--token-budget", type=int, default=0)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    group_id = group_id_from_task_ref(args.task_ref) if args.task_ref else args.group_id
    if not group_id:
        parser.error("group_id or --task-ref required")
    code, run_dir = run_group(
        group_id,
        harness_id=args.harness,
        model=args.model,
        suite=args.suite,
        keep_workspace=args.keep_workspace,
        timeout_seconds=args.timeout_seconds,
        token_budget=args.token_budget,
        task_ref=args.task_ref,
        dry_run=args.dry_run,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
