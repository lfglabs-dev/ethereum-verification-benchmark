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
    from ..classification import classify_run
    from ..identity import HARNESS_USER_AGENT
    from ..lean_lsp_mcp_client import LeanLspMcpSession
    from ..manifests import Group, filter_group_to_task, group_id_from_task_ref, group_to_json, load_group
    from ..metering_proxy import MeteringProxy
    from ..budgets import dependency_warm_timeout_seconds, operational_budget
    from ..paths import RESULTS_DIR, ROOT
    from ..reports import write_run_report
    from ..transport import generic_preflight
    from ..verifier import setup_failure_verifier_result, verify_group
    from ..workspace_builder import (
        agent_group_to_json,
        assert_workspace_isolated,
        build_group_workspace,
        warm_public_dependencies,
        warm_result_failed,
    )
except ImportError:
    from classification import classify_run
    from identity import HARNESS_USER_AGENT
    from lean_lsp_mcp_client import LeanLspMcpSession
    from manifests import Group, filter_group_to_task, group_id_from_task_ref, group_to_json, load_group
    from metering_proxy import MeteringProxy
    from budgets import dependency_warm_timeout_seconds, operational_budget
    from paths import RESULTS_DIR, ROOT
    from reports import write_run_report
    from transport import generic_preflight
    from verifier import setup_failure_verifier_result, verify_group
    from workspace_builder import (
        agent_group_to_json,
        assert_workspace_isolated,
        build_group_workspace,
        warm_public_dependencies,
        warm_result_failed,
    )


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
        "Do not run a broad `lake build`: this isolated workspace intentionally omits the aggregate "
        "Benchmark.lean entry point. Prefer available Lean MCP diagnostics/goals tools, and only check the "
        "exact editable file or ./harness/check.sh.\n"
        "Check your proof by running: lake env lean <editable-file.lean> (fast) or ./harness/check.sh (full).\n"
        "Iterate until Lean reports no errors, then stop.\n"
    )


def _expand(value: str, substitutions: dict[str, str]) -> str:
    for key, replacement in substitutions.items():
        value = value.replace("{" + key + "}", replacement)
    return value


def _run_profile_preflights(
    profile: dict[str, object],
    *,
    cwd: Path,
    timeout_seconds: int = 180,
) -> list[dict[str, object]]:
    """Resolve pinned agent/MCP executables before expensive Lean setup.

    A missing CLI must become a zero-request infrastructure artifact rather
    than failing after the metering proxy and provider path are live.
    """
    results: list[dict[str, object]] = []
    raw_commands = profile.get("preflight_commands")
    if raw_commands is None:
        version_command = profile.get("version_command")
        raw_commands = [version_command] if version_command is not None else []
    if not isinstance(raw_commands, list):
        raise ValueError("preflight_commands must be a list")
    for raw in raw_commands:
        if not isinstance(raw, list) or not raw or not all(isinstance(part, str) for part in raw):
            raise ValueError("each preflight command must be a non-empty string list")
        command = [str(part) for part in raw]
        started = time.time()
        try:
            completed = _run_setup_process_group(
                command,
                cwd=cwd,
                timeout_seconds=timeout_seconds,
            )
            output = (completed.stdout + completed.stderr).strip()
            result = {
                "command": command,
                "status": "passed" if completed.returncode == 0 else "failed",
                "exit_code": completed.returncode,
                "duration_seconds": round(time.time() - started, 3),
                "output_tail": output[-1200:],
            }
        except (OSError, subprocess.TimeoutExpired) as exc:
            result = {
                "command": command,
                "status": "failed",
                "exit_code": 127 if isinstance(exc, OSError) else 124,
                "duration_seconds": round(time.time() - started, 3),
                "output_tail": str(exc)[-1200:],
            }
        results.append(result)
        if result["status"] != "passed":
            break
    return results


def _run_workspace_mcp_preflight(
    profile: dict[str, object], *, workspace: Path
) -> dict[str, object] | None:
    """Initialize profiles' MCP server before a provider can receive a request."""
    if profile.get("lean_lsp_mcp_preflight") is not True:
        return None
    started = time.time()
    session: LeanLspMcpSession | None = None
    try:
        session = LeanLspMcpSession(workspace)
        session.start()
        metadata = session.metadata()
        session.close()
        return {
            "status": "passed",
            "duration_seconds": round(time.time() - started, 3),
            "metadata": metadata,
        }
    except Exception as exc:
        metadata = session.metadata() if session is not None else None
        if session is not None:
            session.close()
        return {
            "status": "failed",
            "duration_seconds": round(time.time() - started, 3),
            "error": str(exc),
            "metadata": metadata,
        }


def _should_validate_host_auth(
    host_auth: object, *, dry_run: bool, setup_failure_class: str | None
) -> bool:
    return isinstance(host_auth, dict) and not dry_run and setup_failure_class is None


def _shell_task_status(
    *,
    verifier_passed: bool,
    harness_status: str,
    exit_code: int,
    editable_changed: bool,
) -> str:
    """Separate gradeable shell output from a CLI/transport crash.

    A non-zero shell invocation may still leave a real candidate behind, so
    modified files remain gradeable. With an untouched placeholder, however,
    timeout/error exits are infrastructure evidence rather than submissions.
    """
    if verifier_passed:
        return "lean_passed"
    if not editable_changed and (harness_status == "timeout" or exit_code == 124):
        return "request_timeout"
    if not editable_changed and (harness_status == "harness_error" or exit_code != 0):
        return "request_failed"
    return "failed_submitted"


def _completed_shell_status(tasks: list[dict[str, object]], raw_status: str) -> str:
    """Report that the benchmark run completed even if the agent CLI exited 1.

    Shell agents commonly use a non-zero exit for a turn limit. Once the
    independent verifier has graded the resulting workspace, that raw process
    status is invocation metadata rather than the run's terminal status.
    """
    if raw_status in {"dry_run", "preflight_failed"}:
        return raw_status
    if tasks and all(task.get("status") == "lean_passed" for task in tasks):
        return "completed"
    return "completed_with_failures"


def _preserve_toolchain_env(env: dict[str, str], original_home: Path) -> None:
    """Keep shared Lean toolchains reachable while isolating agent config."""
    elan_home = original_home / ".elan"
    if "ELAN_HOME" not in env and elan_home.is_dir():
        env["ELAN_HOME"] = str(elan_home)


def _run_setup_process_group(
    command: list[str], *, cwd: Path, timeout_seconds: int
) -> subprocess.CompletedProcess[str]:
    """Run setup in a killable session so Lean descendants cannot escape."""
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        exc.stdout = stdout
        exc.stderr = stderr
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def run_group(
    group_id: str,
    *,
    harness_id: str,
    model: str,
    suite: str = "active",
    keep_workspace: bool = False,
    timeout_seconds: int = 2400,
    token_budget: int = 0,
    max_turns: int = 20,
    task_ref: str | None = None,
    dry_run: bool = False,
) -> tuple[int, Path]:
    profile = load_profile(harness_id)
    op_budget = operational_budget()
    benchmark_budget = {
        "max_attempts": None,
        "max_tool_calls": None,
        "max_turns": max_turns,
        "completion_token_budget": token_budget,
    }
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

    setup_failure_class: str | None = None
    setup_error: str | None = None
    cli_preflights: list[dict[str, object]] = []
    mcp_preflight: dict[str, object] | None = None
    dependency_warm_builds: list[dict[str, object]] = []
    if not dry_run:
        cli_preflights = _run_profile_preflights(profile, cwd=ROOT)
        failed_cli = next((item for item in cli_preflights if item.get("status") != "passed"), None)
        if failed_cli is not None:
            setup_failure_class = "infra_agent_preflight_failed"
            setup_error = f"agent executable preflight failed: {failed_cli.get('output_tail') or failed_cli}"
        else:
            try:
                dependency_warm_builds = warm_public_dependencies(
                    group,
                    timeout_seconds=dependency_warm_timeout_seconds(),
                    log_path=run_dir / "dependency-warm.log",
                )
            except Exception as exc:  # setup must still produce a complete zero-request artifact
                dependency_warm_builds = [
                    {
                        "status": "failed",
                        "exit_code": 1,
                        "error": str(exc),
                        "log_path": str(run_dir / "dependency-warm.log"),
                    }
                ]
            failed_dependency = next(
                (item for item in dependency_warm_builds if warm_result_failed(item)),
                None,
            )
            if failed_dependency is not None:
                setup_failure_class = "infra_dependency_warm_failed"
                setup_error = f"public dependency warm failed: {failed_dependency}"

    built = build_group_workspace(group, run_id=run_id)
    assert_workspace_isolated(built.path)
    initial_editable: dict[str, str] = {}
    for task in group.tasks:
        for rel in task.editable_files:
            path = built.path / rel
            if path.is_file():
                initial_editable[rel] = path.read_text(encoding="utf-8")

    # Let the target check populate target-specific cache entries. The editable
    # theorem is intentionally a placeholder, so a normal non-zero exit is not
    # itself a setup failure; only a timeout is infrastructure-invalid.
    warm: dict[str, object] = {"status": "skipped_dry_run"}
    if not dry_run and setup_failure_class is None:
        warm_started = time.time()
        warm_timeout = int(os.environ.get("DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS", "1800"))
        try:
            completed = _run_setup_process_group(
                ["./harness/check.sh"],
                cwd=built.path,
                timeout_seconds=warm_timeout,
            )
            warm = {
                "status": "passed" if completed.returncode == 0 else "placeholder_failed",
                "exit_code": completed.returncode,
                "duration_seconds": round(time.time() - warm_started, 3),
                "output_tail": (completed.stdout + completed.stderr)[-1200:],
            }
        except subprocess.TimeoutExpired as exc:
            warm = {
                "status": "timeout",
                "exit_code": 124,
                "duration_seconds": round(time.time() - warm_started, 3),
                "output_tail": str(exc)[-1200:],
            }
            setup_failure_class = "infra_target_warm_timeout"
            setup_error = "target cache warm timed out before provider preflight"

    if not dry_run and setup_failure_class is None:
        mcp_preflight = _run_workspace_mcp_preflight(profile, workspace=built.path)
        if mcp_preflight is not None and mcp_preflight.get("status") != "passed":
            setup_failure_class = "infra_agent_preflight_failed"
            setup_error = f"Lean MCP workspace preflight failed: {mcp_preflight.get('error') or mcp_preflight}"

    upstream = os.environ.get("DEFAULT_HARNESS_BASE_URL", "")
    api_key = os.environ.get("DEFAULT_HARNESS_API_KEY")
    uses_proxy = bool(profile.get("uses_proxy", True))
    provider_preflight: dict[str, object] | None = None
    if not dry_run and setup_failure_class is None and uses_proxy:
        try:
            provider_preflight = generic_preflight(upstream, model)
        except Exception as exc:
            provider_preflight = {"status": "failed", "error": str(exc)}
        if provider_preflight.get("status") != "passed":
            setup_failure_class = "provider_setup_error"
            setup_error = f"provider preflight failed: {provider_preflight}"

    proxy: MeteringProxy | None = None
    if not dry_run and setup_failure_class is None and uses_proxy:
        proxy = MeteringProxy(
            upstream,
            api_key,
            usage_path=run_dir / "usage.json",
            completion_token_budget=token_budget,
            user_agent=os.environ.get("DEFAULT_HARNESS_HTTP_USER_AGENT", HARNESS_USER_AGENT),
            text_tool_fallback=bool(profile.get("text_tool_fallback", False)),
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
        "proxy_url": proxy.base_url if proxy is not None else "http://127.0.0.1:0/v1",
        "proxy_key": proxy.local_key if proxy is not None else "not-started",
        "home": str(fake_home),
        "max_turns": str(max_turns),
        "temperature": os.environ.get("DEFAULT_HARNESS_TEMPERATURE", "0.2"),
        "reasoning_effort": os.environ.get("DEFAULT_HARNESS_REASONING_EFFORT", "off"),
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
    if _should_validate_host_auth(
        host_auth, dry_run=dry_run, setup_failure_class=setup_failure_class
    ):
        flag = str(host_auth.get("env_flag") or "")
        source = Path(str(host_auth.get("source") or "")).expanduser()
        fallback_env = str(host_auth.get("fallback_env") or "")
        if flag and os.environ.get(flag) == "1" and source.is_file():
            dest = fake_home / str(host_auth.get("dest") or source.name)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, dest)
            auth_mode = "host-auth"
        elif fallback_env and os.environ.get(fallback_env):
            auth_mode = "env"
        else:
            if proxy is not None:
                proxy.stop()
            shutil.rmtree(fake_home, ignore_errors=True)
            raise RuntimeError(
                f"harness {harness_id} requires host auth: set {flag}=1 with {source} present"
                + (f", or set {fallback_env}" if fallback_env else "")
            )
    command = [_expand(str(part), substitutions) for part in profile["command"]]
    env = os.environ.copy()
    original_home = Path(env.get("HOME") or str(Path.home()))
    env["HOME"] = str(fake_home)
    env["PWD"] = str(built.path)  # some CLIs trust $PWD over getcwd
    env["OLDPWD"] = str(built.path)
    for key in list(env):
        if key.startswith(("DEFAULT_HARNESS_", "OPENAI_", "GAZELLA_", "OPENCODE_")):
            env.pop(key)
    for key, template in (profile.get("env") or {}).items():
        env[str(key)] = _expand(str(template), substitutions)
    _preserve_toolchain_env(env, original_home)

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
    return_code = 0 if dry_run else 1
    harness_status = "dry_run"
    invocations: list[dict[str, object]] = []
    max_invocations = int(os.environ.get("SHELL_AGENT_MAX_INVOCATIONS", "6"))
    continue_template = profile.get("continue_command")
    if not dry_run and setup_failure_class is not None:
        harness_status = (
            "preflight_failed"
            if setup_failure_class == "provider_setup_error"
            else "completed_with_failures"
        )
        stderr = setup_error or setup_failure_class
    elif not dry_run:
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
            if (
                return_code == 124
                or time.time() >= deadline
                or (proxy is not None and proxy.budget_exhausted())
            ):
                break
            # A non-zero exit only ends the loop when there is no configured
            # continue path; otherwise the next iteration re-checks and resumes.
            if return_code != 0 and not isinstance(continue_template, list):
                break
    if proxy is not None:
        proxy.stop()
    shutil.rmtree(fake_home, ignore_errors=True)

    usage = (
        dict(proxy.usage)
        if proxy is not None
        else {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0, "requests": 0}
    )
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
    task_editable_changed: dict[str, bool] = {}
    for task in group.tasks:
        editable_changed = False
        for rel in task.editable_files:
            src = built.path / rel
            after = src.read_text(encoding="utf-8") if src.is_file() else ""
            before = initial_editable.get(rel, "")
            if before != after:
                editable_changed = True
                chunks.extend(
                    difflib.unified_diff(
                        before.splitlines(keepends=True), after.splitlines(keepends=True), fromfile=f"a/{rel}", tofile=f"b/{rel}"
                    )
                )
            if src.is_file():
                dst = submitted_dir / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
        task_editable_changed[task.task_ref] = editable_changed
    (run_dir / "workspace.diff").write_text("".join(chunks), encoding="utf-8")

    verifier_result = (
        setup_failure_verifier_result(
            group,
            built.path,
            failure_class=setup_failure_class,
            artifact_dir=run_dir / "verifier",
        )
        if setup_failure_class is not None
        else verify_group(group, built.path, artifact_dir=run_dir / "verifier")
    )
    response_tasks: list[dict[str, object]]
    if setup_failure_class is not None:
        response_tasks = [
            {
                "task_ref": task.task_ref,
                "status": "request_failed",
                "failure_class": setup_failure_class,
                "error": {
                    "kind": "provider_setup_error"
                    if setup_failure_class == "provider_setup_error"
                    else "transport_error",
                    "message": setup_error or setup_failure_class,
                },
                "attempts": [],
                "benchmark_budget": benchmark_budget,
                "usage": {
                    "prompt_tokens": 0,
                    "completion_tokens": 0,
                    "total_tokens": 0,
                    "requests": 0,
                },
            }
            for task in group.tasks
        ]
    else:
        verifier_targets = {
            str(target.get("task_ref")): target
            for target in verifier_result.get("targets", [])
            if isinstance(target, dict) and target.get("task_ref")
        }
        response_tasks = []
        for task in group.tasks:
            target = verifier_targets.get(task.task_ref, {})
            verifier_passed = target.get("status") == "passed"
            editable_changed = task_editable_changed.get(task.task_ref, False)
            task_status = _shell_task_status(
                verifier_passed=verifier_passed,
                harness_status=harness_status,
                exit_code=return_code,
                editable_changed=editable_changed,
            )
            task_result: dict[str, object] = {
                "task_ref": task.task_ref,
                "status": task_status,
                "attempts": invocations,
                "benchmark_budget": benchmark_budget,
                "usage": usage,
                "verifier_confirmed": verifier_passed,
                "editable_changed": editable_changed,
            }
            if task_status in {"request_failed", "request_timeout"}:
                task_result["failure_class"] = task_status
                task_result["error"] = {
                    "kind": task_status,
                    "harness_status": harness_status,
                    "exit_code": return_code,
                }
            response_tasks.append(task_result)
    classification = classify_run(verifier_result, response_tasks)
    completed_status = _completed_shell_status(response_tasks, harness_status)
    version = None
    version_command = profile.get("version_command")
    if isinstance(version_command, list):
        try:
            probe = subprocess.run([str(part) for part in version_command], capture_output=True, text=True, check=False)
            version = (probe.stdout or probe.stderr).strip().splitlines()[0] if (probe.stdout or probe.stderr).strip() else None
        except OSError:
            version = None
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
        "harness_status": completed_status,
        "agent_exit_status": harness_status,
        "harness_exit_code": return_code,
        "invocations": invocations,
        "timeout_seconds": timeout_seconds,
        "warm_build": warm,
        "dependency_warm_builds": dependency_warm_builds,
        "agent_preflights": cli_preflights,
        "mcp_preflight": mcp_preflight,
        "provider_preflight": provider_preflight,
        "failure_class": setup_failure_class,
        "provider_setup_error": setup_failure_class == "provider_setup_error",
        "auth_mode": auth_mode,
        "usage": usage,
        "usage_source": usage_source,
        "token_budget": token_budget,
        "benchmark_budget": benchmark_budget,
        "operational_budget": {
            "provider_retries": op_budget.provider_retries,
            "infra_restarts": op_budget.infra_restarts,
            "request_timeout_seconds": op_budget.request_timeout_seconds,
            "warm_build_timeout_seconds": op_budget.warm_build_timeout_seconds,
        },
        "workspace": str(built.path) if keep_workspace else None,
        "verifier": verifier_result,
        "classification": classification,
    }
    (run_dir / "harness-response.json").write_text(
        json.dumps(
            {
                "status": completed_status,
                "agent_exit_status": harness_status,
                "command": command,
                "failure_class": setup_failure_class,
                "provider_setup_error": setup_failure_class == "provider_setup_error",
                "dependency_warm_builds": dependency_warm_builds,
                "warm_build": warm,
                "agent_preflights": cli_preflights,
                "mcp_preflight": mcp_preflight,
                "provider_preflight": provider_preflight,
                "tasks": response_tasks,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (run_dir / "harness-request.json").write_text(
        json.dumps(
            {
                "group": agent_group_to_json(group),
                "command": command,
                "model": model,
                "timeout_seconds": timeout_seconds,
                "max_turns": max_turns,
                "auth_mode": auth_mode,
                "dependency_warm_builds": dependency_warm_builds,
                "agent_preflights": cli_preflights,
                "mcp_preflight": mcp_preflight,
                "provider_preflight": provider_preflight,
                "benchmark_budget": run["benchmark_budget"],
                "operational_budget": run["operational_budget"],
            },
            indent=2,
        )
        + "\n",
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
    parser.add_argument("--max-turns", type=int, default=20)
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
        max_turns=args.max_turns,
        task_ref=args.task_ref,
        dry_run=args.dry_run,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
