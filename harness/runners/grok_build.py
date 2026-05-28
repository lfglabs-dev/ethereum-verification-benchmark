from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from ..manifests import Group, filter_group_to_task, group_id_from_task_ref, group_to_json, load_group
    from ..reports import write_run_report
    from ..verifier import verify_group
    from ..workspace_builder import agent_group_to_json, assert_workspace_isolated, build_group_workspace
    from ..paths import RESULTS_DIR
except ImportError:
    from manifests import Group, filter_group_to_task, group_id_from_task_ref, group_to_json, load_group
    from reports import write_run_report
    from verifier import verify_group
    from workspace_builder import agent_group_to_json, assert_workspace_isolated, build_group_workspace
    from paths import RESULTS_DIR


HARNESS_ID = "grok-build"
TRACK = "group/shell"


def _auth_mode() -> str:
    if os.environ.get("GROK_CODE_XAI_API_KEY"):
        return "env:GROK_CODE_XAI_API_KEY"
    if os.environ.get("VERITY_ALLOW_HOST_GROK_AUTH") == "1" and (Path.home() / ".grok" / "auth.json").is_file():
        return "explicit-host-grok-auth"
    return "none"


def _prompt(group: Group) -> str:
    return (
        "You are solving a Verity Lean benchmark group.\n"
        "Edit only files listed as editable in harness/TASKS.json.\n"
        "Do not import hidden Proofs modules or Benchmark/GeneratedPreview.\n"
        "Do not add broad `import Benchmark.Grindset`; use existing imports or narrow helper modules only.\n"
        "Run ./harness/check.sh before stopping. Stop when Lean verifies or the turn budget is exhausted.\n\n"
        f"Tasks:\n{json.dumps(agent_group_to_json(group), indent=2)}\n"
    )


def _json_or_raw_stdout(stdout: str) -> str:
    if stdout.strip():
        try:
            return json.dumps(json.loads(stdout), indent=2) + "\n"
        except json.JSONDecodeError:
            pass
    return json.dumps({"raw_stdout": stdout}, indent=2) + "\n"


def run_group(
    group_id: str,
    *,
    suite: str = "active",
    keep_workspace: bool = False,
    max_turns: int = 20,
    dry_run: bool = False,
    task_ref: str | None = None,
) -> tuple[int, Path]:
    start = time.time()
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_subject = task_ref or group_id
    run_mode = "task" if task_ref else "group"
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{HARNESS_ID}-{run_subject.replace('/', '__')}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    group = load_group(group_id, suite)
    if task_ref:
        group = filter_group_to_task(group, task_ref)
    built = build_group_workspace(group, run_id=run_id)
    assert_workspace_isolated(built.path)
    prompt_file = built.path / "harness" / "PROMPT.grok.md"
    prompt_file.write_text(_prompt(group), encoding="utf-8")
    shutil.copy2(built.manifest_path, run_dir / "workspace-manifest.json")
    (run_dir / "harness-request.json").write_text(
        json.dumps(
            {
                "group": group_to_json(group),
                "prompt_file": str(prompt_file),
                "dry_run": dry_run,
                "max_turns": max_turns,
                "auth_mode": _auth_mode(),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    grok = shutil.which("grok")
    command = [
        grok or "grok",
        "--model",
        "grok-build",
        "--cwd",
        str(built.path),
        "--sandbox",
        "strict",
        "--disable-web-search",
        "--no-memory",
        "--no-subagents",
        "--always-approve",
        "--output-format",
        "json",
        "--max-turns",
        str(max_turns),
        "--prompt-file",
        str(prompt_file),
    ]
    stdout = ""
    stderr = ""
    return_code = 0
    harness_status = "dry_run"
    if dry_run:
        harness_response: dict[str, Any] = {"status": "dry_run", "command": command}
    elif not grok:
        return_code = 127
        harness_status = "harness_error"
        harness_response = {"status": harness_status, "error": "grok executable not found", "command": command}
    elif _auth_mode() == "none":
        return_code = 2
        harness_status = "harness_error"
        harness_response = {
            "status": harness_status,
            "error": "grok is installed but no GROK_CODE_XAI_API_KEY or approved per-run auth file is available",
            "command": command,
        }
    else:
        fake_home = Path(tempfile.mkdtemp(prefix="verity-grok-home-"))
        env = os.environ.copy()
        env["HOME"] = str(fake_home)
        if os.environ.get("GROK_CODE_XAI_API_KEY"):
            env["GROK_CODE_XAI_API_KEY"] = os.environ["GROK_CODE_XAI_API_KEY"]
        elif _auth_mode() == "explicit-host-grok-auth":
            auth_dst = fake_home / ".grok" / "auth.json"
            auth_dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(Path.home() / ".grok" / "auth.json", auth_dst)
        try:
            completed = subprocess.run(command, cwd=built.path, capture_output=True, text=True, check=False, env=env, timeout=900)
            stdout = completed.stdout
            stderr = completed.stderr
            return_code = completed.returncode
            harness_status = "completed" if return_code == 0 else "harness_error"
            harness_response = {"status": harness_status, "exit_code": return_code, "command": command}
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode("utf-8", errors="replace")
            if isinstance(stderr, bytes):
                stderr = stderr.decode("utf-8", errors="replace")
            stderr = stderr + "\ngrok process timed out"
            return_code = 124
            harness_status = "timeout"
            harness_response = {"status": harness_status, "exit_code": return_code, "command": command}
        finally:
            shutil.rmtree(fake_home, ignore_errors=True)

    (run_dir / "stdout.txt").write_text(stdout, encoding="utf-8")
    (run_dir / "stderr.txt").write_text(stderr, encoding="utf-8")
    (run_dir / "grok-output.json").write_text(_json_or_raw_stdout(stdout), encoding="utf-8")
    (run_dir / "harness-response.json").write_text(json.dumps(harness_response, indent=2) + "\n", encoding="utf-8")
    submitted_dir = run_dir / "submitted"
    submitted_dir.mkdir(exist_ok=True)
    for task in group.tasks:
        for rel in task.editable_files:
            src = built.path / rel
            if src.is_file():
                dst = submitted_dir / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)

    verifier_result = verify_group(group, built.path, artifact_dir=run_dir / "verifier")
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": HARNESS_ID,
        "model": "grok-build",
        "track": TRACK,
        "run_mode": run_mode,
        "group_id": group_id,
        "task_ref": task_ref,
        "suite": suite,
        "grok_version": _grok_version(grok),
        "sandbox_profile": "grok:strict",
        "auth_mode": _auth_mode(),
        "started_at": started_at,
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": harness_status,
        "harness_exit_code": return_code,
        "workspace": str(built.path) if keep_workspace else None,
        "verifier": verifier_result,
    }
    (run_dir / "run.json").write_text(json.dumps(run, indent=2) + "\n", encoding="utf-8")
    write_run_report(run_dir, run)
    if not keep_workspace:
        shutil.rmtree(built.path, ignore_errors=True)
    return (0 if verifier_result["score"]["passed_targets"] == verifier_result["score"]["total_targets"] and return_code == 0 else 1), run_dir


def _grok_version(grok: str | None) -> str | None:
    if not grok:
        return None
    completed = subprocess.run([grok, "--version"], capture_output=True, text=True, check=False)
    return (completed.stdout or completed.stderr).strip() or None


def main() -> int:
    parser = argparse.ArgumentParser(description="Run Grok Build on a benchmark group")
    parser.add_argument("group_id")
    parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    parser.add_argument("--keep-workspace", action="store_true")
    parser.add_argument("--max-turns", type=int, default=20)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--task-ref")
    args = parser.parse_args()
    group_id = group_id_from_task_ref(args.task_ref) if args.task_ref else args.group_id
    code, run_dir = run_group(
        group_id,
        suite=args.suite,
        keep_workspace=args.keep_workspace,
        max_turns=args.max_turns,
        dry_run=args.dry_run,
        task_ref=args.task_ref,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
