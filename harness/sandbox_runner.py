from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

try:
    from .manifests import load_group
    from .workspace_builder import assert_workspace_isolated, build_group_workspace
except ImportError:
    from manifests import load_group
    from workspace_builder import assert_workspace_isolated, build_group_workspace


def podman_available() -> bool:
    return shutil.which("podman") is not None


def smoke(executor: str) -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="verity-smoke-") as tmp_dir:
        group = load_group("ethereum/deposit_contract_minimal")
        workspace = build_group_workspace(group, workspace_dir=Path(tmp_dir))
        assert_workspace_isolated(workspace.path)
        result: dict[str, object] = {
            "executor": executor,
            "workspace": str(workspace.path),
            "workspace_isolated": True,
        }
        if executor == "podman":
            policy = {
                "rootless_expected": True,
                "network": "none",
                "capabilities": "drop-all",
                "no_new_privileges": True,
                "read_only_container": True,
                "workspace_mount": "rw",
                "pids_limit": 256,
                "memory": "2g",
                "cpus": "2",
                "image": "docker.io/library/alpine:latest",
                "pull": "never",
            }
            result["policy"] = policy
            if not podman_available():
                result.update({"status": "skipped", "reason": "podman not installed"})
                return result
            command = [
                "podman",
                "run",
                "--rm",
                "--pull=never",
                "--userns=keep-id",
                "--network=none",
                "--cap-drop=all",
                "--security-opt=no-new-privileges",
                "--read-only",
                "--pids-limit=256",
                "--memory=2g",
                "--cpus=2",
                "--tmpfs",
                "/tmp:rw,nosuid,nodev,noexec,size=256m",
                "-v",
                f"{workspace.path}:/workspace:rw",
                "-w",
                "/workspace",
                policy["image"],
                "sh",
                "-lc",
                "test -f harness/TASKS.json && test ! -e Benchmark/GeneratedPreview && test ! -e .env",
            ]
            completed = subprocess.run(command, capture_output=True, text=True, check=False)
            result.update(
                {
                    "status": "passed" if completed.returncode == 0 else "failed",
                    "command": command,
                    "stdout": completed.stdout,
                    "stderr": completed.stderr,
                }
            )
            return result
        result.update({"status": "passed"})
        return result


def main() -> int:
    parser = argparse.ArgumentParser(description="Benchmark sandbox smoke runner")
    sub = parser.add_subparsers(dest="command", required=True)
    smoke_parser = sub.add_parser("smoke")
    smoke_parser.add_argument("--executor", choices=["local", "podman"], default="local")
    args = parser.parse_args()
    payload = smoke(args.executor)
    print(json.dumps(payload, indent=2))
    return 0 if payload.get("status") in {"passed", "skipped"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
