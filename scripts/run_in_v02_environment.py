#!/usr/bin/env python3
"""Run a command from an isolated checkout using the frozen v0.2 environment."""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from harness.v02_release import RELEASE_CHECKOUT_COMMIT

REENTRY_ENV = "VERITY_V02_PINNED_CHECKOUT"


def _git(*args: str, cwd: Path = ROOT, capture_output: bool = False) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args], cwd=cwd, check=False, capture_output=capture_output, text=False
    )


def _require_commit() -> None:
    if _git("cat-file", "-e", f"{RELEASE_CHECKOUT_COMMIT}^{{commit}}").returncode == 0:
        return
    fetched = _git("fetch", "origin", RELEASE_CHECKOUT_COMMIT)
    if fetched.returncode or _git("cat-file", "-e", f"{RELEASE_CHECKOUT_COMMIT}^{{commit}}").returncode:
        raise RuntimeError(f"frozen v0.2 checkout unavailable: {RELEASE_CHECKOUT_COMMIT}")


def run(command: list[str]) -> int:
    if not command:
        raise ValueError("a command is required")
    _require_commit()
    with tempfile.TemporaryDirectory(prefix="verity-v02-environment-") as directory:
        checkout = Path(directory) / "source"
        added = _git(
            "worktree", "add", "--detach", str(checkout), RELEASE_CHECKOUT_COMMIT,
            capture_output=True,
        )
        if added.returncode:
            raise RuntimeError("could not create frozen v0.2 execution checkout")
        try:
            # Run artifacts belong to the invoking checkout, not the disposable
            # frozen checkout. The tracked empty results directory is replaced.
            checkout_results = checkout / "results"
            if checkout_results.exists():
                checkout_results.rename(checkout / "results.frozen")
            (ROOT / "results").mkdir(exist_ok=True)
            checkout_results.symlink_to(ROOT / "results", target_is_directory=True)

            env = os.environ.copy()
            env[REENTRY_ENV] = "1"
            env.pop("ELAN_TOOLCHAIN", None)
            return subprocess.run(command, cwd=checkout, env=env, check=False).returncode
        finally:
            _git("worktree", "remove", "--force", str(checkout), capture_output=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    return run(command)


if __name__ == "__main__":
    raise SystemExit(main())
