#!/usr/bin/env python3
"""Single entry point for the repo's check suite.

Usage:
  python3 scripts/check.py --list
  python3 scripts/check.py fast           # lake-free checks (CI harness-check set)
  python3 scripts/check.py all            # everything, including Lean-workspace checks
  python3 scripts/check.py grindset reference ...   # named subset

Each check is a standalone script under scripts/; this runner just sequences
them and aggregates exit codes.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# name -> (command, needs_lean_toolchain)
CHECKS: dict[str, tuple[list[str], bool]] = {
    "grindset": (["python3", "scripts/check_grindset_generic.py"], False),
    "reference": (["python3", "scripts/check_reference_solutions.py"], False),
    "artifacts": (["python3", "scripts/check_run_artifacts.py", "--self-test"], False),
    "axioms": (["python3", "scripts/check_axiom_ledger.py"], False),
    # advisory / environment-sensitive (not in 'fast'): tomllib needs py>=3.11,
    # pin staleness fails by design when the Verity pin ages
    "manifests": (["python3", "scripts/validate_manifests.py"], True),
    "pin": (["python3", "scripts/check_verity_pin_staleness.py"], True),
    "fair-policy": (["python3", "scripts/check_fair_harness_policy.py"], True),
    "verifier-policy": (["python3", "scripts/check_verifier_policy.py"], True),
    "workspaces": (["python3", "scripts/check_group_workspaces.py", "ethereum/deposit_contract_minimal"], True),
}
FAST = [name for name, (_, lean) in CHECKS.items() if not lean]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("names", nargs="*", help="check names, or 'fast' / 'all'")
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    if args.list or not args.names:
        for name, (command, lean) in CHECKS.items():
            print(f"{name:16} {'(lean)' if lean else '':6} {' '.join(command)}")
        return 0
    if args.names == ["fast"]:
        selected = FAST
    elif args.names == ["all"]:
        selected = list(CHECKS)
    else:
        unknown = [name for name in args.names if name not in CHECKS]
        if unknown:
            parser.error(f"unknown checks: {', '.join(unknown)} (see --list)")
        selected = args.names
    failed: list[str] = []
    for name in selected:
        command, _ = CHECKS[name]
        print(f"== {name}", flush=True)
        if subprocess.run(command, cwd=ROOT).returncode != 0:
            failed.append(name)
    if failed:
        print(f"FAILED: {', '.join(failed)}")
        return 1
    print(f"all {len(selected)} checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
