#!/usr/bin/env python3
"""Verify private source identity and optionally compare Cairo results with Lean.

The Cairo runner must compile/execute the real private contract using its pinned
dependencies. This repository cannot supply that adapter without the missing Cairo
project/dependencies. A missing runner is BLOCKED, never a passing differential run.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HASHES = {
    "paraclear/paraclear.cairo": "279c4aa39ae6ecdeacadc63d2003a71639a458821edecceef0b278ef5fed7e2e",
    "token/token.cairo": "bdaee8fd6c63f259683688629ad57e76be3df86da892936183a11256803b9959",
    "paraclear/math.cairo": "8cae4da156a78632c3d339ac0a79606a29a9270eb2355cd948b9bc7c68cbc3a6",
    "account/account.cairo": "5c18e676b354fcb5d069209df3843e9448291146221067dd141f0972c8b2fca0",
}


def verify_source(source: Path) -> None:
    for relative, expected in HASHES.items():
        actual = hashlib.sha256((source / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Source hash mismatch: {relative}")


def compare(fixtures: list[dict], responses: list[dict]) -> None:
    expected = {row["id"]: row["expected"] for row in fixtures}
    if not expected or len(expected) != len(fixtures):
        raise ValueError("Empty or duplicate fixture IDs")
    seen = set()
    for row in responses:
        identifier = row["id"]
        if identifier in seen or identifier not in expected:
            raise ValueError(f"Duplicate or unknown response ID: {identifier}")
        seen.add(identifier)
        result = row["result"]
        if type(result.get("success")) is not bool:
            raise ValueError(f"Non-Boolean success: {identifier}")
        if result != expected[identifier] or any(
            type(result.get(key)) is not type(value)
            for key, value in expected[identifier].items()
        ):
            raise ValueError(f"Cairo/Lean mismatch: {identifier}: {result} != {expected[identifier]}")
    if seen != set(expected):
        raise ValueError(f"Missing Cairo results: {sorted(set(expected) - seen)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--cairo-runner", type=Path, help="Executable JSONL integration adapter")
    args = parser.parse_args()
    try:
        source = args.source_root.resolve()
        verify_source(source)
        print("Verified four private Cairo source hashes.")
        if args.source_only:
            print("Source identity only; Cairo differential execution NOT RUN.")
            return 0
        if args.cairo_runner is None:
            print("BLOCKED: supply --cairo-runner backed by the complete, pinned Cairo project.")
            return 2
        oracle = subprocess.run(
            ["lake", "env", "lean", "--run",
             "Benchmark/Cases/Paraclear/DirectDepositBacking/Differential.lean"],
            cwd=ROOT, check=True, capture_output=True, text=True, timeout=600,
        )
        fixtures = [json.loads(line) for line in oracle.stdout.splitlines() if line.strip()]
        requests = "".join(json.dumps({"id": row["id"], "input": row["input"]}) + "\n"
                           for row in fixtures)
        cairo = subprocess.run(
            [str(args.cairo_runner.resolve()), "--source-root", str(source)],
            input=requests, check=True, capture_output=True, text=True, timeout=600,
        )
        responses = [json.loads(line) for line in cairo.stdout.splitlines() if line.strip()]
        compare(fixtures, responses)
        print(f"Cairo/Lean differential comparison passed: {len(fixtures)} cases.")
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"FAILED: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
