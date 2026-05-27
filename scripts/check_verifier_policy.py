#!/usr/bin/env python3
from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.manifests import filter_group_to_task, load_group
from harness.verifier import verify_group
from harness.workspace_builder import build_group_workspace

TASK_REF = "ethereum/deposit_contract_minimal/deposit_count"
EDITABLE = "Benchmark/Generated/Ethereum/DepositContractMinimal/Tasks/DepositCount.lean"


def run_case(name: str, transform) -> tuple[str, str]:
    temp_dir = Path(tempfile.mkdtemp(prefix=f"verity-policy-{name}-"))
    try:
        group = filter_group_to_task(load_group("ethereum/deposit_contract_minimal"), TASK_REF)
        build_group_workspace(group, workspace_dir=temp_dir, run_id=f"policy-{name}")
        proof_path = temp_dir / EDITABLE
        proof_path.write_text(transform(proof_path.read_text(encoding="utf-8")), encoding="utf-8")
        result = verify_group(group, temp_dir)
        return name, result["targets"][0]["status"]
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def main() -> int:
    cases = {
        "placeholder": lambda text: text,
        "hidden_import": lambda text: text.replace(
            "import Benchmark.Cases.Ethereum.DepositContractMinimal.Specs",
            "import Benchmark.Cases.Ethereum.DepositContractMinimal.Proofs",
        ),
        "statement_mismatch": lambda text: text.replace(
            "(hMin : depositAmount >= 1000000000)",
            "(hMin : depositAmount >= 1000000001)",
        ),
    }
    expected = {
        "placeholder": "forbidden_placeholder",
        "hidden_import": "hidden_import",
        "statement_mismatch": "theorem_statement_mismatch",
    }
    failures = []
    for name, transform in cases.items():
        _, status = run_case(name, transform)
        if status != expected[name]:
            failures.append(f"{name}: expected {expected[name]}, got {status}")
    if failures:
        print("\n".join(failures))
        return 1
    print(f"verifier policy checks passed for {len(cases)} cases")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
