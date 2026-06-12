#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
source scripts/load_env.sh

python3 -m py_compile harness/*.py harness/runners/*.py scripts/check_group_workspaces.py scripts/check_verifier_policy.py scripts/check_run_artifacts.py scripts/check_fair_harness_policy.py
python3 -m json.tool harness/agents/default.json >/dev/null
python3 -m json.tool harness/agents/grok-build.json >/dev/null
python3 -m harness.cli list --suite active --unit group >/dev/null
python3 scripts/check_fair_harness_policy.py
python3

if python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --dry-run >/tmp/verity-default-run-task-smoke.out; then
  echo "expected default run-task dry-run to fail verification on placeholder proof" >&2
  exit 1
fi
python3 scripts/check_run_artifacts.py "$(tail -1 /tmp/verity-default-run-task-smoke.out)"

if python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --dry-run >/tmp/verity-grok-run-task-smoke.out; then
  echo "expected grok-build run-task dry-run to fail verification on placeholder proof" >&2
  exit 1
fi
python3 scripts/check_run_artifacts.py "$(tail -1 /tmp/verity-grok-run-task-smoke.out)"

python3 scripts/check_group_workspaces.py --suite active
python3 scripts/check_verifier_policy.py
python3 -m harness.sandbox_runner smoke --executor local >/dev/null
if command -v podman >/dev/null 2>&1; then
  if ! python3 -m harness.sandbox_runner smoke --executor podman >/dev/null; then
    if [[ "${VERITY_REQUIRE_PODMAN_SMOKE:-0}" == "1" ]]; then
      echo "podman sandbox smoke failed" >&2
      exit 1
    fi
    echo "podman sandbox smoke failed; set VERITY_REQUIRE_PODMAN_SMOKE=1 to make this fatal" >&2
  fi
fi

python3 scripts/check_reference_solutions.py
python3 scripts/check_axiom_ledger.py
python3 scripts/check_verity_pin_staleness.py --warn-only
python3 scripts/validate_manifests.py
python3 scripts/generate_metadata.py
if [[ "${VERITY_RUN_FULL_TASK_SWEEP:-0}" == "1" ]]; then
  if ! ./scripts/run_all.sh; then
    echo "run_all completed with failing benchmark outcomes; artifact generation was still exercised" >&2
  fi
fi
