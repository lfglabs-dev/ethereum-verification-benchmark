#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
source scripts/load_env.sh

python3 -m py_compile harness/*.py harness/runners/*.py scripts/aggregate_runs.py scripts/check_group_workspaces.py scripts/check_verifier_policy.py scripts/check_run_artifacts.py scripts/check_fair_harness_policy.py scripts/check_publication_safe_classification.py scripts/replay_publication_safe_classification.py scripts/classify_failures.py scripts/extract_task_features.py scripts/cluster_task_failures.py scripts/generate_stratified_panel.py scripts/check_v03_strat50.py scripts/run_strat50.py
python3 -m json.tool harness/agents/default.json >/dev/null
python3 -m harness.cli list --suite active --unit group >/dev/null
python3 scripts/check_fair_harness_policy.py
python3 scripts/check_run_artifacts.py --self-test
python3 scripts/check_v03_strat50.py
python3 -m unittest discover -s tests
python3 scripts/check_publication_safe_classification.py

if python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --dry-run >/tmp/verity-default-run-task-smoke.out; then
  echo "expected default run-task dry-run to fail verification on placeholder proof" >&2
  exit 1
fi
python3 scripts/check_run_artifacts.py "$(tail -1 /tmp/verity-default-run-task-smoke.out)"

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
v02_audit="$(mktemp -t verity-v02-reference-validation.XXXXXX.json)"
trap 'rm -f "$v02_audit"' EXIT
python3 scripts/run_in_v02_environment.py -- \
  python3 scripts/validate_v02_reference_contract.py --audit "$v02_audit"
python3 scripts/generate_metadata.py
if [[ "${VERITY_RUN_FULL_TASK_SWEEP:-0}" == "1" ]]; then
  if ! ./scripts/run_all.sh; then
    echo "run_all completed with failing benchmark outcomes; artifact generation was still exercised" >&2
  fi
fi
