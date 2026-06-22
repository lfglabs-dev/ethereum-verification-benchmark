# Running the Benchmark

This guide covers local reference checks, harness runs, versioned reruns, and result publication. The public leaderboard is at [lfglabs.dev/benchmark](https://lfglabs.dev/benchmark).

## Suite

Version `0.1` contains 135 active tasks across 25 cases. Every active task has a hidden reference proof and a public task manifest. Case-level `proof_status: partial` means the broader case family is incomplete; it does not mean the active task lacks a reference proof.

The suite is strongest today on accounting, local state preservation, storage effects, linked-list ownership structures, and solvency invariants. Thinner areas include temporal properties, cross-contract composition, governance/timelock reasoning, cryptographic assumptions, oracle manipulation, and adversarial EVM-level behavior. See [evaluated-surface.md](./evaluated-surface.md).

## Reference Proof Checks

```bash
# Single task
./scripts/run_task.sh ethereum/deposit_contract_minimal/deposit_count

# All tasks in one case
./scripts/run_case.sh ethereum/deposit_contract_minimal

# Full active suite
./scripts/run_all.sh
```

## Harness Runs

Two harness families are supported:

- `default`: the built-in fair harness. It exposes Lean-native tools through an OpenAI-compatible loop and logs every tool call and conversation turn.
- shell agent profiles: off-the-shelf coding agents from `harness/agents/*.json`, run in isolated workspaces behind a metering proxy.

All harnesses get the same public files, generated `harness/TASK_SUMMARY.md`, and `./harness/check.sh`. Hidden reference proofs and private build artifacts are removed from the agent workspace. The verifier rebuilds submissions in a private copy and rejects hidden imports, placeholders, added assumptions, and theorem-statement changes.

Configure provider credentials:

```bash
cp .env.example .env
$EDITOR .env
```

Run examples:

```bash
# One default-harness task
python3 -m harness.cli run-task lido/vaulthub_locked/locked_funds_solvency --harness default

# Deeper default-harness attempt
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --budget deep

# Full case
./scripts/run_default_harness_group.sh lido/vaulthub_locked --max-attempts 2

# Full suite
./scripts/run_default_harness_suite.sh --suite active --max-attempts 1

# Shell agent profile
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget deep
```

Budget profiles:

- `quick`: CI-sized smoke budget.
- `normal`: small comparison budget.
- `deep`: long agent budget for real attempts.

Operational metadata is recorded separately from benchmark budget metadata. Run rows include failure classes for provider failures, malformed tool calls, no-tool loops, parse errors, unknown names, unsolved goals, budget exhaustion, and Lean timeouts.

## Versioned Reruns

Benchmark versions live in `benchmark-versions/`. A version manifest records:

- `task_set_id`: ordered task refs.
- `task_fingerprint`: execution-relevant task files and manifest fields.
- `task_interface_id`: public/editable files and fields visible to models.
- `harness_id`: harness code, policies, prompts, runner scripts, and agent configs.
- `environment_id`: Lean/Lake toolchain and runtime dependency pins.

Create or refresh a version manifest:

```bash
python3 scripts/compute_fingerprints.py \
  --version 0.2 \
  --created-at 2026-06-16 \
  --out benchmark-versions/v0.2.json
```

Plan an incremental rerun:

```bash
python3 scripts/plan_rerun.py \
  --from benchmark-versions/v0.1.json \
  --to benchmark-versions/v0.2.json \
  --model minimax/minimax-m3 \
  --results-manifest results/manifests/v0.1.json \
  --json-out results/rerun-plans/minimax-v0.1-to-v0.2.json
```

The planner reruns all tasks when the harness, mode, or budget changes. It reruns changed tasks and rejects reuse of zero-token, missing-verifier, stale-fingerprint, or error-only artifacts.

## Publishing Results

Detailed run directories should be published as release archives instead of committed. The committed result manifest indexes those archives by release tag, asset name, byte size, SHA-256, caveats, and per-task result keys.

Regenerate public result files:

```bash
python3 scripts/aggregate_version.py \
  --version benchmark-versions/v0.1.json \
  --results-manifest results/manifests/v0.1.json \
  --out-dir .
```

This updates:

- `results/summaries/v0.1.json`
- `results/leaderboards/v0.1.json`
- `results.json`
- `leaderboard.md`
- `badges/*.json`

Validate before publishing:

```bash
python3 scripts/validate_manifests.py
python3 scripts/check_run_artifacts.py --self-test
python3 scripts/check.py
```

