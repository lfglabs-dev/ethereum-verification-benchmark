# v0.2 Multi-Model Benchmark Sweep — Final Results

## Benchmark Configuration

| Parameter | Value |
|---|---|
| Release | v0.2 (immutable) |
| HEAD | `c5a2344b121040445ccd745a3f839548ca8f9158` |
| Lean | 4.24.0 |
| Harness | `sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867` |
| Total tasks | 240 |

## Panels

| Panel | Tasks | Selection |
|---|---|---|
| FULL-240 | 240 | All benchmark tasks (defined in `panels.json`; no verified result row is published) |
| P4-50 | 50 | Stratified, seed=42 |
| FAST-12 | 12 | First 12 tasks of P4-50 |

## Effort Profiles

| Profile | Max attempts | Max tool calls |
|---|---|---|
| p1_release | 2 | 24 |
| p4_normal | 16 | 120 |

## Methodology

Each (model, task) job runs the `default` harness at a fixed effort profile against the
pinned v0.2 release commit. A task counts as **solved** only when every classification
target in the run reports `final_class = SOLVED` — i.e. a Lean proof that compiles against
the task's specification. There is no partial credit.

Every run lands in exactly one of three outcome classes:

| Class | Meaning | Counted in solve rate? |
|---|---|---|
| `SOLVED` | All targets verified by Lean | Yes (numerator + denominator) |
| `GENUINE_FAIL` | Model produced output, Lean rejected it or budget ran out | Yes (denominator) |
| `INFRA_INVALID` | No usable verdict — provider/proxy error, no model output | **No** — excluded from both |

`INFRA_INVALID` runs are not model failures and are never scored as such. Solve rates below
are therefore computed over **valid verdicts** (`SOLVED + GENUINE_FAIL`), not over runs
attempted. Rows whose panel coverage is incomplete — because tasks were not all run, or
because some runs returned `INFRA_INVALID` — are reported separately as **partial** and are
excluded from rank comparison, following the convention already used by the v0.1
`leaderboard.md`.

Token counts are total tokens (prompt + completion) reported by the provider, summed across
all attempts for a task. Because effort profiles differ by up to 8x in attempt budget,
tokens/task is only comparable **within** a profile, not across profiles.

## Leaderboard

### Complete rows

Full coverage and zero `INFRA_INVALID`. Rows are comparable only within the same panel and
profile, so this publication intentionally assigns no cross-panel or cross-profile ordinal.

| Model | Panel | Profile | Solved | Evaluated | Rate | Avg tokens/task |
|---|---|---|---:|---:|---:|---:|
| gpt-5.6-sol | FAST-12 | p4_normal | 6 | 12 | 50.0% | 28,958 |
| gpt-5.6-terra | FAST-12 | p4_normal | 3 | 12 | 25.0% | 23,844 |
| gpt-5.6-luna | FAST-12 | p4_normal | 3 | 12 | 25.0% | 21,450 |
| minimax/MiniMax-M2.7 | FAST-12 | p1_release | 1 | 12 | 8.3% | 35,650 |
| minimax/MiniMax-M3 | FAST-12 | p1_release | 0 | 12 | 0.0% | 31,659 |

### Partial rows — shown for transparency, excluded from ranking

| Model | Panel | Profile | Solved | Valid verdicts | Panel size | Rate (valid) | Avg tokens/valid task | Why partial |
|---|---|---|---:|---:|---:|---:|---:|---|
| gpt-5.6-terra | P4-50 | p4_normal | 6 | 16 | 50 | 37.5% | 19,452 | panel incomplete — only 16/50 tasks run |
| openai/gpt-5.5 | FAST-12 | p1_release | 2 | 9 | 12 | 22.2% | 18,032 | 3/12 runs `INFRA_INVALID` (proxy 429) |

`gpt-5.6-terra` P4-50 is a **truncated run**: the sweep was interrupted after 16 of 50 tasks.
Its 37.5% is measured on the first 16 tasks of the stratified panel only and must not be
compared against full-panel rates.

`openai/gpt-5.5` lost its first 3 FAST-12 tasks to proxy 429s. Its 2 solves are over the 9
tasks that returned a real verdict. Scored over all 12 attempted runs it would read 16.7%,
which would understate it by charging infrastructure failures against the model.

### Not covered — no usable data

Every run returned `INFRA_INVALID` with 0 tokens: the request never reached the model, due
to persistent HTTP 429 rate-limiting from the sandboxed.sh proxy. **These are not zero
scores and must not be read as such** — these models were not measured.

| Model | Panel | Profile | Runs attempted | INFRA_INVALID | Tokens |
|---|---|---|---:|---:|---:|
| anthropic/claude-fable-5 | FAST-12 | p1_release | 12 | 12 | 0 |
| anthropic/claude-opus-5 | FAST-12 | p1_release | 12 | 12 | 0 |
| anthropic/claude-sonnet-5 | FAST-12 | p1_release | 12 | 12 | 0 |
| muse/muse-spark-1.1 | FAST-12 | p1_release | 12 | 12 | 0 |
| muse/muse-spark-1.2 | FAST-12 | p4_normal | 12 | 12 | 0 |
| openai/gpt-5.6 | FAST-12 | p1_release | 12 | 12 | 0 |
| zai/glm-4.7 | FAST-12 | p1_release | 12 | 12 | 0 |
| zai/glm-5.2 | FAST-12 | p1_release | 12 | 12 | 0 |

A follow-up catch-up sweep on 2026-08-10 re-attempted this set at p1_release.
`anthropic/claude-opus-5` and `anthropic/claude-fable-5` again returned 12/12
`INFRA_INVALID` at 0 tokens, confirming the block is environmental and not
model-specific. That sweep is not included in `raw_results.json`.

### Never attempted

| Model | Reason |
|---|---|
| spark/qwen3.6-aeon-dflash | DGX Spark paused (operator directive) |
| spark/leanstral-2603 | DGX Spark paused (operator directive) |
| cerebras/zai-glm-4.7 | Provider auth error |
| google/gemini-3-pro-preview | Provider auth error |
| google/gemini-2.5-pro | Provider auth error |
| google/gemini-3.5-flash | Provider auth error |
| xai/grok-4.5-latest | Provider unavailable |
| xai/grok-build-latest | Provider unavailable |
| openai/gpt-5.5-pro | Provider unavailable |
| openai/gpt-5.4-pro | Provider unavailable |
| openai/gpt-5.3-codex | Provider unavailable |

## Coverage Summary

| | Models |
|---|---:|
| Attempted | 14 |
| Produced at least one valid verdict | 6 |
| Full panel coverage (rank-eligible) | 5 |
| No usable data (proxy 429) | 8 |

Of 184 published runs, 85 produced a valid Lean verdict and 99 were `INFRA_INVALID`.

## Cross-model task overlap (FAST-12)

Six of the twelve FAST-12 tasks were solved by at least one model. Blank = attempted and
failed.

| Task | gpt-5.6-sol | gpt-5.6-terra | gpt-5.6-luna | gpt-5.5 | MiniMax-M2.7 | MiniMax-M3 |
|---|---|---|---|---|---|---|
| damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance | yes | yes | yes | | yes | |
| erc4337/entry_point_invariant/beneficiary_eq_total_prefund | yes | yes | | | | |
| erc4337/entry_point_invariant/execution_length_eq_validation_length | yes | | | | | |
| ethereum/deposit_contract_minimal/chain_start_threshold | yes | yes | yes | yes | | |
| ethereum/deposit_contract_minimal/deposit_count | yes | | yes | yes | | |
| forgeyields/global_solvency/handle_preserves_global_solvency | yes | | | | | |

The remaining six FAST-12 tasks (`1inch/xycswap_curve_safety`, both
`alchemix/earmark_conservation` tasks, `balancer/reclamm_swap_rounding`,
`cork/pool_solvency`, `damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool`) were
solved by **no** model. Note that `gpt-5.5`'s three `INFRA_INVALID` runs cover
`1inch/xycswap_curve_safety` and both `alchemix` tasks, so it has no verdict on those.

## Key Findings

1. **The GPT-5.6 family leads among the measured p4_normal FAST-12 models**: sol (6/12) > terra = luna (3/12),
   all producing real Lean proofs.

2. **`side_entrance/flash_loan_via_deposit_preserves_pool_balance` and
   `deposit_contract_minimal/chain_start_threshold` are the most-solved tasks**, each cleared
   by 4 of the 6 models that produced verdicts.

3. **Proxy rate-limiting, not model capability, is the binding constraint.** 8 of 14
   attempted models produced zero tokens, and 99 of 184 runs were `INFRA_INVALID`. The
   headline caveat on this sweep is coverage, not scores.

## Caveats

- FAST-12 is 12 tasks. Differences of one or two solves are within noise; treat the ordering
  as indicative, not decisive.
- Profiles are not held constant across models, so the leaderboard mixes effort levels.
  Compare within a profile.
- No FULL-240 result is published: nine retained MiniMax-M3 raw rows conflict with their
  archived artifacts, so that cohort is withheld rather than reconstructed by assumption.
- Solve rates exclude `INFRA_INVALID` runs, so a model's denominator may be smaller than the
  panel size. The partial table states this explicitly per row.

## Reproduction

```bash
# Checkout the immutable v0.2 release
git clone https://github.com/lfglabs-dev/ethereum-verification-benchmark.git
cd ethereum-verification-benchmark
git checkout c5a2344b121040445ccd745a3f839548ca8f9158

# Run a single task with a specific model
DEFAULT_HARNESS_MODEL=gpt-5.6-sol \
DEFAULT_HARNESS_MAX_RESPONSE_TOKENS=32768 \
python -m harness.cli run-task <task_ref> \
  --harness default \
  --max-attempts 16 \
  --max-tool-calls 120 \
  --suite all
```

## Files

- `leaderboard.json` — structured leaderboard; each row carries `runs_attempted`,
  `valid_verdicts`, `infra_invalid`, `genuine_fail` and `solved_tasks`, so partial coverage
  is recoverable from the data.
- `raw_results.json` — per-task raw results (184 rows across FAST-12 and P4-50), one row per
  (model, task) job with its `final_class` and token usage.
- `panels.json` — ordered membership for all three declared panels.
- `v0.2-manifest.json` — immutable 240-task benchmark manifest for the pinned release.
- `run-artifact-index.json` and `artifacts/run-archive.tar.gz` — SHA-256-indexed run
  artifacts, including `run.json`, verifier output, submitted attempts and logs.
