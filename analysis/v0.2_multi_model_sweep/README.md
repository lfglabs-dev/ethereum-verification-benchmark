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
| FULL-240 | 240 | All benchmark tasks |
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

Full panel coverage, zero `INFRA_INVALID`. These are the rank-eligible results.

| # | Model | Panel | Profile | Solved | Evaluated | Rate | Avg tokens/task |
|---|---|---|---|---:|---:|---:|---:|
| 1 | **gpt-5.6-sol** | FAST-12 | p4_normal | 6 | 12 | **50.0%** | 28,958 |
| 2 | **gpt-5.6-terra** | FAST-12 | p4_normal | 3 | 12 | **25.0%** | 23,844 |
| 3 | gpt-5.6-luna | FAST-12 | p4_normal | 3 | 12 | 25.0% | 21,450 |
| 4 | minimax/MiniMax-M2.7 | FAST-12 | p1_release | 1 | 12 | 8.3% | 35,650 |
| 5 | minimax/MiniMax-M3 | FULL-240 | p1_release | 16 | 240 | 6.7% | 509,459 |
| 6 | minimax/MiniMax-M3 | FAST-12 | p1_release | 0 | 12 | 0.0% | 31,659 |

Ranks 2 and 3 are tied on solve rate (3/12); `gpt-5.6-terra` is listed first only because it
is also the model with P4-50 coverage. A 12-task panel cannot separate them.

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

Of 424 total runs, 325 produced a valid Lean verdict and 99 were `INFRA_INVALID`.

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

## MiniMax-M3 FULL-240 solved tasks (16/240)

1. damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance
2. damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_sets_sender_credit
3. erc4337/entry_point_invariant/execution_length_eq_validation_length
4. erc4337/entry_point_invariant/no_beneficiary_payout_on_revert
5. ethereum/deposit_contract_minimal/chain_start_threshold
6. forgeyields/global_solvency/report_preserves_global_solvency
7. kleros/sortition_trees/root_equals_sum_of_leaves
8. lido/vaulthub_locked/max_liability_shares_bound
9. lido/vaulthub_locked/reserve_ratio_bounds
10. nexus_mutual/ramm_price_band/sync_sets_book_value
11. nexus_mutual/ramm_price_band/sync_sets_buy_price
12. nexus_mutual/ramm_price_band/sync_sets_sell_price
13. paladin_votes/stream_recovery_claim_usdc/no_overclaim
14. t3tris/hwm_performance_fee/fee_claim_preserves_unclaimed_le_supply
15. usual/dao_collateral/redeem_fee_formula
16. wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity

## Key Findings

1. **Effort budget matters more than the 12-task ranking suggests.** MiniMax-M3 scores 0/12
   on FAST-12 at p1_release (2 attempts / 24 tool calls) but solves 16/240 on the full panel
   at the same profile, and gpt-5.6-sol reaches 50% on FAST-12 at p4_normal (16/120). The
   sweep does not run any single model at both profiles on the same panel, so effort and
   model are confounded — this is a hypothesis the data is consistent with, not a measured
   effect.

2. **The GPT-5.6 family leads among measured models**: sol (6/12) > terra = luna (3/12) on
   FAST-12 at p4_normal, all producing real Lean proofs.

3. **MiniMax-M3 FULL-240 is the only full-benchmark result**: 16/240 = 6.7% with zero
   `INFRA_INVALID`, at 509k tokens/task. For reference, the v0.1 `leaderboard.md` records
   MiniMax-M3 at 38/135 = 28.1% and ~773k tokens/task, on a different task set — v0.1 and
   v0.2 rates are not comparable.

4. **`side_entrance/flash_loan_via_deposit_preserves_pool_balance` and
   `deposit_contract_minimal/chain_start_threshold` are the most-solved tasks**, each cleared
   by 4 of the 6 models that produced verdicts.

5. **Proxy rate-limiting, not model capability, is the binding constraint.** 8 of 14
   attempted models produced zero tokens, and 99 of 424 runs were `INFRA_INVALID`. The
   headline caveat on this sweep is coverage, not scores.

## Caveats

- FAST-12 is 12 tasks. Differences of one or two solves are within noise; treat the ordering
  as indicative, not decisive.
- Profiles are not held constant across models, so the leaderboard mixes effort levels.
  Compare within a profile.
- Only one model (MiniMax-M3) has full-benchmark coverage. All other rates come from a 12-
  or 16-task subset.
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

- `leaderboard.json` — structured leaderboard; each row carries `tasks_evaluated`,
  `infra_invalid`, `genuine_fail` and `solved_tasks`, so partial coverage is recoverable
  from the data.
- `raw_results.json` — per-task raw results (424 rows across 3 panels), one row per
  (model, task) job with its `final_class` and token usage.
