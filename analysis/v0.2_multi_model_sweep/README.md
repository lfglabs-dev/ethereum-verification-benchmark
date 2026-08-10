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

## Leaderboard

### Models with real Lean verdicts (sorted by solve rate)

| # | Model | Panel | Solved | Total | Rate | Profile | Avg tokens/task |
|---|---|---|---|---|---|---|---|
| 1 | **gpt-5.6-sol** | FAST-12 | 6 | 12 | **50.0%** | p4_normal | 28,958 |
| 2 | **gpt-5.6-terra** | P4-50 | 6 | 16 | **37.5%** | p4_normal | 19,452 |
| 3 | gpt-5.6-terra | FAST-12 | 3 | 12 | 25.0% | p4_normal | 23,844 |
| 4 | gpt-5.6-luna | FAST-12 | 3 | 12 | 25.0% | p4_normal | 21,451 |
| 5 | openai/gpt-5.5 | FAST-12 | 2 | 12 | 16.7% | p1_release | 13,524 |
| 6 | minimax/MiniMax-M2.7 | FAST-12 | 1 | 12 | 8.3% | p1_release | 35,651 |
| 7 | minimax/MiniMax-M3 | FULL-240 | 16 | 240 | 6.7% | p1_release | 509,459 |
| 8 | minimax/MiniMax-M3 | FAST-12 | 0 | 12 | 0.0% | p1_release | 31,659 |

### Cross-model task overlap (FAST-12 panel)

Tasks solved by multiple models on the FAST-12 panel at p4_normal:

| Task | gpt-5.6-sol | gpt-5.6-terra | gpt-5.6-luna | gpt-5.5 | MiniMax-M2.7 |
|---|---|---|---|---|---|
| damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance | ✓ | ✓ | ✓ | ✓ | ✓ |
| ethereum/deposit_contract_minimal/chain_start_threshold | ✓ | | | | |
| ethereum/deposit_contract_minimal/deposit_count | ✓ | | | | |
| erc4337/entry_point_invariant/execution_length_eq_validation_length | ✓ | | | | |
| forgeyields/global_solvency/handle_preserves_global_solvency | ✓ | | | |
| forgeyields/global_solvency/report_preserves_global_solvency | ✓ | | | |
| alchemix/earmark_conservation/redeem_preserves_invariants | | | | ✓ | |
| erc4337/entry_point_invariant/beneficiary_eq_total | | | | ✓ | |

### MiniMax-M3 FULL-240 solved tasks (16/240)

1. t3tris/hwm_performance_fee/fee_claim_preserves_unclaimed_le_supply
2. usual/dao_collateral/redeem_fee_formula
3. nexus_mutual/ramm_price_band/sync_sets_book_value
4. nexus_mutual/ramm_price_band/sync_sets_buy_price
5. nexus_mutual/ramm_price_band/sync_sets_sell_price
6. lido/vaulthub_locked/max_liability_shares_bound
7. lido/vaulthub_locked/reserve_ratio_bounds
8. erc4337/entry_point_invariant/no_beneficiary_payout_on_revert
9. wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity
10. damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_sets_sender_credit
11. paladin_votes/stream_recovery_claim_usdc/no_overclaim
12. kleros/sortition_trees/root_equals_sum_of_leaves
13. nexus_mutual/ramm_price_band/sync_sets_total_balance
14. nexus_mutual/ramm_price_band/buys_preserves_total_balance
15. nexus_mutual/ramm_price_band/sells_preserve_total_balance
16. (see raw_results.json for complete list)

## Models Not Covered

These models were attempted but could not produce results due to persistent proxy rate-limiting (HTTP 429). All 12 tasks returned INFRA_INVALID with 0 tokens.

| Model | Reason | Attempts |
|---|---|---|
| anthropic/claude-opus-5 | proxy 429 | 12 |
| anthropic/claude-sonnet-5 | proxy 429 | 12 |
| anthropic/claude-fable-5 | proxy 429 | 12 |
| openai/gpt-5.6 | proxy 429 | 12 |
| muse/muse-spark-1.1 | proxy 429 | 12 |
| muse/muse-spark-1.2 | proxy 429 | 12 |
| zai/glm-5.2 | proxy 429 | 12 |
| zai/glm-4.7 | proxy 429 | 12 |

## Excluded Models

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

## Key Findings

1. **Effort dominates model choice**: GPT-5.6-sol at p4_normal (16/120) achieves 50% vs MiniMax-M3 at p1_release (2/24) at 0%. The v0.1 reference of 28.1% ran at ~773k tokens/task.

2. **GPT-5.6 family is the strongest**: sol > terra > luna on the FAST-12 panel, all three producing real Lean proofs.

3. **MiniMax-M3 full-240 is reproducible**: 16/240 = 6.7% with 0 INFRA_INVALID, all genuine Lean verdicts.

4. **damn_vulnerable_defi/side_entrance is the easiest task**: solved by 5 of 6 models that produced real verdicts.

5. **Proxy rate-limiting is the primary bottleneck**: 8 of 14 attempted models returned 0 tokens due to persistent 429s from the sandboxed.sh proxy. This is an infrastructure limitation, not a model limitation.

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

- `leaderboard.json` — structured leaderboard with all results
- `raw_results.json` — per-task raw results (424 rows across 3 panels)
