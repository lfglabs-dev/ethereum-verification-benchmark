# Verity Benchmark Leaderboard

Generated 2026-06-14 07:48Z · commit `a85f0cf61` · budget `normal`

**Ranked by total cost (cheapest first).** All combos run the same task set;
pass/fail is decided by the independent verifier; tokens are counted across the
whole agent loop (builtin: in-loop accounting; shell harnesses: metered at the API
boundary by the harness proxy).

| Harness | Model | Pass | Median completion tok / pass | Median prompt tok / pass | Median cost / pass | Total completion tok | Total prompt tok | Total cost |
|---|---|---|---|---|---|---|---|---|
| builtin (fair) | builtin/smart | 5/5 | 6.9k | 768.9k | $0.24 | 42.9k | 4.8M | $1.49 |
| opencode | builtin/smart | 3/5 | 10.5k | 1.9M | $0.59 | 113.7k | 10.8M | $3.38 |
| opencode | builtin/fast | 5/5 | 7.5k | 301.0k | $0.39 | 134.0k | 4.0M | $5.29 |
| builtin (fair) | grok | 4/5 | 2.1k | 476.2k | $0.48 | 32.1k | 5.8M | $5.84 |
| builtin (fair) | builtin/fast | 5/5 | 12.4k | 1.2M | $1.52 | 56.9k | 6.0M | $7.39 |
| builtin (fair) | gpt55 | 5/5 | 1.3k | 240.7k | $1.23 | 14.9k | 1.6M | $8.42 |
| codex | gpt-5.5 | 5/5 | — | — | — | — | — | — |
| grok-build | grok-build | 4/5 | — | — | — | — | — | — |
| builtin (fair) | zai/glm-5.2 | 53/135 | 2.6k | 105.7k | — | 1.3M | 61.7M | — |
| builtin (fair) | minimax/minimax-m3 | 38/135 | 2.3k | 156.7k | — | 1.5M | 102.9M | — |
| builtin (fair) | Step37 | 1/135 | — | — | — | — | — | — |

## Per-task completion tokens

Cell = ✅/❌ with completion tokens spent on that task (including failed attempts).

| Task | codex<br>gpt-5.5 | builtin (fair)<br>builtin/fast | builtin (fair)<br>builtin/smart | builtin (fair)<br>gpt55 | builtin (fair)<br>grok | builtin (fair)<br>minimax/minimax-m3 | builtin (fair)<br>Step37 | builtin (fair)<br>zai/glm-5.2 | grok-build<br>grok-build | opencode<br>builtin/fast | opencode<br>builtin/smart |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `alchemix/earmark_conservation/earmark_preserves_invariant` | · | · | · | · | · | ❌ 7.3k | ❌ — | ❌ 14.6k | · | · | · |
| `alchemix/earmark_conservation/redeem_preserves_invariant` | · | · | · | · | · | ❌ 11.7k | ❌ — | ❌ 12.6k | · | · | · |
| `alchemix/earmark_conservation/sub_debt_preserves_invariant` | · | · | · | · | · | ❌ 15.8k | ❌ — | ❌ 12.8k | · | · | · |
| `alchemix/earmark_conservation/sub_earmarked_debt_preserves_invariant` | · | · | · | · | · | ❌ 7.0k | ❌ — | ❌ 8.6k | · | · | · |
| `alchemix/earmark_conservation/sync_account_preserves_invariant` | · | · | · | · | · | ❌ 10.3k | ❌ — | ❌ 8.8k | · | · | · |
| `balancer/reclamm_swap_rounding/on_swap_fixed_virtual_balances_product_non_decreasing` | · | · | · | · | · | ❌ 9.0k | ❌ — | ❌ 12.9k | · | · | · |
| `cork/pool_solvency/solvency_preserved` | · | · | · | · | · | ❌ 7.5k | ❌ — | ❌ 10.7k | · | · | · |
| `damn_vulnerable_defi/side_entrance/deposit_sets_pool_balance` | ✅ ≈192.4k total | ✅ 13.2k ($1.52) | ✅ 8.9k ($0.35) | ✅ 792 ($0.85) | ✅ 1.8k ($0.32) | ✅ 2.5k | ❌ — | ✅ 1.6k | ❌ — | ✅ 2.1k ($0.17) | ✅ 10.5k ($0.59) |
| `damn_vulnerable_defi/side_entrance/deposit_sets_sender_credit` | · | · | · | · | · | ✅ 589 | ❌ — | ✅ 855 | · | · | · |
| `damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool` | · | · | · | · | · | ❌ 10.1k | ❌ — | ❌ 12.8k | · | · | · |
| `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance` | · | · | · | · | · | ✅ 865 | ❌ — | ✅ 2.0k | · | · | · |
| `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_sets_sender_credit` | · | · | · | · | · | ✅ 932 | ❌ — | ✅ 3.2k | · | · | · |
| `ethereum/deposit_contract_minimal/chain_start_threshold` | · | · | · | · | · | ✅ 1.1k | ❌ — | ✅ 628 | · | · | · |
| `ethereum/deposit_contract_minimal/deposit_count` | ✅ ≈123.6k total | ✅ 12.4k ($1.72) | ✅ 4.8k ($0.19) | ✅ 5.5k ($2.26) | ✅ 5.2k ($0.62) | ❌ 7.4k | ❌ — | ✅ 2.4k | ✅ — | ✅ 96.0k ($3.06) | ❌ 3.9k ($0.20) |
| `ethereum/deposit_contract_minimal/full_deposit_increments_full_count` | · | · | · | · | · | ✅ 7.8k | ❌ — | ✅ 2.8k | · | · | · |
| `ethereum/deposit_contract_minimal/full_deposit_preserves_partial_gap` | · | · | · | · | · | ❌ 6.3k | ❌ — | ❌ 17.9k | · | · | · |
| `ethereum/deposit_contract_minimal/small_deposit_preserves_full_count` | · | · | · | · | · | ❌ 10.2k | ❌ — | ✅ 5.3k | · | · | · |
| `forgeyields/global_solvency/claim_redeem_preserves_global_solvency` | · | · | · | · | · | ❌ 11.6k | ❌ — | ✅ 4.3k | · | · | · |
| `forgeyields/global_solvency/deposit_preserves_global_solvency` | · | · | · | · | · | ✅ 5.0k | ❌ — | ✅ 3.7k | · | · | · |
| `forgeyields/global_solvency/handle_preserves_global_solvency` | · | · | · | · | · | ❌ 8.7k | ❌ — | ✅ 4.7k | · | · | · |
| `forgeyields/global_solvency/redeem_token_gateway_depreciated_preserves_global_solvency` | · | · | · | · | · | ✅ 1.2k | ❌ — | ✅ 2.6k | · | · | · |
| `forgeyields/global_solvency/report_preserves_global_solvency` | · | · | · | · | · | ✅ 895 | ❌ — | ✅ 1.4k | · | · | · |
| `forgeyields/global_solvency/request_redeem_preserves_global_solvency` | · | · | · | · | · | ❌ 16.3k | ❌ — | ✅ 1.1k | · | · | · |
| `forgeyields/global_solvency/transfer_remote_preserves_global_solvency` | · | · | · | · | · | ✅ 2.3k | ❌ — | ✅ 2.4k | · | · | · |
| `ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free` | · | · | · | · | · | ❌ 21.2k | ❌ — | ❌ 6.2k | · | · | · |
| `ipor/plasma_vault_redeem_split/redeem_preserves_pps` | · | · | · | · | · | ❌ 19.0k | ❌ — | ❌ 17.6k | · | · | · |
| `kleros/sortition_trees/draw_interval_matches_weights` | · | · | · | · | · | ✅ 1.2k | ❌ — | ✅ 8.5k | · | · | · |
| `kleros/sortition_trees/draw_selects_valid_leaf` | · | · | · | · | · | ❌ 6.8k | ❌ — | ✅ 10.4k | · | · | · |
| `kleros/sortition_trees/node_id_bijection` | ✅ ≈192.8k total | ✅ 6.8k ($0.95) | ✅ 5.6k ($0.17) | ✅ 1.3k ($0.35) | ✅ 1.1k ($0.38) | ❌ 11.4k | ❌ — | ✅ 1.1k | ✅ — | ✅ 22.5k ($1.33) | ❌ 2.9k ($0.19) |
| `kleros/sortition_trees/parent_equals_sum_of_children` | · | · | · | · | · | ❌ 13.4k | ❌ — | ✅ 1.9k | · | · | · |
| `kleros/sortition_trees/root_equals_sum_of_leaves` | · | · | · | · | · | ✅ 1.4k | ❌ — | ✅ 2.2k | · | · | · |
| `kleros/sortition_trees/root_minus_left_equals_right_subtree` | · | · | · | · | · | ❌ 8.9k | ❌ — | ❌ 16.7k | · | · | · |
| `lagoon/guardrails/exact_compliance` | · | · | · | · | · | ❌ 5.7k | ❌ — | ❌ 26.2k | · | · | · |
| `lagoon/guardrails/negative_variation_bounded` | · | · | · | · | · | ❌ 12.0k | ❌ — | ❌ 8.6k | · | · | · |
| `lagoon/guardrails/positive_variation_bounded` | · | · | · | · | · | ❌ 3.6k | ❌ — | ❌ 17.7k | · | · | · |
| `lido/vaulthub_locked/ceildiv_sandwich` | · | · | · | · | · | ❌ 16.0k | ❌ — | ❌ 26.9k | · | · | · |
| `lido/vaulthub_locked/locked_funds_solvency` | · | · | · | · | · | ❌ 34.6k | ❌ — | ❌ 14.0k | · | · | · |
| `lido/vaulthub_locked/max_liability_shares_bound` | · | · | · | · | · | ✅ 342 | ❌ — | ✅ 476 | · | · | · |
| `lido/vaulthub_locked/reserve_ratio_bounds` | · | · | · | · | · | ✅ 733 | ❌ — | ✅ 573 | · | · | · |
| `lido/vaulthub_locked/shares_conversion_monotone` | · | · | · | · | · | ❌ 31.3k | ❌ — | ❌ 27.6k | · | · | · |
| `nexus_mutual/ramm_price_band/sync_sets_book_value` | ✅ ≈124.2k total | ✅ 3.8k ($0.68) | ✅ 6.9k ($0.24) | ✅ 1.0k ($1.23) | ✅ 2.5k ($0.58) | ✅ 697 | ❌ — | ✅ 733 | ✅ — | ✅ 5.9k ($0.33) | ✅ 3.6k ($0.10) |
| `nexus_mutual/ramm_price_band/sync_sets_buy_price` | · | · | · | · | · | ✅ 2.5k | ❌ — | ✅ 3.8k | · | · | · |
| `nexus_mutual/ramm_price_band/sync_sets_capital` | · | · | · | · | · | ✅ 1.5k | ❌ — | ✅ 461 | · | · | · |
| `nexus_mutual/ramm_price_band/sync_sets_sell_price` | · | · | · | · | · | ✅ 953 | ❌ — | ✅ 354 | · | · | · |
| `onedelta/caller_address_integrity/delta_compose_internal_erc20_transfer_from_uses_outer_caller` | · | · | · | · | · | ❌ 8.8k | ❌ — | ✅ 2.9k | · | · | · |
| `onedelta/caller_address_integrity/delta_compose_internal_permit2_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 9.3k | ❌ — | ✅ 1.1k | · | · | · |
| `onedelta/caller_address_integrity/direct_erc20_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 3.4k | ❌ — | ✅ 3.5k | · | · | · |
| `onedelta/caller_address_integrity/direct_permit2_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 3.3k | ❌ — | ✅ 1.5k | · | · | · |
| `onedelta/caller_address_integrity/flash_callback_erc20_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 5.6k | ❌ — | ✅ 4.7k | · | · | · |
| `onedelta/caller_address_integrity/nested_flash_and_swap_callbacks_keep_outer_caller` | · | · | · | · | · | ✅ 2.4k | ❌ — | ✅ 1.2k | · | · | · |
| `onedelta/caller_address_integrity/swap_callback_permit2_transfer_from_uses_outer_caller` | · | · | · | · | · | ❌ 13.9k | ❌ — | ✅ 3.6k | · | · | · |
| `onedelta/caller_address_integrity/transfers_erc20_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 2.2k | ❌ — | ✅ 4.9k | · | · | · |
| `onedelta/caller_address_integrity/transfers_permit2_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 3.8k | ❌ — | ✅ 1.0k | · | · | · |
| `onedelta/caller_address_integrity/v3_callback_direct_transfer_from_uses_outer_caller` | · | · | · | · | · | ✅ 3.2k | ❌ — | ✅ 2.9k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_claim_marks_both_claimed` | · | · | · | · | · | ❌ 9.3k | ❌ — | ❌ 7.8k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_round_claimed` | · | · | · | · | · | ❌ 13.5k | ❌ — | ❌ 15.1k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_total_allocated` | · | · | · | · | · | ❌ 10.8k | ❌ — | ❌ 10.5k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_claimed_plus_allocated_conserved` | · | · | · | · | · | ❌ 14.5k | ❌ — | ❌ 6.8k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_matches_independent_claims` | · | · | · | · | · | ❌ 10.2k | ❌ — | ❌ 11.4k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_no_overclaim` | · | · | · | · | · | ❌ 14.7k | ❌ — | ❌ 12.6k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_usdc_bound_violation_rejected` | · | · | · | · | · | ❌ 6.0k | ❌ — | ❌ 9.8k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_usdc_double_claim_rejected` | · | · | · | · | · | ❌ 6.9k | ❌ — | ❌ 14.2k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_weth_bound_violation_rejected` | · | · | · | · | · | ❌ 7.7k | ❌ — | ❌ 19.3k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/both_weth_double_claim_rejected` | · | · | · | · | · | ❌ 8.2k | ❌ — | ❌ 14.7k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/bound_violation_rejected` | · | · | · | · | · | ❌ 6.0k | ❌ — | ❌ 26.0k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/claim_marks_user` | ✅ ≈151.3k total | ✅ 20.7k ($2.52) | ✅ 16.8k ($0.55) | ✅ 6.3k ($3.72) | ❌ 21.5k ($3.94) | ✅ 4.3k | ❌ — | ✅ 7.3k | ✅ — | ✅ 7.5k ($0.39) | ✅ 92.7k ($2.30) |
| `paladin_votes/stream_recovery_claim_usdc/claim_updates_round_claimed` | · | · | · | · | · | ❌ 14.4k | ❌ — | ❌ 10.6k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/claim_updates_total_allocated` | · | · | · | · | · | ❌ 17.1k | ❌ — | ✅ 8.6k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/claimed_plus_allocated_conserved` | · | · | · | · | · | ❌ 16.2k | ❌ — | ❌ 14.2k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/double_claim_rejected` | · | · | · | · | · | ✅ 2.3k | ❌ — | ✅ 4.3k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/no_overclaim` | · | · | · | · | · | ✅ 6.1k | ❌ — | ✅ 14.6k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/usdc_preserves_weth_state` | · | · | · | · | · | ✅ 8.3k | ❌ — | ✅ 12.0k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_bound_violation_rejected` | · | · | · | · | · | ❌ 15.8k | ❌ — | ❌ 15.9k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_claim_marks_user` | · | · | · | · | · | ❌ 11.3k | ❌ — | ✅ 6.5k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_round_claimed` | · | · | · | · | · | ❌ 9.1k | ❌ — | ✅ 5.7k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_total_allocated` | · | · | · | · | · | ❌ 13.0k | ❌ — | ❌ 21.4k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_claimed_plus_allocated_conserved` | · | · | · | · | · | ❌ 10.4k | ❌ — | ❌ 26.7k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_double_claim_rejected` | · | · | · | · | · | ✅ 2.5k | ❌ — | ✅ 1.3k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_no_overclaim` | · | · | · | · | · | ❌ 9.6k | ❌ — | ✅ 7.8k | · | · | · |
| `paladin_votes/stream_recovery_claim_usdc/weth_preserves_usdc_state` | · | · | · | · | · | ✅ 2.5k | ❌ — | ✅ 13.5k | · | · | · |
| `piku/fund_conservation/amount_paid_preserves_fund_conservation` | · | · | · | · | · | ❌ 21.0k | ❌ — | ❌ 12.1k | · | · | · |
| `piku/fund_conservation/amount_paid_records_distribution` | · | · | · | · | · | ✅ 1.6k | ❌ — | ✅ 2.9k | · | · | · |
| `piku/fund_conservation/sell_order_preserves_fund_conservation` | · | · | · | · | · | ❌ 15.4k | ❌ — | ❌ 19.3k | · | · | · |
| `piku/fund_conservation/sell_order_records_redemption_buckets` | · | · | · | · | · | ❌ 16.8k | ❌ — | ❌ 16.1k | · | · | · |
| `polaris/bonding_curve/buy_preserves_reserve_ratio_zero` | · | · | · | · | · | ❌ 18.1k | ❌ — | ❌ 7.9k | · | · | · |
| `polaris/bonding_curve/floor_sell_and_burn_preserves_reserve_ratio_zero` | · | · | · | · | · | ❌ 15.8k | ❌ — | ❌ 6.1k | · | · | · |
| `polaris/bonding_curve/init_reserve_ratio_zero` | · | · | · | · | · | ❌ 7.7k | ❌ — | ❌ 19.9k | · | · | · |
| `polaris/bonding_curve/sell_preserves_reserve_ratio_zero` | · | · | · | · | · | ❌ 15.4k | ❌ — | ❌ 5.8k | · | · | · |
| `polygon/agglayer_bridge/claimAsset_valid_leaf_and_consumes_unique_nullifier` | · | · | · | · | · | ❌ 11.4k | ❌ — | ❌ 7.9k | · | · | · |
| `polygon/agglayer_bridge/claimMessage_valid_leaf_and_consumes_unique_nullifier` | · | · | · | · | · | ❌ 15.9k | ❌ — | ❌ 8.4k | · | · | · |
| `reserve/auction_price_band/price_at_end_time` | · | · | · | · | · | ✅ 2.2k | ❌ — | ✅ 1.2k | · | · | · |
| `reserve/auction_price_band/price_at_start_time` | · | · | · | · | · | ✅ 1.6k | ❌ — | ✅ 1.2k | · | · | · |
| `reserve/auction_price_band/price_lower_bound` | · | · | · | · | · | ❌ 11.3k | ❌ — | ✅ 1.1k | · | · | · |
| `reserve/auction_price_band/price_upper_bound` | · | · | · | · | · | ❌ 7.2k | ❌ — | ❌ 4.5k | · | · | · |
| `rootstock/flyover_quote_lifecycle/deposit_peg_out_registers_required_amount` | · | · | · | · | · | ❌ 6.5k | ❌ — | ❌ 7.7k | · | · | · |
| `rootstock/flyover_quote_lifecycle/refund_peg_out_conserves_quote_amount` | · | · | · | · | · | ❌ 7.4k | ❌ — | ❌ 4.6k | · | · | · |
| `rootstock/flyover_quote_lifecycle/refund_user_peg_out_conserves_quote_amount` | · | · | · | · | · | ❌ 13.1k | ❌ — | ❌ 7.0k | · | · | · |
| `safe/owner_manager_reach/add_owner_acyclicity` | · | · | · | · | · | ❌ 13.0k | ❌ — | ❌ 12.2k | · | · | · |
| `safe/owner_manager_reach/add_owner_is_owner_correctness` | · | · | · | · | · | ❌ 11.0k | ❌ — | ❌ 16.6k | · | · | · |
| `safe/owner_manager_reach/add_owner_owner_list_invariant` | · | · | · | · | · | ❌ 21.5k | ❌ — | ❌ 8.9k | · | · | · |
| `safe/owner_manager_reach/in_list_reachable` | · | · | · | · | · | ❌ 8.7k | ❌ — | ❌ 18.6k | · | · | · |
| `safe/owner_manager_reach/remove_owner_acyclicity` | · | · | · | · | · | ❌ 9.8k | ❌ — | ❌ 26.6k | · | · | · |
| `safe/owner_manager_reach/remove_owner_in_list_reachable` | · | · | · | · | · | ❌ 10.2k | ❌ — | ❌ 18.7k | · | · | · |
| `safe/owner_manager_reach/remove_owner_is_owner_correctness` | · | · | · | · | · | ❌ 7.2k | ❌ — | ❌ 6.4k | · | · | · |
| `safe/owner_manager_reach/remove_owner_owner_list_invariant` | · | · | · | · | · | ❌ 24.0k | ❌ — | ❌ 15.1k | · | · | · |
| `safe/owner_manager_reach/setup_owners_acyclicity` | · | · | · | · | · | ❌ 14.0k | ❌ — | ❌ 12.0k | · | · | · |
| `safe/owner_manager_reach/setup_owners_in_list_reachable` | · | · | · | · | · | ❌ 15.9k | ❌ — | ❌ 7.3k | · | · | · |
| `safe/owner_manager_reach/setup_owners_owner_list_invariant` | · | · | · | · | · | ❌ 11.9k | ❌ — | ❌ 11.2k | · | · | · |
| `safe/owner_manager_reach/swap_owner_acyclicity` | · | · | · | · | · | ❌ 108.1k | ❌ — | ❌ 39.4k | · | · | · |
| `safe/owner_manager_reach/swap_owner_in_list_reachable` | · | · | · | · | · | ❌ 17.6k | ❌ — | ❌ 29.6k | · | · | · |
| `safe/owner_manager_reach/swap_owner_is_owner_correctness` | · | · | · | · | · | ❌ 13.0k | ❌ — | ❌ 4.9k | · | · | · |
| `safe/owner_manager_reach/swap_owner_owner_list_invariant` | · | · | · | · | · | ❌ 9.1k | ❌ — | ❌ 15.2k | · | · | · |
| `term_finance/term_auction_clearing/clearing_assignment_correct` | · | · | · | · | · | ❌ 15.6k | ❌ — | ❌ 12.2k | · | · | · |
| `termmax/order_v2_buy_xt_single_segment/swap_debt_token_to_xt_updates_virtual_xt_reserve` | · | · | · | · | · | ❌ 34.8k | ❌ — | ❌ 8.5k | · | · | · |
| `usual/dao_collateral/redeem_conservation` | · | · | · | · | · | ❌ 7.7k | ❌ — | ❌ 9.4k | · | · | · |
| `usual/dao_collateral/redeem_fee_formula` | · | · | · | · | · | ✅ 1.2k | ❌ — | ✅ 1.7k | · | · | · |
| `usual/dao_collateral/redeem_return_formula` | · | · | · | · | · | ❌ 9.8k | ❌ — | ❌ 5.0k | · | · | · |
| `usual/dao_collateral/swap_conservation` | · | · | · | · | · | ❌ 7.2k | ❌ — | ❌ 12.0k | · | · | · |
| `usual/dao_collateral/swap_value_conservation` | · | · | · | · | · | ❌ 8.5k | ❌ — | ❌ 8.5k | · | · | · |
| `wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity` | · | · | · | · | · | ❌ 57.6k | ✅ — | ✅ 2.4k | · | · | · |
| `zama/erc7984_confidential_token/burn_decreases_supply` | · | · | · | · | · | ❌ 14.4k | ❌ — | ❌ 10.5k | · | · | · |
| `zama/erc7984_confidential_token/burn_insufficient` | · | · | · | · | · | ❌ 15.0k | ❌ — | ❌ 7.6k | · | · | · |
| `zama/erc7984_confidential_token/mint_ctokens_match_deposit` | · | · | · | · | · | ❌ 18.5k | ❌ — | ❌ 18.9k | · | · | · |
| `zama/erc7984_confidential_token/mint_increases_supply` | · | · | · | · | · | ❌ 14.2k | ❌ — | ❌ 7.4k | · | · | · |
| `zama/erc7984_confidential_token/mint_overflow_protection` | · | · | · | · | · | ❌ 15.4k | ❌ — | ❌ 11.2k | · | · | · |
| `zama/erc7984_confidential_token/setOperator_updates` | · | · | · | · | · | ✅ 2.9k | ❌ — | ✅ 5.3k | · | · | · |
| `zama/erc7984_confidential_token/transferFrom_conservation` | · | · | · | · | · | ❌ 8.6k | ❌ — | ❌ 15.6k | · | · | · |
| `zama/erc7984_confidential_token/transfer_conservation` | · | · | · | · | · | ❌ 12.5k | ❌ — | ❌ 16.6k | · | · | · |
| `zama/erc7984_confidential_token/transfer_insufficient` | · | · | · | · | · | ❌ 9.9k | ❌ — | ❌ 9.6k | · | · | · |
| `zama/erc7984_confidential_token/transfer_no_balance_revert` | · | · | · | · | · | ✅ 6.4k | ❌ — | ❌ 6.5k | · | · | · |
| `zama/erc7984_confidential_token/transfer_preserves_supply` | · | · | · | · | · | ❌ 10.4k | ❌ — | ❌ 6.0k | · | · | · |
| `zama/erc7984_confidential_token/transfer_sufficient` | · | · | · | · | · | ❌ 14.2k | ❌ — | ❌ 7.1k | · | · | · |
| `zodiac/roles_decoder_faithfulness/metadata_bridge` | · | · | · | · | · | ❌ 10.9k | ❌ — | ❌ 27.0k | · | · | · |
| `zodiac/roles_decoder_faithfulness/roles_decoder_bounds_safe` | · | · | · | · | · | ❌ 8.6k | ❌ — | ❌ 20.6k | · | · | · |
| `zodiac/roles_decoder_faithfulness/roles_decoder_faithful` | · | · | · | · | · | ❌ 13.6k | ❌ — | ❌ 15.8k | · | · | · |

Notes: completion tokens are what the model generated (the main cost driver per
provider pricing); prompt tokens show how context-hungry each harness is. Shell
harness rows have no attempt counts because iteration happens inside the CLI.
Values marked *(est.)* are estimates, not measurements: grok-cli exposes no token
telemetry at all (range derived from turn counts, run durations, and the same
model's measured usage under the builtin harness); codex reports only an
undecomposed total (cost range assumes 90-99% of tokens are prompt-side, the
typical split for coding agents).
