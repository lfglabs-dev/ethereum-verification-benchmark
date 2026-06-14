# Verity Benchmark Leaderboard

Generated 2026-06-14 07:48Z · commit `a85f0cf61` · budget `normal`

**Ranked by total cost (cheapest first).** All combos run the same task set;
pass/fail is decided by the independent verifier; tokens are counted across the
whole agent loop (builtin: in-loop accounting; shell harnesses: metered at the API
boundary by the harness proxy).

| Harness | Model | Pass | Median completion tok / pass | Median prompt tok / pass | Median cost / pass | Total completion tok | Total prompt tok | Total cost |
|---|---|---|---|---|---|---|---|---|
| builtin (fair) | gpt55 | 5/5 | 1.3k | 240.7k | $1.23 | 14.9k | 1.6M | $8.42 |
| builtin (fair) | minimax/minimax-m3 | 38/135 | 2.3k | 156.7k | $0.049 | 1.5M | 102.9M | $32.62 |
| builtin (fair) | zai/glm-5.2 | 53/135 | 2.6k | 105.7k | $0.066 | 1.3M | 61.7M | $39.88 |
| builtin (fair) | Step37 | 1/135 | — | — | — | — | — | — |

## Per-task completion tokens

Cell = ✅/❌ with completion tokens spent on that task (including failed attempts).

| Task | builtin (fair)<br>gpt55 | builtin (fair)<br>minimax/minimax-m3 | builtin (fair)<br>Step37 | builtin (fair)<br>zai/glm-5.2 |
|---|---|---|---|---|
| `alchemix/earmark_conservation/earmark_preserves_invariant` | · | ❌ 7.3k ($0.30) | ❌ — | ❌ 14.6k ($0.34) |
| `alchemix/earmark_conservation/redeem_preserves_invariant` | · | ❌ 11.7k ($0.28) | ❌ — | ❌ 12.6k ($0.56) |
| `alchemix/earmark_conservation/sub_debt_preserves_invariant` | · | ❌ 15.8k ($0.37) | ❌ — | ❌ 12.8k ($0.33) |
| `alchemix/earmark_conservation/sub_earmarked_debt_preserves_invariant` | · | ❌ 7.0k ($0.19) | ❌ — | ❌ 8.6k ($0.33) |
| `alchemix/earmark_conservation/sync_account_preserves_invariant` | · | ❌ 10.3k ($0.41) | ❌ — | ❌ 8.8k ($0.45) |
| `balancer/reclamm_swap_rounding/on_swap_fixed_virtual_balances_product_non_decreasing` | · | ❌ 9.0k ($0.26) | ❌ — | ❌ 12.9k ($0.35) |
| `cork/pool_solvency/solvency_preserved` | · | ❌ 7.5k ($0.22) | ❌ — | ❌ 10.7k ($0.32) |
| `damn_vulnerable_defi/side_entrance/deposit_sets_pool_balance` | ✅ 792 ($0.85) | ✅ 2.5k ($0.093) | ❌ — | ✅ 1.6k ($0.041) |
| `damn_vulnerable_defi/side_entrance/deposit_sets_sender_credit` | · | ✅ 589 ($0.007) | ❌ — | ✅ 855 ($0.021) |
| `damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool` | · | ❌ 10.1k ($0.42) | ❌ — | ❌ 12.8k ($0.44) |
| `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance` | · | ✅ 865 ($0.007) | ❌ — | ✅ 2.0k ($0.074) |
| `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_sets_sender_credit` | · | ✅ 932 ($0.013) | ❌ — | ✅ 3.2k ($0.079) |
| `ethereum/deposit_contract_minimal/chain_start_threshold` | · | ✅ 1.1k ($0.013) | ❌ — | ✅ 628 ($0.023) |
| `ethereum/deposit_contract_minimal/deposit_count` | ✅ 5.5k ($2.26) | ❌ 7.4k ($0.14) | ❌ — | ✅ 2.4k ($0.060) |
| `ethereum/deposit_contract_minimal/full_deposit_increments_full_count` | · | ✅ 7.8k ($0.22) | ❌ — | ✅ 2.8k ($0.044) |
| `ethereum/deposit_contract_minimal/full_deposit_preserves_partial_gap` | · | ❌ 6.3k ($0.36) | ❌ — | ❌ 17.9k ($0.59) |
| `ethereum/deposit_contract_minimal/small_deposit_preserves_full_count` | · | ❌ 10.2k ($0.35) | ❌ — | ✅ 5.3k ($0.083) |
| `forgeyields/global_solvency/claim_redeem_preserves_global_solvency` | · | ❌ 11.6k ($0.43) | ❌ — | ✅ 4.3k ($0.045) |
| `forgeyields/global_solvency/deposit_preserves_global_solvency` | · | ✅ 5.0k ($0.041) | ❌ — | ✅ 3.7k ($0.081) |
| `forgeyields/global_solvency/handle_preserves_global_solvency` | · | ❌ 8.7k ($0.22) | ❌ — | ✅ 4.7k ($0.081) |
| `forgeyields/global_solvency/redeem_token_gateway_depreciated_preserves_global_solvency` | · | ✅ 1.2k ($0.010) | ❌ — | ✅ 2.6k ($0.058) |
| `forgeyields/global_solvency/report_preserves_global_solvency` | · | ✅ 895 ($0.011) | ❌ — | ✅ 1.4k ($0.089) |
| `forgeyields/global_solvency/request_redeem_preserves_global_solvency` | · | ❌ 16.3k ($0.31) | ❌ — | ✅ 1.1k ($0.015) |
| `forgeyields/global_solvency/transfer_remote_preserves_global_solvency` | · | ✅ 2.3k ($0.058) | ❌ — | ✅ 2.4k ($0.050) |
| `ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free` | · | ❌ 21.2k ($0.30) | ❌ — | ❌ 6.2k ($0.077) |
| `ipor/plasma_vault_redeem_split/redeem_preserves_pps` | · | ❌ 19.0k ($0.12) | ❌ — | ❌ 17.6k ($0.067) |
| `kleros/sortition_trees/draw_interval_matches_weights` | · | ✅ 1.2k ($0.041) | ❌ — | ✅ 8.5k ($0.23) |
| `kleros/sortition_trees/draw_selects_valid_leaf` | · | ❌ 6.8k ($0.20) | ❌ — | ✅ 10.4k ($0.45) |
| `kleros/sortition_trees/node_id_bijection` | ✅ 1.3k ($0.35) | ❌ 11.4k ($0.37) | ❌ — | ✅ 1.1k ($0.066) |
| `kleros/sortition_trees/parent_equals_sum_of_children` | · | ❌ 13.4k ($0.31) | ❌ — | ✅ 1.9k ($0.031) |
| `kleros/sortition_trees/root_equals_sum_of_leaves` | · | ✅ 1.4k ($0.032) | ❌ — | ✅ 2.2k ($0.025) |
| `kleros/sortition_trees/root_minus_left_equals_right_subtree` | · | ❌ 8.9k ($0.32) | ❌ — | ❌ 16.7k ($0.42) |
| `lagoon/guardrails/exact_compliance` | · | ❌ 5.7k ($0.059) | ❌ — | ❌ 26.2k ($0.46) |
| `lagoon/guardrails/negative_variation_bounded` | · | ❌ 12.0k ($0.23) | ❌ — | ❌ 8.6k ($0.15) |
| `lagoon/guardrails/positive_variation_bounded` | · | ❌ 3.6k ($0.11) | ❌ — | ❌ 17.7k ($0.32) |
| `lido/vaulthub_locked/ceildiv_sandwich` | · | ❌ 16.0k ($0.42) | ❌ — | ❌ 26.9k ($0.57) |
| `lido/vaulthub_locked/locked_funds_solvency` | · | ❌ 34.6k ($0.50) | ❌ — | ❌ 14.0k ($0.39) |
| `lido/vaulthub_locked/max_liability_shares_bound` | · | ✅ 342 ($0.004) | ❌ — | ✅ 476 ($0.006) |
| `lido/vaulthub_locked/reserve_ratio_bounds` | · | ✅ 733 ($0.008) | ❌ — | ✅ 573 ($0.019) |
| `lido/vaulthub_locked/shares_conversion_monotone` | · | ❌ 31.3k ($0.43) | ❌ — | ❌ 27.6k ($0.64) |
| `nexus_mutual/ramm_price_band/sync_sets_book_value` | ✅ 1.0k ($1.23) | ✅ 697 ($0.013) | ❌ — | ✅ 733 ($0.025) |
| `nexus_mutual/ramm_price_band/sync_sets_buy_price` | · | ✅ 2.5k ($0.038) | ❌ — | ✅ 3.8k ($0.12) |
| `nexus_mutual/ramm_price_band/sync_sets_capital` | · | ✅ 1.5k ($0.031) | ❌ — | ✅ 461 ($0.019) |
| `nexus_mutual/ramm_price_band/sync_sets_sell_price` | · | ✅ 953 ($0.009) | ❌ — | ✅ 354 ($0.012) |
| `onedelta/caller_address_integrity/delta_compose_internal_erc20_transfer_from_uses_outer_caller` | · | ❌ 8.8k ($0.25) | ❌ — | ✅ 2.9k ($0.065) |
| `onedelta/caller_address_integrity/delta_compose_internal_permit2_transfer_from_uses_outer_caller` | · | ✅ 9.3k ($0.17) | ❌ — | ✅ 1.1k ($0.068) |
| `onedelta/caller_address_integrity/direct_erc20_transfer_from_uses_outer_caller` | · | ✅ 3.4k ($0.061) | ❌ — | ✅ 3.5k ($0.12) |
| `onedelta/caller_address_integrity/direct_permit2_transfer_from_uses_outer_caller` | · | ✅ 3.3k ($0.11) | ❌ — | ✅ 1.5k ($0.056) |
| `onedelta/caller_address_integrity/flash_callback_erc20_transfer_from_uses_outer_caller` | · | ✅ 5.6k ($0.14) | ❌ — | ✅ 4.7k ($0.14) |
| `onedelta/caller_address_integrity/nested_flash_and_swap_callbacks_keep_outer_caller` | · | ✅ 2.4k ($0.051) | ❌ — | ✅ 1.2k ($0.059) |
| `onedelta/caller_address_integrity/swap_callback_permit2_transfer_from_uses_outer_caller` | · | ❌ 13.9k ($0.38) | ❌ — | ✅ 3.6k ($0.12) |
| `onedelta/caller_address_integrity/transfers_erc20_transfer_from_uses_outer_caller` | · | ✅ 2.2k ($0.055) | ❌ — | ✅ 4.9k ($0.14) |
| `onedelta/caller_address_integrity/transfers_permit2_transfer_from_uses_outer_caller` | · | ✅ 3.8k ($0.13) | ❌ — | ✅ 1.0k ($0.049) |
| `onedelta/caller_address_integrity/v3_callback_direct_transfer_from_uses_outer_caller` | · | ✅ 3.2k ($0.056) | ❌ — | ✅ 2.9k ($0.13) |
| `paladin_votes/stream_recovery_claim_usdc/both_claim_marks_both_claimed` | · | ❌ 9.3k ($0.20) | ❌ — | ❌ 7.8k ($0.39) |
| `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_round_claimed` | · | ❌ 13.5k ($0.41) | ❌ — | ❌ 15.1k ($0.44) |
| `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_total_allocated` | · | ❌ 10.8k ($0.32) | ❌ — | ❌ 10.5k ($0.43) |
| `paladin_votes/stream_recovery_claim_usdc/both_claimed_plus_allocated_conserved` | · | ❌ 14.5k ($0.34) | ❌ — | ❌ 6.8k ($0.46) |
| `paladin_votes/stream_recovery_claim_usdc/both_matches_independent_claims` | · | ❌ 10.2k ($0.25) | ❌ — | ❌ 11.4k ($0.43) |
| `paladin_votes/stream_recovery_claim_usdc/both_no_overclaim` | · | ❌ 14.7k ($0.29) | ❌ — | ❌ 12.6k ($0.42) |
| `paladin_votes/stream_recovery_claim_usdc/both_usdc_bound_violation_rejected` | · | ❌ 6.0k ($0.23) | ❌ — | ❌ 9.8k ($0.57) |
| `paladin_votes/stream_recovery_claim_usdc/both_usdc_double_claim_rejected` | · | ❌ 6.9k ($0.29) | ❌ — | ❌ 14.2k ($0.36) |
| `paladin_votes/stream_recovery_claim_usdc/both_weth_bound_violation_rejected` | · | ❌ 7.7k ($0.17) | ❌ — | ❌ 19.3k ($0.66) |
| `paladin_votes/stream_recovery_claim_usdc/both_weth_double_claim_rejected` | · | ❌ 8.2k ($0.27) | ❌ — | ❌ 14.7k ($0.22) |
| `paladin_votes/stream_recovery_claim_usdc/bound_violation_rejected` | · | ❌ 6.0k ($0.40) | ❌ — | ❌ 26.0k ($0.59) |
| `paladin_votes/stream_recovery_claim_usdc/claim_marks_user` | ✅ 6.3k ($3.72) | ✅ 4.3k ($0.15) | ❌ — | ✅ 7.3k ($0.13) |
| `paladin_votes/stream_recovery_claim_usdc/claim_updates_round_claimed` | · | ❌ 14.4k ($0.27) | ❌ — | ❌ 10.6k ($0.63) |
| `paladin_votes/stream_recovery_claim_usdc/claim_updates_total_allocated` | · | ❌ 17.1k ($0.28) | ❌ — | ✅ 8.6k ($0.39) |
| `paladin_votes/stream_recovery_claim_usdc/claimed_plus_allocated_conserved` | · | ❌ 16.2k ($0.38) | ❌ — | ❌ 14.2k ($0.57) |
| `paladin_votes/stream_recovery_claim_usdc/double_claim_rejected` | · | ✅ 2.3k ($0.065) | ❌ — | ✅ 4.3k ($0.12) |
| `paladin_votes/stream_recovery_claim_usdc/no_overclaim` | · | ✅ 6.1k ($0.096) | ❌ — | ✅ 14.6k ($0.28) |
| `paladin_votes/stream_recovery_claim_usdc/usdc_preserves_weth_state` | · | ✅ 8.3k ($0.10) | ❌ — | ✅ 12.0k ($0.78) |
| `paladin_votes/stream_recovery_claim_usdc/weth_bound_violation_rejected` | · | ❌ 15.8k ($0.49) | ❌ — | ❌ 15.9k ($0.76) |
| `paladin_votes/stream_recovery_claim_usdc/weth_claim_marks_user` | · | ❌ 11.3k ($0.29) | ❌ — | ✅ 6.5k ($0.090) |
| `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_round_claimed` | · | ❌ 9.1k ($0.26) | ❌ — | ✅ 5.7k ($0.080) |
| `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_total_allocated` | · | ❌ 13.0k ($0.34) | ❌ — | ❌ 21.4k ($0.36) |
| `paladin_votes/stream_recovery_claim_usdc/weth_claimed_plus_allocated_conserved` | · | ❌ 10.4k ($0.30) | ❌ — | ❌ 26.7k ($0.53) |
| `paladin_votes/stream_recovery_claim_usdc/weth_double_claim_rejected` | · | ✅ 2.5k ($0.079) | ❌ — | ✅ 1.3k ($0.023) |
| `paladin_votes/stream_recovery_claim_usdc/weth_no_overclaim` | · | ❌ 9.6k ($0.24) | ❌ — | ✅ 7.8k ($0.45) |
| `paladin_votes/stream_recovery_claim_usdc/weth_preserves_usdc_state` | · | ✅ 2.5k ($0.055) | ❌ — | ✅ 13.5k ($0.57) |
| `piku/fund_conservation/amount_paid_preserves_fund_conservation` | · | ❌ 21.0k ($0.36) | ❌ — | ❌ 12.1k ($0.55) |
| `piku/fund_conservation/amount_paid_records_distribution` | · | ✅ 1.6k ($0.052) | ❌ — | ✅ 2.9k ($0.13) |
| `piku/fund_conservation/sell_order_preserves_fund_conservation` | · | ❌ 15.4k ($0.35) | ❌ — | ❌ 19.3k ($0.43) |
| `piku/fund_conservation/sell_order_records_redemption_buckets` | · | ❌ 16.8k ($0.36) | ❌ — | ❌ 16.1k ($0.56) |
| `polaris/bonding_curve/buy_preserves_reserve_ratio_zero` | · | ❌ 18.1k ($0.42) | ❌ — | ❌ 7.9k ($0.34) |
| `polaris/bonding_curve/floor_sell_and_burn_preserves_reserve_ratio_zero` | · | ❌ 15.8k ($0.34) | ❌ — | ❌ 6.1k ($0.35) |
| `polaris/bonding_curve/init_reserve_ratio_zero` | · | ❌ 7.7k ($0.39) | ❌ — | ❌ 19.9k ($0.49) |
| `polaris/bonding_curve/sell_preserves_reserve_ratio_zero` | · | ❌ 15.4k ($0.34) | ❌ — | ❌ 5.8k ($0.32) |
| `polygon/agglayer_bridge/claimAsset_valid_leaf_and_consumes_unique_nullifier` | · | ❌ 11.4k ($0.27) | ❌ — | ❌ 7.9k ($0.47) |
| `polygon/agglayer_bridge/claimMessage_valid_leaf_and_consumes_unique_nullifier` | · | ❌ 15.9k ($0.33) | ❌ — | ❌ 8.4k ($0.32) |
| `reserve/auction_price_band/price_at_end_time` | · | ✅ 2.2k ($0.035) | ❌ — | ✅ 1.2k ($0.054) |
| `reserve/auction_price_band/price_at_start_time` | · | ✅ 1.6k ($0.048) | ❌ — | ✅ 1.2k ($0.065) |
| `reserve/auction_price_band/price_lower_bound` | · | ❌ 11.3k ($0.24) | ❌ — | ✅ 1.1k ($0.056) |
| `reserve/auction_price_band/price_upper_bound` | · | ❌ 7.2k ($0.33) | ❌ — | ❌ 4.5k ($0.43) |
| `rootstock/flyover_quote_lifecycle/deposit_peg_out_registers_required_amount` | · | ❌ 6.5k ($0.29) | ❌ — | ❌ 7.7k ($0.29) |
| `rootstock/flyover_quote_lifecycle/refund_peg_out_conserves_quote_amount` | · | ❌ 7.4k ($0.22) | ❌ — | ❌ 4.6k ($0.25) |
| `rootstock/flyover_quote_lifecycle/refund_user_peg_out_conserves_quote_amount` | · | ❌ 13.1k ($0.27) | ❌ — | ❌ 7.0k ($0.55) |
| `safe/owner_manager_reach/add_owner_acyclicity` | · | ❌ 13.0k ($0.32) | ❌ — | ❌ 12.2k ($0.42) |
| `safe/owner_manager_reach/add_owner_is_owner_correctness` | · | ❌ 11.0k ($0.26) | ❌ — | ❌ 16.6k ($0.39) |
| `safe/owner_manager_reach/add_owner_owner_list_invariant` | · | ❌ 21.5k ($0.36) | ❌ — | ❌ 8.9k ($0.50) |
| `safe/owner_manager_reach/in_list_reachable` | · | ❌ 8.7k ($0.41) | ❌ — | ❌ 18.6k ($0.36) |
| `safe/owner_manager_reach/remove_owner_acyclicity` | · | ❌ 9.8k ($0.28) | ❌ — | ❌ 26.6k ($0.39) |
| `safe/owner_manager_reach/remove_owner_in_list_reachable` | · | ❌ 10.2k ($0.37) | ❌ — | ❌ 18.7k ($0.34) |
| `safe/owner_manager_reach/remove_owner_is_owner_correctness` | · | ❌ 7.2k ($0.33) | ❌ — | ❌ 6.4k ($0.28) |
| `safe/owner_manager_reach/remove_owner_owner_list_invariant` | · | ❌ 24.0k ($0.33) | ❌ — | ❌ 15.1k ($0.44) |
| `safe/owner_manager_reach/setup_owners_acyclicity` | · | ❌ 14.0k ($0.39) | ❌ — | ❌ 12.0k ($0.084) |
| `safe/owner_manager_reach/setup_owners_in_list_reachable` | · | ❌ 15.9k ($0.21) | ❌ — | ❌ 7.3k ($0.31) |
| `safe/owner_manager_reach/setup_owners_owner_list_invariant` | · | ❌ 11.9k ($0.35) | ❌ — | ❌ 11.2k ($0.44) |
| `safe/owner_manager_reach/swap_owner_acyclicity` | · | ❌ 108.1k ($0.80) | ❌ — | ❌ 39.4k ($0.53) |
| `safe/owner_manager_reach/swap_owner_in_list_reachable` | · | ❌ 17.6k ($0.19) | ❌ — | ❌ 29.6k ($0.25) |
| `safe/owner_manager_reach/swap_owner_is_owner_correctness` | · | ❌ 13.0k ($0.32) | ❌ — | ❌ 4.9k ($0.37) |
| `safe/owner_manager_reach/swap_owner_owner_list_invariant` | · | ❌ 9.1k ($0.24) | ❌ — | ❌ 15.2k ($0.32) |
| `term_finance/term_auction_clearing/clearing_assignment_correct` | · | ❌ 15.6k ($0.21) | ❌ — | ❌ 12.2k ($0.063) |
| `termmax/order_v2_buy_xt_single_segment/swap_debt_token_to_xt_updates_virtual_xt_reserve` | · | ❌ 34.8k ($0.43) | ❌ — | ❌ 8.5k ($0.33) |
| `usual/dao_collateral/redeem_conservation` | · | ❌ 7.7k ($0.21) | ❌ — | ❌ 9.4k ($0.44) |
| `usual/dao_collateral/redeem_fee_formula` | · | ✅ 1.2k ($0.019) | ❌ — | ✅ 1.7k ($0.029) |
| `usual/dao_collateral/redeem_return_formula` | · | ❌ 9.8k ($0.20) | ❌ — | ❌ 5.0k ($0.42) |
| `usual/dao_collateral/swap_conservation` | · | ❌ 7.2k ($0.33) | ❌ — | ❌ 12.0k ($0.59) |
| `usual/dao_collateral/swap_value_conservation` | · | ❌ 8.5k ($0.33) | ❌ — | ❌ 8.5k ($0.39) |
| `wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity` | · | ❌ 57.6k ($0.64) | ✅ — | ✅ 2.4k ($0.058) |
| `zama/erc7984_confidential_token/burn_decreases_supply` | · | ❌ 14.4k ($0.26) | ❌ — | ❌ 10.5k ($0.33) |
| `zama/erc7984_confidential_token/burn_insufficient` | · | ❌ 15.0k ($0.41) | ❌ — | ❌ 7.6k ($0.51) |
| `zama/erc7984_confidential_token/mint_ctokens_match_deposit` | · | ❌ 18.5k ($0.31) | ❌ — | ❌ 18.9k ($0.44) |
| `zama/erc7984_confidential_token/mint_increases_supply` | · | ❌ 14.2k ($0.22) | ❌ — | ❌ 7.4k ($0.29) |
| `zama/erc7984_confidential_token/mint_overflow_protection` | · | ❌ 15.4k ($0.34) | ❌ — | ❌ 11.2k ($0.38) |
| `zama/erc7984_confidential_token/setOperator_updates` | · | ✅ 2.9k ($0.043) | ❌ — | ✅ 5.3k ($0.15) |
| `zama/erc7984_confidential_token/transferFrom_conservation` | · | ❌ 8.6k ($0.22) | ❌ — | ❌ 15.6k ($0.38) |
| `zama/erc7984_confidential_token/transfer_conservation` | · | ❌ 12.5k ($0.41) | ❌ — | ❌ 16.6k ($0.60) |
| `zama/erc7984_confidential_token/transfer_insufficient` | · | ❌ 9.9k ($0.32) | ❌ — | ❌ 9.6k ($0.32) |
| `zama/erc7984_confidential_token/transfer_no_balance_revert` | · | ✅ 6.4k ($0.17) | ❌ — | ❌ 6.5k ($0.35) |
| `zama/erc7984_confidential_token/transfer_preserves_supply` | · | ❌ 10.4k ($0.24) | ❌ — | ❌ 6.0k ($0.32) |
| `zama/erc7984_confidential_token/transfer_sufficient` | · | ❌ 14.2k ($0.48) | ❌ — | ❌ 7.1k ($0.49) |
| `zodiac/roles_decoder_faithfulness/metadata_bridge` | · | ❌ 10.9k ($0.19) | ❌ — | ❌ 27.0k ($0.60) |
| `zodiac/roles_decoder_faithfulness/roles_decoder_bounds_safe` | · | ❌ 8.6k ($0.31) | ❌ — | ❌ 20.6k ($0.48) |
| `zodiac/roles_decoder_faithfulness/roles_decoder_faithful` | · | ❌ 13.6k ($0.30) | ❌ — | ❌ 15.8k ($0.45) |

Notes: completion tokens are what the model generated (the main cost driver per
provider pricing); prompt tokens show how context-hungry each harness is. Shell
harness rows have no attempt counts because iteration happens inside the CLI.
Values marked *(est.)* are estimates, not measurements: grok-cli exposes no token
telemetry at all (range derived from turn counts, run durations, and the same
model's measured usage under the builtin harness); codex reports only an
undecomposed total (cost range assumes 90-99% of tokens are prompt-side, the
typical split for coding agents).
