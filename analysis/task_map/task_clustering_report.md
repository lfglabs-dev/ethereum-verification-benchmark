# Task Clustering Analysis

Generated from `results/manifests/v0.1.json`.

## Recommended Approach

Use a two-layer categorization:

1. Keep the human taxonomy (`proof_family`, `property_class`, skills) as the canonical explanation layer.
2. Add behavior-derived clusters from the task-model pass/fail matrix as the empirical layer.

The best default visualization is the SVG task map plus the clustered heatmap. The map is good for discovering axes; the heatmap is better for auditing whether the clusters are real.

For current v0.1 data, the most stable empirical cluster key is the cohort signature derived from the full-coverage cohort in `analysis/task_features.json`. It is tied to that comparison cohort, so it should be shown as a behavior profile, not as a permanent taxonomy.

## Axis Interpretation

- Axis 1 explains 85.4% of the two-axis embedding signal and mostly tracks global task difficulty.
- Axis 2 explains 14.6% of the two-axis embedding signal and mostly tracks model-specialization differences.
- Dot size is failure rate; color is `property_class`; tooltips carry task, cluster, attempts, and pass rate.

## Coverage Caveat

High-coverage models in this manifest: claude-opus-4-8, kimi/kimi-for-coding, minimax/minimax-m3, openai-gpt-55, spark/step3p7-flash-148b, zai/glm-5.2.
Low-coverage models are retained but distances are coverage-penalized: deepseek-v4-flash, deepseek-v4-pro, grok, openai-gpt-55-pro, virtuals/deepseek-v4-flash, virtuals/deepseek-v4-pro, virtuals/xiaomi-mimo-v2-5, xai/grok-4.3, xiaomi-mimo-v2-5.
When the backfilled full-result manifest is regenerated, rerun this script; the cluster assignments should be treated as provisional until then.

## Cohort Signatures

The full-coverage cohort signature is the cleanest behavior-derived category today:

- `FFFF`: 80 tasks, cohort-universal hard
- `PPFP`: 24 tasks, mostly solved, one-model gap
- `FPFP`: 13 tasks, divisive 2-of-4
- `FFFP`: 10 tasks, single-model solvable
- `PFFP`: 5 tasks, divisive 2-of-4
- `PFFF`: 1 tasks, single-model solvable
- `PFPP`: 1 tasks, mostly solved, one-model gap
- `FPFF`: 1 tasks, single-model solvable

## Cluster Summaries

### Cluster 1

- tasks: 80
- average pass rate: 2.4%
- average observed models: 5.6
- dominant property classes: accounting_conservation (14), accounting_bound (9), linked_list_invariant (8)
- dominant proof families: state_preservation_local_effects (34), functional_correctness (21), refinement_equivalence (9)
- dominant cohort signatures: FFFF (80)
- examples: `zodiac/roles_decoder_faithfulness/roles_decoder_faithful, zodiac/roles_decoder_faithfulness/roles_decoder_bounds_safe, zodiac/roles_decoder_faithfulness/metadata_bridge`

### Cluster 2

- tasks: 24
- average pass rate: 78.7%
- average observed models: 6.5
- dominant property classes: access_control_identity (4), guarded_solvency (3), price_computation (3)
- dominant proof families: state_preservation_local_effects (7), authorization_enablement (6), protocol_transition_correctness (5)
- dominant cohort signatures: PPFP (24)
- examples: `paladin_votes/stream_recovery_claim_usdc/weth_preserves_usdc_state, paladin_votes/stream_recovery_claim_usdc/weth_double_claim_rejected, paladin_votes/stream_recovery_claim_usdc/usdc_preserves_weth_state`

### Cluster 3

- tasks: 13
- average pass rate: 65.0%
- average observed models: 6.5
- dominant property classes: access_control_identity (4), price_computation (2), accounting_invariant_break (1)
- dominant proof families: authorization_enablement (6), protocol_transition_correctness (3), functional_correctness (3)
- dominant cohort signatures: FPFP (13)
- examples: `zama/erc7984_confidential_token/setOperator_updates, piku/fund_conservation/amount_paid_records_distribution, paladin_votes/stream_recovery_claim_usdc/claim_marks_user`

### Cluster 4

- tasks: 10
- average pass rate: 44.5%
- average observed models: 6.5
- dominant property classes: guarded_solvency (2), accounting_update (2), monotonic_counter (1)
- dominant proof families: protocol_transition_correctness (4), state_preservation_local_effects (2), functional_correctness (2)
- dominant cohort signatures: FFFP (10)
- examples: `paladin_votes/stream_recovery_claim_usdc/weth_no_overclaim, reserve/auction_price_band/price_lower_bound, kleros/sortition_trees/parent_equals_sum_of_children`

### Cluster 5

- tasks: 3
- average pass rate: 42.1%
- average observed models: 6.3
- dominant property classes: authorization_state (2), guarded_solvency (1)
- dominant proof families: authorization_enablement (2), protocol_transition_correctness (1)
- dominant cohort signatures: PFFP (2), PFFF (1)
- examples: `paladin_votes/stream_recovery_claim_usdc/both_usdc_double_claim_rejected, forgeyields/global_solvency/handle_preserves_global_solvency, paladin_votes/stream_recovery_claim_usdc/weth_claim_marks_user`

### Cluster 6

- tasks: 3
- average pass rate: 66.7%
- average observed models: 7.0
- dominant property classes: threshold_partition (1), mapping_consistency (1), access_control_identity (1)
- dominant proof families: state_preservation_local_effects (2), authorization_enablement (1)
- dominant cohort signatures: PFFP (3)
- examples: `ethereum/deposit_contract_minimal/small_deposit_preserves_full_count, onedelta/caller_address_integrity/delta_compose_internal_erc20_transfer_from_uses_outer_caller, kleros/sortition_trees/node_id_bijection`

### Cluster 7

- tasks: 1
- average pass rate: 25.0%
- average observed models: 4.0
- dominant property classes: non_leakage (1)
- dominant proof families: protocol_transition_correctness (1)
- dominant cohort signatures: FPFF (1)
- examples: `zama/erc7984_confidential_token/transfer_no_balance_revert`

### Cluster 8

- tasks: 1
- average pass rate: 75.0%
- average observed models: 4.0
- dominant property classes: accounting_bound (1)
- dominant proof families: functional_correctness (1)
- dominant cohort signatures: PFPP (1)
- examples: `wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity`

## Method Comparison

- PCA/SVD on the raw binary matrix is useful for a quick biplot, but it handles missing coverage poorly unless imputed.
- Coverage-aware MDS over pairwise task distances is a better first artifact for the current partial manifest.
- Hierarchical clustering plus a heatmap is the best audit view because it shows the exact pass/fail pattern behind each cluster.
- UMAP/t-SNE may reveal visual neighborhoods, but should not define canonical categories because the axes are unstable and hard to explain.
- Multidimensional IRT is the cleanest later statistical model once all selected models have full coverage; it can separate model ability from task difficulty and latent skill axes.

## Website Data Model

Expose `analysis/task_map/task_map.json` for the website. It contains task coordinates, clusters, pass rates, taxonomy labels, model coverage, and cluster summaries. Keep `results/summaries/v0.1.json` as the leaderboard input and `results/manifests/v0.1.json` as the full audit input.
