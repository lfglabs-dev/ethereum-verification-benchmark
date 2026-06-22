# Task Clustering Analysis

Generated from `results/manifests/v0.1.json`.

## Recommended Approach

Use a two-layer categorization:

1. Keep the human taxonomy (`proof_family`, `property_class`, skills) as the canonical explanation layer.
2. Add behavior-derived clusters from the task-model pass/fail matrix as the empirical layer.

The best default visualization is the SVG task map plus the clustered heatmap. The map is good for discovering axes; the heatmap is better for auditing whether the clusters are real.

For current v0.1 data, the most stable empirical cluster key is the cohort signature derived from the full-coverage cohort in `analysis/task_features.json`. It is tied to that comparison cohort, so it should be shown as a behavior profile, not as a permanent taxonomy.

## Axis Interpretation

- Axis 1 explains 92.1% of the two-axis embedding signal and mostly tracks global task difficulty.
- Axis 2 explains 7.9% of the two-axis embedding signal and mostly tracks model-specialization differences.
- Dot size is failure rate; color is `property_class`; tooltips carry task, cluster, attempts, and pass rate.

## Coverage Caveat

High-coverage models in this manifest: claude-opus-4-8, grok, kimi/kimi-for-coding, minimax/minimax-m3, mistralai/Leanstral-2603, openai-gpt-55, virtuals/deepseek-v4-flash, virtuals/deepseek-v4-pro, virtuals/xiaomi-mimo-v2-5, xai/grok-4.3, zai/glm-5.2.
Low-coverage models are retained but distances are coverage-penalized: openai-gpt-55-pro.
When the backfilled full-result manifest is regenerated, rerun this script; the cluster assignments should be treated as provisional until then.

## Cohort Signatures

The full-coverage cohort signature is the cleanest behavior-derived category today:

- `FFFFFFFFFF`: 63 tasks, cohort-universal hard
- `FFFFFPFFFF`: 11 tasks, single-model solvable
- `PFFFFPFFFP`: 3 tasks, mixed profile
- `FPPPFPFFFP`: 3 tasks, mixed profile
- `PFFFFFFFFF`: 3 tasks, single-model solvable
- `PPFPFPPFFP`: 3 tasks, mixed profile
- `PPPPFPPFFP`: 3 tasks, mixed profile
- `PPPPFPPFPP`: 3 tasks, mixed profile
- `PPPPPPPFPP`: 2 tasks, mostly solved, one-model gap
- `FPPPFPFFPP`: 2 tasks, mixed profile
- `PPPPPPPPPP`: 2 tasks, cohort-universal solved
- `PPPPFPPPPP`: 2 tasks, mostly solved, one-model gap
- `PPPPPPPFFP`: 1 tasks, mixed profile
- `PPFPFPPPPP`: 1 tasks, mixed profile
- `PFPPFPPPPP`: 1 tasks, mixed profile
- `PPFPFPFPPP`: 1 tasks, mixed profile
- `PPPPFPFPFP`: 1 tasks, mixed profile
- `PPPFFFFFFP`: 1 tasks, mixed profile
- `FPFFFPFFFP`: 1 tasks, mixed profile
- `FFPFFPFPFP`: 1 tasks, mixed profile
- `PPFPFPFFFP`: 1 tasks, mixed profile
- `PFFFFPFFPP`: 1 tasks, mixed profile
- `FPFFFPFFPP`: 1 tasks, mixed profile
- `PPPFFPPFFP`: 1 tasks, mixed profile
- `PFFFFPPFFP`: 1 tasks, mixed profile
- `PFPPFPPFPP`: 1 tasks, mixed profile
- `PFPPPPPPPP`: 1 tasks, mostly solved, one-model gap
- `PPFPFPPFPP`: 1 tasks, mixed profile
- `PPPFFPPFPP`: 1 tasks, mixed profile
- `PFFPFPFPPP`: 1 tasks, mixed profile
- `PPPPFPFFPP`: 1 tasks, mixed profile
- `PPFPPPPFFP`: 1 tasks, mixed profile
- `PPFFFPPFPP`: 1 tasks, mixed profile
- `PPFPFPPPFP`: 1 tasks, mixed profile
- `FFPFFPFFFF`: 1 tasks, divisive 2-of-4
- `PFFFFPFFFF`: 1 tasks, divisive 2-of-4
- `FFFPFPFFFP`: 1 tasks, mixed profile
- `PFFPFPFFFP`: 1 tasks, mixed profile
- `FFPFFPFFFP`: 1 tasks, mixed profile
- `FFFFFPFFFP`: 1 tasks, divisive 2-of-4
- `FPPPFPPFFP`: 1 tasks, mixed profile
- `FPFPFPFFFP`: 1 tasks, mixed profile
- `PPFFPPPFPP`: 1 tasks, mixed profile
- `FPFFFPFFFF`: 1 tasks, divisive 2-of-4
- `PPPFPPPPPP`: 1 tasks, mostly solved, one-model gap
- `FPFFFFFFFF`: 1 tasks, single-model solvable
- `PFFPFFFFFF`: 1 tasks, divisive 2-of-4

## Cluster Summaries

### Cluster 1

- tasks: 83
- average pass rate: 2.9%
- average observed models: 11.1
- dominant property classes: accounting_conservation (14), accounting_bound (10), linked_list_invariant (8)
- dominant proof families: state_preservation_local_effects (34), functional_correctness (21), authorization_enablement (10)
- dominant cohort signatures: FFFFFFFFFF (63), FFFFFPFFFF (11), PFFFFFFFFF (3)
- examples: `zodiac/roles_decoder_faithfulness/roles_decoder_faithful, zodiac/roles_decoder_faithfulness/roles_decoder_bounds_safe, zodiac/roles_decoder_faithfulness/metadata_bridge`

### Cluster 2

- tasks: 15
- average pass rate: 70.8%
- average observed models: 11.9
- dominant property classes: access_control_identity (8), price_computation (3), storage_update (1)
- dominant proof families: authorization_enablement (8), functional_correctness (4), state_preservation_local_effects (2)
- dominant cohort signatures: PPFPFPPFFP (3), PPPPFPPFFP (3), PPPPPPPFFP (1)
- examples: `zama/erc7984_confidential_token/setOperator_updates, forgeyields/global_solvency/redeem_token_gateway_depreciated_preserves_global_solvency, onedelta/caller_address_integrity/transfers_permit2_transfer_from_uses_outer_caller`

### Cluster 3

- tasks: 13
- average pass rate: 86.4%
- average observed models: 11.8
- dominant property classes: accounting_bound (3), balance_credit_update (2), accounting_invariant_break (1)
- dominant proof families: state_preservation_local_effects (4), protocol_transition_correctness (4), functional_correctness (3)
- dominant cohort signatures: PPPPPPPFPP (2), PPPPPPPPPP (2), PPPPFPPPPP (2)
- examples: `onedelta/caller_address_integrity/delta_compose_internal_permit2_transfer_from_uses_outer_caller, kleros/sortition_trees/root_equals_sum_of_leaves, ethereum/deposit_contract_minimal/chain_start_threshold`

### Cluster 4

- tasks: 10
- average pass rate: 56.1%
- average observed models: 11.4
- dominant property classes: guarded_solvency (2), authorization_state (2), frame_property (2)
- dominant proof families: authorization_enablement (3), state_preservation_local_effects (3), protocol_transition_correctness (2)
- dominant cohort signatures: FPPPFPFFFP (3), FPPPFPFFPP (2), PPPPFPPFPP (2)
- examples: `piku/fund_conservation/amount_paid_records_distribution, kleros/sortition_trees/draw_interval_matches_weights, paladin_votes/stream_recovery_claim_usdc/usdc_preserves_weth_state`

### Cluster 5

- tasks: 9
- average pass rate: 33.8%
- average observed models: 11.4
- dominant property classes: guarded_solvency (2), authorization_state (2), accounting_update (2)
- dominant proof families: protocol_transition_correctness (4), authorization_enablement (3), state_preservation_local_effects (2)
- dominant cohort signatures: PFFFFPFFFP (3), FFPFFPFPFP (1), PFFFFPFFPP (1)
- examples: `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_round_claimed, paladin_votes/stream_recovery_claim_usdc/weth_claim_marks_user, paladin_votes/stream_recovery_claim_usdc/claim_updates_total_allocated`

### Cluster 6

- tasks: 2
- average pass rate: 37.5%
- average observed models: 12.0
- dominant property classes: guarded_solvency (1), output_range (1)
- dominant proof families: protocol_transition_correctness (1), functional_correctness (1)
- dominant cohort signatures: FPFFFPFFFP (1), FPFFFPFFPP (1)
- examples: `kleros/sortition_trees/draw_selects_valid_leaf, forgeyields/global_solvency/claim_redeem_preserves_global_solvency`

### Cluster 7

- tasks: 2
- average pass rate: 54.2%
- average observed models: 12.0
- dominant property classes: monotonic_counter (1), threshold_partition (1)
- dominant proof families: protocol_transition_correctness (1), state_preservation_local_effects (1)
- dominant cohort signatures: PPPPFPFPFP (1), PPPFFFFFFP (1)
- examples: `ethereum/deposit_contract_minimal/small_deposit_preserves_full_count, ethereum/deposit_contract_minimal/full_deposit_increments_full_count`

### Cluster 8

- tasks: 1
- average pass rate: 63.6%
- average observed models: 11.0
- dominant property classes: price_band (1)
- dominant proof families: functional_correctness (1)
- dominant cohort signatures: PPFFPPPFPP (1)
- examples: `reserve/auction_price_band/price_lower_bound`

## Method Comparison

- PCA/SVD on the raw binary matrix is useful for a quick biplot, but it handles missing coverage poorly unless imputed.
- Coverage-aware MDS over pairwise task distances is a better first artifact for the current partial manifest.
- Hierarchical clustering plus a heatmap is the best audit view because it shows the exact pass/fail pattern behind each cluster.
- UMAP/t-SNE may reveal visual neighborhoods, but should not define canonical categories because the axes are unstable and hard to explain.
- Multidimensional IRT is the cleanest later statistical model once all selected models have full coverage; it can separate model ability from task difficulty and latent skill axes.

## Website Data Model

Expose `analysis/task_map/task_map.json` for the website. It contains task coordinates, clusters, pass rates, taxonomy labels, model coverage, and cluster summaries. Keep `results/summaries/v0.1.json` as the leaderboard input and `results/manifests/v0.1.json` as the full audit input.
