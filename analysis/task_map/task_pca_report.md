# Task PCA Analysis

Generated from `results/manifests/v0.1.json`.

This is a true PCA over the centered binary task-model success matrix. Missing cells are imputed with the model mean pass rate, so the current output remains provisional until the manifest is regenerated from the full backfills.

## Inputs

- models used: claude-opus-4-8, grok, kimi/kimi-for-coding, minimax/minimax-m3, mistralai/Leanstral-2603, openai-gpt-55, virtuals/deepseek-v4-flash, virtuals/deepseek-v4-pro, virtuals/xiaomi-mimo-v2-5, xai/grok-4.3, zai/glm-5.2
- tasks projected: 135
- PC1 explained variance: 62.4%
- PC2 explained variance: 7.7%

## Axis Interpretation

- PC1 is the broad solvability axis: easy local properties separate from tasks that nearly every model fails.
- PC2 is the specialization axis: it separates tasks solved by different subsets of the stronger models.
- The model arrows in `task_pca.svg` show which model success vectors define each direction.

## Empirical Families

- `hard_state_invariant`: 83 tasks
- `mostly_solved_local_transition`: 31 tasks
- `mixed_empirical_profile`: 21 tasks

## Proposed Stable Semantic Families

- `state_preservation_and_local_effects`: 43 tasks
- `asset_accounting_and_conservation`: 34 tasks
- `authorization_and_caller_integrity`: 19 tasks
- `structural_indexing_invariants`: 11 tasks
- `numeric_bounds_and_pricing`: 8 tasks
- `solvency_and_liquidity_guards`: 7 tasks
- `decoder_and_refinement_equivalence`: 6 tasks
- `protocol_transition_correctness`: 5 tasks
- `negative_and_attack_boundaries`: 2 tasks

## Cohort Signatures

- `FFFFFFFFFF`: 63 tasks
- `FFFFFPFFFF`: 11 tasks
- `PFFFFPFFFP`: 3 tasks
- `FPPPFPFFFP`: 3 tasks
- `PFFFFFFFFF`: 3 tasks
- `PPFPFPPFFP`: 3 tasks
- `PPPPFPPFFP`: 3 tasks
- `PPPPFPPFPP`: 3 tasks
- `PPPPPPPFPP`: 2 tasks
- `FPPPFPFFPP`: 2 tasks
- `PPPPPPPPPP`: 2 tasks
- `PPPPFPPPPP`: 2 tasks
- `PPPPPPPFFP`: 1 tasks
- `PPFPFPPPPP`: 1 tasks
- `PFPPFPPPPP`: 1 tasks
- `PPFPFPFPPP`: 1 tasks
- `PPPPFPFPFP`: 1 tasks
- `PPPFFFFFFP`: 1 tasks
- `FPFFFPFFFP`: 1 tasks
- `FFPFFPFPFP`: 1 tasks
- `PPFPFPFFFP`: 1 tasks
- `PFFFFPFFPP`: 1 tasks
- `FPFFFPFFPP`: 1 tasks
- `PPPFFPPFFP`: 1 tasks
- `PFFFFPPFFP`: 1 tasks
- `PFPPFPPFPP`: 1 tasks
- `PFPPPPPPPP`: 1 tasks
- `PPFPFPPFPP`: 1 tasks
- `PPPFFPPFPP`: 1 tasks
- `PFFPFPFPPP`: 1 tasks
- `PPPPFPFFPP`: 1 tasks
- `PPFPPPPFFP`: 1 tasks
- `PPFFFPPFPP`: 1 tasks
- `PPFPFPPPFP`: 1 tasks
- `FFPFFPFFFF`: 1 tasks
- `PFFFFPFFFF`: 1 tasks
- `FFFPFPFFFP`: 1 tasks
- `PFFPFPFFFP`: 1 tasks
- `FFPFFPFFFP`: 1 tasks
- `FFFFFPFFFP`: 1 tasks
- `FPPPFPPFFP`: 1 tasks
- `FPFPFPFFFP`: 1 tasks
- `PPFFPPPFPP`: 1 tasks
- `FPFFFPFFFF`: 1 tasks
- `PPPFPPPPPP`: 1 tasks
- `FPFFFFFFFF`: 1 tasks
- `PFFPFFFFFF`: 1 tasks

## Model Loadings

- `openai-gpt-55`: pc1=-0.364, pc2=0.515, mean_pass=48.9%, coverage=135
- `claude-opus-4-8`: pc1=-0.346, pc2=-0.388, mean_pass=33.3%, coverage=135
- `virtuals/deepseek-v4-pro`: pc1=-0.281, pc2=-0.390, mean_pass=22.2%, coverage=126
- `zai/glm-5.2`: pc1=-0.408, pc2=0.253, mean_pass=39.3%, coverage=135
- `virtuals/deepseek-v4-flash`: pc1=-0.313, pc2=-0.342, mean_pass=22.2%, coverage=135
- `grok`: pc1=-0.347, pc2=0.197, mean_pass=30.4%, coverage=135
- `kimi/kimi-for-coding`: pc1=-0.276, pc2=0.220, mean_pass=23.0%, coverage=135
- `xai/grok-4.3`: pc1=-0.251, pc2=-0.240, mean_pass=18.5%, coverage=135
- `minimax/minimax-m3`: pc1=-0.340, pc2=0.125, mean_pass=28.1%, coverage=135
- `virtuals/xiaomi-mimo-v2-5`: pc1=-0.135, pc2=-0.205, mean_pass=9.6%, coverage=135
- `mistralai/Leanstral-2603`: pc1=-0.106, pc2=-0.220, mean_pass=6.7%, coverage=135

## Recommendation

Use empirical families as the seed for the stable taxonomy, but do not make PCA clusters the permanent taxonomy directly. The clean schema is `stable_family` for the semantic category, `property_class` for the precise proof obligation, and `empirical_family` plus PCA coordinates for measured behavior. In future benchmark versions, merge stable families that remain behaviorally indistinguishable and split families that consistently form separate PCA/heatmap neighborhoods.
