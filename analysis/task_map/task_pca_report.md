# Task PCA Analysis

Generated from `results/manifests/v0.1.json`.

This is a true PCA over the centered binary task-model success matrix. Missing cells are imputed with the model mean pass rate, so the current output remains provisional until the manifest is regenerated from the full backfills.

## Inputs

- models used: claude-opus-4-8, kimi/kimi-for-coding, minimax/minimax-m3, openai-gpt-55, spark/step3p7-flash-148b, zai/glm-5.2
- tasks projected: 135
- PC1 explained variance: 65.1%
- PC2 explained variance: 13.4%

## Axis Interpretation

- PC1 is the broad solvability axis: easy local properties separate from tasks that nearly every model fails.
- PC2 is the specialization axis: it separates tasks solved by different subsets of the stronger models.
- The model arrows in `task_pca.svg` show which model success vectors define each direction.

## Empirical Families

- `hard_state_invariant`: 80 tasks
- `mostly_solved_local_transition`: 24 tasks
- `divisive_authorization_or_accounting`: 18 tasks
- `single_model_solvable_boundary`: 12 tasks
- `simple_bound_regression`: 1 tasks

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

- `FFFF`: 80 tasks
- `PPFP`: 24 tasks
- `FPFP`: 13 tasks
- `FFFP`: 10 tasks
- `PFFP`: 5 tasks
- `PFFF`: 1 tasks
- `PFPP`: 1 tasks
- `FPFF`: 1 tasks

## Model Loadings

- `claude-opus-4-8`: pc1=-0.322, pc2=-0.736, mean_pass=43.2%, coverage=88
- `kimi/kimi-for-coding`: pc1=-0.402, pc2=0.586, mean_pass=23.0%, coverage=135
- `minimax/minimax-m3`: pc1=-0.494, pc2=0.185, mean_pass=28.1%, coverage=135
- `openai-gpt-55`: pc1=-0.393, pc2=-0.280, mean_pass=62.4%, coverage=93
- `zai/glm-5.2`: pc1=-0.579, pc2=0.035, mean_pass=39.3%, coverage=135
- `spark/step3p7-flash-148b`: pc1=-0.006, pc2=0.026, mean_pass=0.7%, coverage=135

## Recommendation

Use empirical families as the seed for the stable taxonomy, but do not make PCA clusters the permanent taxonomy directly. The clean schema is `stable_family` for the semantic category, `property_class` for the precise proof obligation, and `empirical_family` plus PCA coordinates for measured behavior. In future benchmark versions, merge stable families that remain behaviorally indistinguishable and split families that consistently form separate PCA/heatmap neighborhoods.
