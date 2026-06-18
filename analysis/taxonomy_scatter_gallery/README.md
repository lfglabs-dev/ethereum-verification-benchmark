# Taxonomy Scatter Gallery

## Recommended Stable Categories

### state_preservation_and_local_effects

- tasks: 47
- avg_pass_rate: 0.148
- needs_review: 6
- property_classes: storage_write (6), reserve_state_transition (4), arithmetic_rounding (3), compliance_boundary (3), lifecycle_accounting (3), linked_list_acyclicity (3)
- empirical_families: hard_state_invariant (33), mostly_solved_local_transition (11), divisive_authorization_or_accounting (2), single_model_solvable_boundary (1)
- examples: balancer/reclamm_swap_rounding/on_swap_fixed_virtual_balances_product_non_decreasing, damn_vulnerable_defi/side_entrance/deposit_sets_pool_balance, damn_vulnerable_defi/side_entrance/deposit_sets_sender_credit, ethereum/deposit_contract_minimal/deposit_count, ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free, ipor/plasma_vault_redeem_split/redeem_preserves_pps

### asset_accounting_and_conservation

- tasks: 37
- avg_pass_rate: 0.155
- needs_review: 6
- property_classes: accounting_bound (16), accounting_conservation (15), accounting_update (6)
- empirical_families: hard_state_invariant (30), single_model_solvable_boundary (3), mostly_solved_local_transition (2), divisive_authorization_or_accounting (1)
- examples: alchemix/earmark_conservation/earmark_preserves_invariant, alchemix/earmark_conservation/redeem_preserves_invariant, alchemix/earmark_conservation/sub_debt_preserves_invariant, alchemix/earmark_conservation/sub_earmarked_debt_preserves_invariant, alchemix/earmark_conservation/sync_account_preserves_invariant, cork/pool_solvency/solvency_preserved

### authorization_and_caller_integrity

- tasks: 19
- avg_pass_rate: 0.549
- needs_review: 8
- property_classes: access_control_identity (10), authorization_state (9)
- empirical_families: divisive_authorization_or_accounting (7), mostly_solved_local_transition (6), hard_state_invariant (4), single_model_solvable_boundary (2)
- examples: onedelta/caller_address_integrity/delta_compose_internal_erc20_transfer_from_uses_outer_caller, onedelta/caller_address_integrity/delta_compose_internal_permit2_transfer_from_uses_outer_caller, onedelta/caller_address_integrity/direct_erc20_transfer_from_uses_outer_caller, onedelta/caller_address_integrity/direct_permit2_transfer_from_uses_outer_caller, onedelta/caller_address_integrity/flash_callback_erc20_transfer_from_uses_outer_caller, onedelta/caller_address_integrity/nested_flash_and_swap_callbacks_keep_outer_caller

### structural_indexing_invariants

- tasks: 11
- avg_pass_rate: 0.156
- needs_review: 2
- property_classes: linked_list_invariant (8), threshold_partition (1), mapping_consistency (1), tree_conservation (1)
- empirical_families: hard_state_invariant (8), divisive_authorization_or_accounting (2), single_model_solvable_boundary (1)
- examples: ethereum/deposit_contract_minimal/small_deposit_preserves_full_count, kleros/sortition_trees/node_id_bijection, kleros/sortition_trees/parent_equals_sum_of_children, safe/owner_manager_reach/add_owner_owner_list_invariant, safe/owner_manager_reach/in_list_reachable, safe/owner_manager_reach/remove_owner_in_list_reachable

### numeric_bounds_and_pricing

- tasks: 9
- avg_pass_rate: 0.508
- needs_review: 4
- property_classes: price_computation (5), output_range (2), price_band (2)
- empirical_families: single_model_solvable_boundary (3), mostly_solved_local_transition (3), divisive_authorization_or_accounting (2), hard_state_invariant (1)
- examples: kleros/sortition_trees/draw_selects_valid_leaf, nexus_mutual/ramm_price_band/sync_sets_book_value, nexus_mutual/ramm_price_band/sync_sets_buy_price, nexus_mutual/ramm_price_band/sync_sets_sell_price, openzeppelin/erc4626_virtual_offset_deposit/positive_deposit_mints_positive_shares_under_rate_bound, reserve/auction_price_band/price_at_end_time

### solvency_and_liquidity_guards

- tasks: 7
- avg_pass_rate: 0.612
- needs_review: 4
- property_classes: guarded_solvency (7)
- empirical_families: mostly_solved_local_transition (3), single_model_solvable_boundary (2), divisive_authorization_or_accounting (2)
- examples: forgeyields/global_solvency/claim_redeem_preserves_global_solvency, forgeyields/global_solvency/deposit_preserves_global_solvency, forgeyields/global_solvency/handle_preserves_global_solvency, forgeyields/global_solvency/redeem_token_gateway_depreciated_preserves_global_solvency, forgeyields/global_solvency/report_preserves_global_solvency, forgeyields/global_solvency/request_redeem_preserves_global_solvency

### decoder_and_refinement_equivalence

- tasks: 6
- avg_pass_rate: 0.171
- needs_review: 0
- property_classes: exploit_trace (1), total_conservation (1), subtree_partition (1), noninterference (1), calldata_decoder_metadata (1), calldata_decoder_faithfulness (1)
- empirical_families: hard_state_invariant (5), mostly_solved_local_transition (1)
- examples: damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool, kleros/sortition_trees/root_equals_sum_of_leaves, kleros/sortition_trees/root_minus_left_equals_right_subtree, paladin_votes/stream_recovery_claim_usdc/both_matches_independent_claims, zodiac/roles_decoder_faithfulness/metadata_bridge, zodiac/roles_decoder_faithfulness/roles_decoder_faithful

### protocol_transition_correctness

- tasks: 5
- avg_pass_rate: 0.457
- needs_review: 1
- property_classes: balance_credit_update (1), threshold_activation (1), monotonic_counter (1), linked_list_acyclicity (1), reserve_state_transition (1)
- empirical_families: mostly_solved_local_transition (2), hard_state_invariant (2), divisive_authorization_or_accounting (1)
- examples: damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_sets_sender_credit, ethereum/deposit_contract_minimal/chain_start_threshold, ethereum/deposit_contract_minimal/full_deposit_increments_full_count, safe/owner_manager_reach/setup_owners_acyclicity, termmax/order_v2_buy_xt_single_segment/swap_debt_token_to_xt_updates_virtual_xt_reserve

### negative_and_attack_boundaries

- tasks: 2
- avg_pass_rate: 0.482
- needs_review: 1
- property_classes: accounting_invariant_break (1), non_leakage (1)
- empirical_families: divisive_authorization_or_accounting (1), single_model_solvable_boundary (1)
- examples: damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance, zama/erc7984_confidential_token/transfer_no_balance_revert

## Plots

- `01_pca_by_stable_family.svg`: PCA des tâches par famille stable - Point=tâche, taille=log tokens moyens; PC1≈difficulté, PC2≈spécialisation
- `02_pca_by_empirical_family.svg`: PCA par famille empirique - Point=tâche, taille=pass-rate; montre les clusters issus des runs
- `03_pca_by_property_class.svg`: PCA par property_class - Point=tâche; catégories de preuve précises projetées sur le comportement modèle
- `04_pca_by_review_status.svg`: PCA et revue humaine - Diamant=tâche à revue; utile pour voir les zones taxonomiques incertaines
- `05_mds_by_mds_cluster.svg`: Carte MDS par cluster comportemental - Reprise de la carte pass/fail coverage-aware avec couleurs de clusters
- `06_mds_by_stable_family.svg`: Carte MDS par famille stable - Compare les familles sémantiques aux voisinages comportementaux
- `07_pass_rate_vs_tokens_stable.svg`: Pass-rate vs tokens par famille stable - Les tâches chères mais non résolues ressortent en haut à gauche
- `08_cohort_pass_rate_vs_tokens_empirical.svg`: Cohort pass-rate vs tokens par famille empirique - Vue centrée sur la cohorte de modèles comparables
- `09_pc1_vs_tokens_stable.svg`: PC1 vs tokens - PC1 mesure surtout la solvabilité; les tokens indiquent l'effort historique
- `10_pc2_vs_divisiveness_empirical.svg`: PC2 vs divisiveness - Met en évidence les tâches qui séparent les modèles
- `11_confidence_vs_pass_rate_stable.svg`: Confiance taxonomique vs pass-rate - Cherche les familles stables peu résolues mais bien identifiées
- `12_confidence_vs_tokens_review.svg`: Confiance vs tokens et revue - Priorise la revue humaine: basse confiance + haut coût
- `13_skill_count_vs_pass_rate_stable.svg`: Nombre de skills de preuve vs pass-rate - Complexité de preuve estimée contre succès historique
- `14_spec_signal_count_vs_pass_rate_stable.svg`: Signaux de spec vs pass-rate - Les specs riches ne sont pas forcément faciles
- `15_neighbors_vs_confidence_stable.svg`: Voisins taxonomiques vs confiance - Contrôle que les placements par similarité ont assez de voisins
- `16_resolved_vs_pca_stable.svg`: Tâches résolues et non résolues sur PCA - Forme=résolution historique; couleur=famille stable
- `17_task_model_tokens_vs_pc1_model.svg`: Tâche-modèle: tokens vs PC1 - Point=paire tâche-modèle; triangle=pass, cercle=fail
- `18_task_model_pca_by_model.svg`: Tâche-modèle sur PCA par modèle - Point=paire tâche-modèle; triangle=pass; montre les zones couvertes par chaque modèle
- `19_task_model_pass_vs_tokens.svg`: Tâche-modèle: pass/fail vs tokens - Chaque point est une tentative modèle; utile pour voir l'effort dépensé avant succès
- `20_family_centroids_pca.svg`: Centres de familles stables sur PCA - Point=tâche, ellipse=extension approximative, label=centroïde de famille