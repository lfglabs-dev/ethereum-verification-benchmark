# Benchmark report

This report is generated from the benchmark manifests.

## Summary

- Families: 16
- Implementations: 16
- Active cases: 12
- Buildable active cases: 12
- Active tasks: 85
- Backlog cases: 4

## Buildable active cases

### `alchemix/earmark_conservation`
- Family / implementation: `alchemix` / `v3`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Alchemix.EarmarkConservation.Compile`
- Source ref: `https://github.com/alchemix-finance/v3@117c95b6ee11a75221d6fbdc79f16ac6acdb96f5:src/AlchemistV3.sol`
- Selected functions: `_earmark`, `_sync`, `_computeUnrealizedAccount`, `redeem`, `_subEarmarkedDebt`, `_subDebt`
- Source artifact: `src/AlchemistV3.sol`
- Notes: Earmark conservation invariant for Alchemix V3 lazy-accrual debt accounting. The literal "sum of stored account.earmarked equals cumulativeEarmarked" is provably false on the deployed code (see AlchemistV3.sol:1014 comment "Global can lag local by rounding") because per-account earmarked is updated lazily inside _sync(tokenId). The lazy-projected version proven here is the property the design actually maintains and that downstream consumers (redemption math, collateral debit) rely on.

### `cork/pool_solvency`
- Family / implementation: `cork` / `phoenix`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Cork.PoolSolvency.Compile`
- Source ref: `https://github.com/Cork-Technology/phoenix@40d9b173c4b:contracts/libraries/PoolLib.sol`
- Selected functions: `previewUnwindExerciseOther`, `_unwindExercise`
- Source artifact: `contracts/libraries/PoolLib.sol`
- Notes: Cork Phoenix pool solvency slice targeting the Certora P-02 gap. Based on the Certora formal verification report (September-December 2025). P-02 was verified for all functions except unwindExerciseOther (timeout).

### `damn_vulnerable_defi/side_entrance`
- Family / implementation: `damn_vulnerable_defi` / `v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Compile`
- Source ref: `https://github.com/OpenZeppelin/damn-vulnerable-defi@6797353c7cb5409e3d388e9e8f13954f9bb5f609:contracts/side-entrance/SideEntranceLenderPool.sol`
- Selected functions: `deposit`, `flashLoan`, `withdraw`
- Source artifact: `contracts/side-entrance/SideEntranceLenderPool.sol`
- Notes: Compact Side Entrance benchmark focused on the broken coherence between pool assets and withdrawable credit when flash-loan repayment is routed through the deposit path.

### `ethereum/deposit_contract_minimal`
- Family / implementation: `ethereum` / `deposit_contract`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Ethereum.DepositContractMinimal.Compile`
- Source ref: `https://github.com/ethereum/deposit_contract@691feb18330d3d102b5a4b3d4434fac7571f51b8:deposit_contract/contracts/validator_registration.v.py`
- Selected functions: `deposit`
- Source artifact: `deposit_contract/contracts/validator_registration.v.py`
- Notes: Counter-oriented slice of the deposit path. Merkle tree, SSZ hashing, and log emission are omitted so the benchmark can focus on threshold-driven state updates.

### `kleros/sortition_trees`
- Family / implementation: `kleros` / `kleros_v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Kleros.SortitionTrees.Compile`
- Source ref: `https://github.com/kleros/kleros-v2@75125dfa54eee723cac239f20e5746d15786196b:contracts/src/libraries/SortitionTrees.sol`
- Selected functions: `set`, `updateParents`, `draw`
- Source artifact: `contracts/src/libraries/SortitionTrees.sol`
- Notes: Sortition-tree slice focused on additive parent invariants, root conservation, interval-based draws, and ID/index correspondence.

### `lido/vaulthub_locked`
- Family / implementation: `lido` / `core`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Lido.VaulthubLocked.Compile`
- Source ref: `https://github.com/lidofinance/core@96738395ca3bffd6513700a45d4c9389662c5835:contracts/0.8.25/vaults/VaultHub.sol`
- Selected functions: `_locked`, `getPooledEthBySharesRoundUp`
- Source artifact: `contracts/0.8.25/vaults/VaultHub.sol`
- Notes: Locked-amount arithmetic slice of Lido VaultHub (V3 vaults branch). Based on the Certora formal verification report (December 2025). F-01 could not be proven by Certora and is the primary benchmark task. P-VH-03 and P-VH-04 were proven by Certora and serve as supporting lemmas.

### `nexus_mutual/ramm_price_band`
- Family / implementation: `nexus_mutual` / `smart_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.NexusMutual.RammPriceBand.Compile`
- Source ref: `https://github.com/NexusMutual/smart-contracts@ad212043a78953a2cd98cd02b06c8e3e354c6023:contracts/modules/capital/Ramm.sol`
- Selected functions: `calculateNxm`, `_getReserves`, `getSpotPrices`, `getBookValue`
- Source artifact: `contracts/modules/capital/Ramm.sol`
- Notes: Price-band slice of Nexus Mutual RAMM. The Verity model keeps the buffered book-value computation behind buy and sell spot prices and omits unrelated state evolution machinery.

### `paladin_votes/stream_recovery_claim_usdc`
- Family / implementation: `paladin_votes` / `stream_recovery_claim`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Compile`
- Source ref: `https://github.com/Figu3/sonic-earn-recovery-system@699cbbc79def374cab9739e451acbbf866293d12:src/StreamRecoveryClaim.sol`
- Selected functions: `claimUsdc`, `_claimUsdc`, `claimWeth`, `_claimWeth`, `claimBoth`
- Source artifact: `src/StreamRecoveryClaim.sol`
- Notes: Single-round accounting slice of the full USDC/WETH claim surface, including `claimBoth`. Merkle verification is abstracted as a boolean witness and token transfer side effects are omitted.

### `safe/owner_manager_reach`
- Family / implementation: `safe` / `smart_account`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Safe.OwnerManagerReach.Compile`
- Source ref: `https://github.com/safe-global/safe-smart-account@a2e19c6aa42a45ceec68057f3fa387f169c5b321:contracts/base/OwnerManager.sol`
- Selected functions: `addOwnerWithThreshold`, `removeOwner`, `swapOwner`, `setupOwners`
- Source artifact: `contracts/base/OwnerManager.sol`
- Notes: Linked list reachability invariant preservation and functional correctness for the Safe OwnerManager. Based on the Certora OwnerReach.spec which defines the inListReachable and reachableInList invariants. All 15 proof tasks are complete (0 sorry) covering acyclicity, inListReachable, ownerListInvariant preservation, and isOwner functional correctness for all four operations. The unprovable stronglyAcyclic axiom was replaced with the provable uniquePredecessor property. Functional correctness proofs verify that each operation changes exactly the intended owners and leaves all others unchanged.

### `termmax/order_v2_buy_xt_single_segment`
- Family / implementation: `termmax` / `contracts_v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Compile`
- Source ref: `https://github.com/term-structure/termmax-contract-v2@64bd47b98e064c7fb91ab4a59b70520e0ec285d5:contracts/v2/TermMaxOrderV2.sol`
- Selected functions: `swapExactTokenToToken`, `_swapAndUpdateReserves`, `_buyToken`, `_buyXt`, `_buyXtStep`, `buyXt`, `cutsReverseIter`, `calcIntervalProps`, `plusInt256`
- Source artifact: `contracts/v2/TermMaxOrderV2.sol`
- Notes: TermMax range-order AMM slice for pricing-state transition correctness. The proof target is the highest-signal easy theorem in this family: on the successful single-segment `debtToken -> XT` exact-input path, the stored `virtualXtReserve` decreases by exactly the XT amount implied by the curve.

### `wildcat/borrow_liquidity_safety`
- Family / implementation: `wildcat` / `v2_protocol`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Compile`
- Source ref: `https://github.com/wildcat-finance/v2-protocol@a70f297fbd1b1ab597e0e9a3458a2d13a34b4657:src/market/WildcatMarket.sol`
- Selected functions: `borrow`, `_getUpdatedState`, `liquidityRequired`, `borrowableAssets`
- Source artifact: `src/market/WildcatMarket.sol`
- Notes: Wildcat V2 borrow safety slice proving that a successful positive borrow cannot pull market assets below the liquidity requirement computed from the updated state used by the borrow guard. The required liquidity includes the reserve-ratio-backed portion of non-pending supply, 100% of pending withdrawals, 100% of normalized unclaimed withdrawals, and updated accrued protocol fees.

### `zama/erc7984_confidential_token`
- Family / implementation: `zama` / `confidential_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Compile`
- Source ref: `https://github.com/OpenZeppelin/openzeppelin-confidential-contracts@master:contracts/token/ERC7984/ERC7984.sol`
- Selected functions: `_update`, `_transfer`, `_mint`, `_burn`, `confidentialTransferFrom`, `setOperator`
- Source artifact: `contracts/token/ERC7984/ERC7984.sol`
- Notes: ERC-7984 is the confidential fungible token standard co-developed by Zama and OpenZeppelin for the fhEVM. The key verification targets are balance conservation (no tokens created/destroyed by transfers), correctness of the FHE.select pattern (insufficient balance → silent 0-transfer instead of revert), mint/burn accounting, overflow protection via FHESafeMath.tryIncrease, operator-gated transferFrom, and functional correctness of setOperator. Eleven proof tasks cover the 5 modeled functions.

## Non-buildable active cases

- None

## Active tasks

### `alchemix/earmark_conservation/earmark_preserves_invariant`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Alchemix.EarmarkConservation._earmark_preserves_invariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/alchemix/earmark_conservation/verity/Contract.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Contract.lean`
- Specification files: `cases/alchemix/earmark_conservation/verity/Specs.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Alchemix/EarmarkConservation/Tasks/EarmarkPreservesInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Alchemix.EarmarkConservation.Proofs`

### `alchemix/earmark_conservation/redeem_preserves_invariant`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Alchemix.EarmarkConservation.redeem_preserves_invariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/alchemix/earmark_conservation/verity/Contract.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Contract.lean`
- Specification files: `cases/alchemix/earmark_conservation/verity/Specs.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Alchemix/EarmarkConservation/Tasks/RedeemPreservesInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Alchemix.EarmarkConservation.Proofs`

### `alchemix/earmark_conservation/sub_debt_preserves_invariant`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Alchemix.EarmarkConservation._subDebt_preserves_invariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/alchemix/earmark_conservation/verity/Contract.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Contract.lean`
- Specification files: `cases/alchemix/earmark_conservation/verity/Specs.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Alchemix/EarmarkConservation/Tasks/SubDebtPreservesInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Alchemix.EarmarkConservation.Proofs`

### `alchemix/earmark_conservation/sub_earmarked_debt_preserves_invariant`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Alchemix.EarmarkConservation._subEarmarkedDebt_preserves_invariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/alchemix/earmark_conservation/verity/Contract.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Contract.lean`
- Specification files: `cases/alchemix/earmark_conservation/verity/Specs.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Alchemix/EarmarkConservation/Tasks/SubEarmarkedDebtPreservesInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Alchemix.EarmarkConservation.Proofs`

### `alchemix/earmark_conservation/sync_account_preserves_invariant`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Alchemix.EarmarkConservation._sync_preserves_invariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/alchemix/earmark_conservation/verity/Contract.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Contract.lean`
- Specification files: `cases/alchemix/earmark_conservation/verity/Specs.lean`, `Benchmark/Cases/Alchemix/EarmarkConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Alchemix/EarmarkConservation/Tasks/SyncAccountPreservesInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Alchemix.EarmarkConservation.Proofs`

### `cork/pool_solvency/solvency_preserved`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Cork.PoolSolvency.solvency_preserved`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/cork/pool_solvency/verity/Contract.lean`, `Benchmark/Cases/Cork/PoolSolvency/Contract.lean`
- Specification files: `cases/cork/pool_solvency/verity/Specs.lean`, `Benchmark/Cases/Cork/PoolSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/Cork/PoolSolvency/Tasks/SolvencyPreserved.lean`
- Hidden reference solution: `Benchmark.Cases.Cork.PoolSolvency.Proofs`

### `damn_vulnerable_defi/side_entrance/deposit_sets_pool_balance`
- Track / property class / proof family: `proof-only` / `storage_update` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_pool_balance`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/damn_vulnerable_defi/side_entrance/verity/Contract.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Contract.lean`
- Specification files: `cases/damn_vulnerable_defi/side_entrance/verity/Specs.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Specs.lean`
- Editable proof file: `Benchmark/Generated/DamnVulnerableDeFi/SideEntrance/Tasks/DepositSetsPoolBalance.lean`
- Hidden reference solution: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Proofs`

### `damn_vulnerable_defi/side_entrance/deposit_sets_sender_credit`
- Track / property class / proof family: `proof-only` / `balance_credit_update` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_sender_credit`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/damn_vulnerable_defi/side_entrance/verity/Contract.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Contract.lean`
- Specification files: `cases/damn_vulnerable_defi/side_entrance/verity/Specs.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Specs.lean`
- Editable proof file: `Benchmark/Generated/DamnVulnerableDeFi/SideEntrance/Tasks/DepositSetsSenderCredit.lean`
- Hidden reference solution: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Proofs`

### `damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool`
- Track / property class / proof family: `proof-only` / `exploit_trace` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.exploit_trace_drains_pool`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/damn_vulnerable_defi/side_entrance/verity/Contract.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Contract.lean`
- Specification files: `cases/damn_vulnerable_defi/side_entrance/verity/Specs.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Specs.lean`
- Editable proof file: `Benchmark/Generated/DamnVulnerableDeFi/SideEntrance/Tasks/ExploitTraceDrainsPool.lean`
- Hidden reference solution: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Proofs`

### `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance`
- Track / property class / proof family: `proof-only` / `accounting_invariant_break` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_preserves_pool_balance`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/damn_vulnerable_defi/side_entrance/verity/Contract.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Contract.lean`
- Specification files: `cases/damn_vulnerable_defi/side_entrance/verity/Specs.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Specs.lean`
- Editable proof file: `Benchmark/Generated/DamnVulnerableDeFi/SideEntrance/Tasks/FlashLoanViaDepositPreservesPoolBalance.lean`
- Hidden reference solution: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Proofs`

### `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_sets_sender_credit`
- Track / property class / proof family: `proof-only` / `balance_credit_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_sets_sender_credit`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/damn_vulnerable_defi/side_entrance/verity/Contract.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Contract.lean`
- Specification files: `cases/damn_vulnerable_defi/side_entrance/verity/Specs.lean`, `Benchmark/Cases/DamnVulnerableDeFi/SideEntrance/Specs.lean`
- Editable proof file: `Benchmark/Generated/DamnVulnerableDeFi/SideEntrance/Tasks/FlashLoanViaDepositSetsSenderCredit.lean`
- Hidden reference solution: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Proofs`

### `ethereum/deposit_contract_minimal/chain_start_threshold`
- Track / property class / proof family: `proof-only` / `threshold_activation` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_starts_chain_at_threshold`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ethereum/deposit_contract_minimal/verity/Contract.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Contract.lean`
- Specification files: `cases/ethereum/deposit_contract_minimal/verity/Specs.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Specs.lean`
- Editable proof file: `Benchmark/Generated/Ethereum/DepositContractMinimal/Tasks/ChainStartThreshold.lean`
- Hidden reference solution: `Benchmark.Cases.Ethereum.DepositContractMinimal.Proofs`

### `ethereum/deposit_contract_minimal/deposit_count`
- Track / property class / proof family: `proof-only` / `monotonic_counter` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Ethereum.DepositContractMinimal.deposit_increments_deposit_count`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ethereum/deposit_contract_minimal/verity/Contract.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Contract.lean`
- Specification files: `cases/ethereum/deposit_contract_minimal/verity/Specs.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Specs.lean`
- Editable proof file: `Benchmark/Generated/Ethereum/DepositContractMinimal/Tasks/DepositCount.lean`
- Hidden reference solution: `Benchmark.Cases.Ethereum.DepositContractMinimal.Proofs`

### `ethereum/deposit_contract_minimal/full_deposit_increments_full_count`
- Track / property class / proof family: `proof-only` / `monotonic_counter` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_increments_full_count`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ethereum/deposit_contract_minimal/verity/Contract.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Contract.lean`
- Specification files: `cases/ethereum/deposit_contract_minimal/verity/Specs.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Specs.lean`
- Editable proof file: `Benchmark/Generated/Ethereum/DepositContractMinimal/Tasks/FullDepositIncrementsFullCount.lean`
- Hidden reference solution: `Benchmark.Cases.Ethereum.DepositContractMinimal.Proofs`

### `ethereum/deposit_contract_minimal/full_deposit_preserves_partial_gap`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_preserves_partial_gap`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ethereum/deposit_contract_minimal/verity/Contract.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Contract.lean`
- Specification files: `cases/ethereum/deposit_contract_minimal/verity/Specs.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Specs.lean`
- Editable proof file: `Benchmark/Generated/Ethereum/DepositContractMinimal/Tasks/FullDepositPreservesPartialGap.lean`
- Hidden reference solution: `Benchmark.Cases.Ethereum.DepositContractMinimal.Proofs`

### `ethereum/deposit_contract_minimal/small_deposit_preserves_full_count`
- Track / property class / proof family: `proof-only` / `threshold_partition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Ethereum.DepositContractMinimal.small_deposit_preserves_full_count`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ethereum/deposit_contract_minimal/verity/Contract.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Contract.lean`
- Specification files: `cases/ethereum/deposit_contract_minimal/verity/Specs.lean`, `Benchmark/Cases/Ethereum/DepositContractMinimal/Specs.lean`
- Editable proof file: `Benchmark/Generated/Ethereum/DepositContractMinimal/Tasks/SmallDepositPreservesFullCount.lean`
- Hidden reference solution: `Benchmark.Cases.Ethereum.DepositContractMinimal.Proofs`

### `kleros/sortition_trees/draw_interval_matches_weights`
- Track / property class / proof family: `proof-only` / `weighted_selection` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Kleros.SortitionTrees.draw_interval_matches_weights`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kleros/sortition_trees/verity/Contract.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Contract.lean`
- Specification files: `cases/kleros/sortition_trees/verity/Specs.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Specs.lean`
- Editable proof file: `Benchmark/Generated/Kleros/SortitionTrees/Tasks/DrawIntervalMatchesWeights.lean`
- Hidden reference solution: `Benchmark.Cases.Kleros.SortitionTrees.Proofs`

### `kleros/sortition_trees/draw_selects_valid_leaf`
- Track / property class / proof family: `proof-only` / `output_range` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Kleros.SortitionTrees.draw_selects_valid_leaf`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kleros/sortition_trees/verity/Contract.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Contract.lean`
- Specification files: `cases/kleros/sortition_trees/verity/Specs.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Specs.lean`
- Editable proof file: `Benchmark/Generated/Kleros/SortitionTrees/Tasks/DrawSelectsValidLeaf.lean`
- Hidden reference solution: `Benchmark.Cases.Kleros.SortitionTrees.Proofs`

### `kleros/sortition_trees/node_id_bijection`
- Track / property class / proof family: `proof-only` / `mapping_consistency` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Kleros.SortitionTrees.node_id_bijection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kleros/sortition_trees/verity/Contract.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Contract.lean`
- Specification files: `cases/kleros/sortition_trees/verity/Specs.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Specs.lean`
- Editable proof file: `Benchmark/Generated/Kleros/SortitionTrees/Tasks/NodeIdBijection.lean`
- Hidden reference solution: `Benchmark.Cases.Kleros.SortitionTrees.Proofs`

### `kleros/sortition_trees/parent_equals_sum_of_children`
- Track / property class / proof family: `proof-only` / `tree_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Kleros.SortitionTrees.parent_equals_sum_of_children`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kleros/sortition_trees/verity/Contract.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Contract.lean`
- Specification files: `cases/kleros/sortition_trees/verity/Specs.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Specs.lean`
- Editable proof file: `Benchmark/Generated/Kleros/SortitionTrees/Tasks/ParentEqualsSumOfChildren.lean`
- Hidden reference solution: `Benchmark.Cases.Kleros.SortitionTrees.Proofs`

### `kleros/sortition_trees/root_equals_sum_of_leaves`
- Track / property class / proof family: `proof-only` / `total_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Kleros.SortitionTrees.root_equals_sum_of_leaves`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kleros/sortition_trees/verity/Contract.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Contract.lean`
- Specification files: `cases/kleros/sortition_trees/verity/Specs.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Specs.lean`
- Editable proof file: `Benchmark/Generated/Kleros/SortitionTrees/Tasks/RootEqualsSumOfLeaves.lean`
- Hidden reference solution: `Benchmark.Cases.Kleros.SortitionTrees.Proofs`

### `kleros/sortition_trees/root_minus_left_equals_right_subtree`
- Track / property class / proof family: `proof-only` / `subtree_partition` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Kleros.SortitionTrees.root_minus_left_equals_right_subtree`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kleros/sortition_trees/verity/Contract.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Contract.lean`
- Specification files: `cases/kleros/sortition_trees/verity/Specs.lean`, `Benchmark/Cases/Kleros/SortitionTrees/Specs.lean`
- Editable proof file: `Benchmark/Generated/Kleros/SortitionTrees/Tasks/RootMinusLeftEqualsRightSubtree.lean`
- Hidden reference solution: `Benchmark.Cases.Kleros.SortitionTrees.Proofs`

### `lido/vaulthub_locked/ceildiv_sandwich`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lido.VaulthubLocked.ceildiv_sandwich`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lido/vaulthub_locked/verity/Contract.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Contract.lean`
- Specification files: `cases/lido/vaulthub_locked/verity/Specs.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lido/VaulthubLocked/Tasks/CeildivSandwich.lean`
- Hidden reference solution: `Benchmark.Cases.Lido.VaulthubLocked.Proofs`

### `lido/vaulthub_locked/locked_funds_solvency`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lido/vaulthub_locked/verity/Contract.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Contract.lean`
- Specification files: `cases/lido/vaulthub_locked/verity/Specs.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lido/VaulthubLocked/Tasks/LockedFundsSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.Lido.VaulthubLocked.Proofs`

### `lido/vaulthub_locked/max_liability_shares_bound`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lido.VaulthubLocked.max_liability_shares_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lido/vaulthub_locked/verity/Contract.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Contract.lean`
- Specification files: `cases/lido/vaulthub_locked/verity/Specs.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lido/VaulthubLocked/Tasks/MaxLiabilitySharesBound.lean`
- Hidden reference solution: `Benchmark.Cases.Lido.VaulthubLocked.Proofs`

### `lido/vaulthub_locked/reserve_ratio_bounds`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lido.VaulthubLocked.reserve_ratio_bounds`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lido/vaulthub_locked/verity/Contract.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Contract.lean`
- Specification files: `cases/lido/vaulthub_locked/verity/Specs.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lido/VaulthubLocked/Tasks/ReserveRatioBounds.lean`
- Hidden reference solution: `Benchmark.Cases.Lido.VaulthubLocked.Proofs`

### `lido/vaulthub_locked/shares_conversion_monotone`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lido.VaulthubLocked.shares_conversion_monotone`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lido/vaulthub_locked/verity/Contract.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Contract.lean`
- Specification files: `cases/lido/vaulthub_locked/verity/Specs.lean`, `Benchmark/Cases/Lido/VaulthubLocked/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lido/VaulthubLocked/Tasks/SharesConversionMonotone.lean`
- Hidden reference solution: `Benchmark.Cases.Lido.VaulthubLocked.Proofs`

### `nexus_mutual/ramm_price_band/sync_sets_book_value`
- Track / property class / proof family: `proof-only` / `price_computation` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_book_value`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/nexus_mutual/ramm_price_band/verity/Contract.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Contract.lean`
- Specification files: `cases/nexus_mutual/ramm_price_band/verity/Specs.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/NexusMutual/RammPriceBand/Tasks/SyncSetsBookValue.lean`
- Hidden reference solution: `Benchmark.Cases.NexusMutual.RammPriceBand.Proofs`

### `nexus_mutual/ramm_price_band/sync_sets_buy_price`
- Track / property class / proof family: `proof-only` / `price_computation` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_buy_price`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/nexus_mutual/ramm_price_band/verity/Contract.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Contract.lean`
- Specification files: `cases/nexus_mutual/ramm_price_band/verity/Specs.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/NexusMutual/RammPriceBand/Tasks/SyncSetsBuyPrice.lean`
- Hidden reference solution: `Benchmark.Cases.NexusMutual.RammPriceBand.Proofs`

### `nexus_mutual/ramm_price_band/sync_sets_capital`
- Track / property class / proof family: `proof-only` / `storage_write` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_capital`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/nexus_mutual/ramm_price_band/verity/Contract.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Contract.lean`
- Specification files: `cases/nexus_mutual/ramm_price_band/verity/Specs.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/NexusMutual/RammPriceBand/Tasks/SyncSetsCapital.lean`
- Hidden reference solution: `Benchmark.Cases.NexusMutual.RammPriceBand.Proofs`

### `nexus_mutual/ramm_price_band/sync_sets_sell_price`
- Track / property class / proof family: `proof-only` / `price_computation` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_sell_price`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/nexus_mutual/ramm_price_band/verity/Contract.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Contract.lean`
- Specification files: `cases/nexus_mutual/ramm_price_band/verity/Specs.lean`, `Benchmark/Cases/NexusMutual/RammPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/NexusMutual/RammPriceBand/Tasks/SyncSetsSellPrice.lean`
- Hidden reference solution: `Benchmark.Cases.NexusMutual.RammPriceBand.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_claim_marks_both_claimed`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_marks_both_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothClaimMarksBothClaimed.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_round_claimed`
- Track / property class / proof family: `proof-only` / `accounting_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_updates_round_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothClaimUpdatesRoundClaimed.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_total_allocated`
- Track / property class / proof family: `proof-only` / `accounting_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_updates_total_allocated`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothClaimUpdatesTotalAllocated.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_claimed_plus_allocated_conserved`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_claimed_plus_allocated_conserved`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothClaimedPlusAllocatedConserved.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_matches_independent_claims`
- Track / property class / proof family: `proof-only` / `noninterference` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_matches_independent_claims`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothMatchesIndependentClaims.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_no_overclaim`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_preserves_round_bounds`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothNoOverclaim.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_usdc_bound_violation_rejected`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_usdc_exceeds_total`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothUsdcBoundViolationRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_usdc_double_claim_rejected`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_usdc_already_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothUsdcDoubleClaimRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_weth_bound_violation_rejected`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_weth_exceeds_total`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothWethBoundViolationRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/both_weth_double_claim_rejected`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_weth_already_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BothWethDoubleClaimRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/bound_violation_rejected`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_reverts_if_exceeds_total`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/BoundViolationRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/claim_marks_user`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_marks_user_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/ClaimMarksUser.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/claim_updates_round_claimed`
- Track / property class / proof family: `proof-only` / `accounting_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_updates_round_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/ClaimUpdatesRoundClaimed.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/claim_updates_total_allocated`
- Track / property class / proof family: `proof-only` / `accounting_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_updates_total_allocated`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/ClaimUpdatesTotalAllocated.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/claimed_plus_allocated_conserved`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_claimed_plus_allocated_conserved`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/ClaimedPlusAllocatedConserved.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/double_claim_rejected`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_reverts_if_already_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/DoubleClaimRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/no_overclaim`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_preserves_round_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/NoOverclaim.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/usdc_preserves_weth_state`
- Track / property class / proof family: `proof-only` / `frame_property` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_preserves_weth_state`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/UsdcPreservesWethState.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_bound_violation_rejected`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_reverts_if_exceeds_total`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethBoundViolationRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_claim_marks_user`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_marks_user_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethClaimMarksUser.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_round_claimed`
- Track / property class / proof family: `proof-only` / `accounting_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_updates_round_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethClaimUpdatesRoundClaimed.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_claim_updates_total_allocated`
- Track / property class / proof family: `proof-only` / `accounting_update` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_updates_total_allocated`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethClaimUpdatesTotalAllocated.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_claimed_plus_allocated_conserved`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_claimed_plus_allocated_conserved`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethClaimedPlusAllocatedConserved.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_double_claim_rejected`
- Track / property class / proof family: `proof-only` / `authorization_state` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_reverts_if_already_claimed`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethDoubleClaimRejected.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_no_overclaim`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_preserves_round_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethNoOverclaim.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `paladin_votes/stream_recovery_claim_usdc/weth_preserves_usdc_state`
- Track / property class / proof family: `proof-only` / `frame_property` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_preserves_usdc_state`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Contract.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Contract.lean`
- Specification files: `cases/paladin_votes/stream_recovery_claim_usdc/verity/Specs.lean`, `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean`
- Editable proof file: `Benchmark/Generated/PaladinVotes/StreamRecoveryClaimUsdc/Tasks/WethPreservesUsdcState.lean`
- Hidden reference solution: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Proofs`

### `safe/owner_manager_reach/add_owner_acyclicity`
- Track / property class / proof family: `proof-only` / `linked_list_acyclicity` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.addOwner_acyclicity`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/AddOwnerAcyclicity.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/add_owner_is_owner_correctness`
- Track / property class / proof family: `proof-only` / `isOwner_effect` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.addOwner_isOwnerCorrectness`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/AddOwnerIsOwnerCorrectness.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/add_owner_owner_list_invariant`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.addOwner_ownerListInvariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/AddOwnerOwnerListInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/in_list_reachable`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.in_list_reachable`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/InListReachable.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/remove_owner_acyclicity`
- Track / property class / proof family: `proof-only` / `linked_list_acyclicity` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.removeOwner_acyclicity`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/RemoveOwnerAcyclicity.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/remove_owner_in_list_reachable`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.removeOwner_inListReachable`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/RemoveOwnerInListReachable.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/remove_owner_is_owner_correctness`
- Track / property class / proof family: `proof-only` / `isOwner_effect` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.removeOwner_isOwnerCorrectness`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/RemoveOwnerIsOwnerCorrectness.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/remove_owner_owner_list_invariant`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.removeOwner_ownerListInvariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/RemoveOwnerOwnerListInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/setup_owners_acyclicity`
- Track / property class / proof family: `proof-only` / `linked_list_acyclicity` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.setupOwners_acyclicity`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SetupOwnersAcyclicity.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/setup_owners_in_list_reachable`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.setupOwners_inListReachable`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SetupOwnersInListReachable.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/setup_owners_owner_list_invariant`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.setupOwners_ownerListInvariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SetupOwnersOwnerListInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/swap_owner_acyclicity`
- Track / property class / proof family: `proof-only` / `linked_list_acyclicity` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.swapOwner_acyclicity`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SwapOwnerAcyclicity.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/swap_owner_in_list_reachable`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.swapOwner_inListReachable`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SwapOwnerInListReachable.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/swap_owner_is_owner_correctness`
- Track / property class / proof family: `proof-only` / `isOwner_effect` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.swapOwner_isOwnerCorrectness`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SwapOwnerIsOwnerCorrectness.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `safe/owner_manager_reach/swap_owner_owner_list_invariant`
- Track / property class / proof family: `proof-only` / `linked_list_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Safe.OwnerManagerReach.swapOwner_ownerListInvariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/safe/owner_manager_reach/verity/Contract.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Contract.lean`
- Specification files: `cases/safe/owner_manager_reach/verity/Specs.lean`, `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean`
- Editable proof file: `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/SwapOwnerOwnerListInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.Safe.OwnerManagerReach.Proofs`

### `termmax/order_v2_buy_xt_single_segment/swap_debt_token_to_xt_updates_virtual_xt_reserve`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.swapDebtTokenToXt_updates_virtual_xt_reserve`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/termmax/order_v2_buy_xt_single_segment/verity/Contract.lean`, `Benchmark/Cases/TermMax/OrderV2BuyXtSingleSegment/Contract.lean`
- Specification files: `cases/termmax/order_v2_buy_xt_single_segment/verity/Specs.lean`, `Benchmark/Cases/TermMax/OrderV2BuyXtSingleSegment/Specs.lean`
- Editable proof file: `Benchmark/Generated/TermMax/OrderV2BuyXtSingleSegment/Tasks/SwapDebtTokenToXtUpdatesVirtualXtReserve.lean`
- Hidden reference solution: `Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Proofs`

### `wildcat/borrow_liquidity_safety/positive_borrow_preserves_required_liquidity`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Wildcat.BorrowLiquiditySafety.positive_borrow_preserves_required_liquidity`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/wildcat/borrow_liquidity_safety/verity/Contract.lean`, `Benchmark/Cases/Wildcat/BorrowLiquiditySafety/Contract.lean`
- Specification files: `cases/wildcat/borrow_liquidity_safety/verity/Specs.lean`, `Benchmark/Cases/Wildcat/BorrowLiquiditySafety/Specs.lean`
- Editable proof file: `Benchmark/Generated/Wildcat/BorrowLiquiditySafety/Tasks/PositiveBorrowPreservesRequiredLiquidity.lean`
- Hidden reference solution: `Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Proofs`

### `zama/erc7984_confidential_token/burn_decreases_supply`
- Track / property class / proof family: `proof-only` / `supply_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.burn_decreases_supply`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/BurnDecreasesSupply.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/burn_insufficient`
- Track / property class / proof family: `proof-only` / `silent_failure` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.burn_insufficient`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/BurnInsufficient.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/mint_increases_supply`
- Track / property class / proof family: `proof-only` / `supply_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_increases_supply`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/MintIncreasesSupply.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/mint_overflow_protection`
- Track / property class / proof family: `proof-only` / `overflow_safety` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_overflow_protection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/MintOverflowProtection.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/setOperator_updates`
- Track / property class / proof family: `proof-only` / `storage_write` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.setOperator_updates`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/SetOperatorUpdates.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/transferFrom_conservation`
- Track / property class / proof family: `proof-only` / `balance_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.transferFrom_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/TransferFromConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/transfer_conservation`
- Track / property class / proof family: `proof-only` / `balance_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/TransferConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/transfer_insufficient`
- Track / property class / proof family: `proof-only` / `silent_failure` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_insufficient`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/TransferInsufficient.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/transfer_no_balance_revert`
- Track / property class / proof family: `proof-only` / `non_leakage` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_no_balance_revert`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/TransferNoBalanceRevert.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/transfer_preserves_supply`
- Track / property class / proof family: `proof-only` / `supply_invariance` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_preserves_supply`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/TransferPreservesSupply.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

### `zama/erc7984_confidential_token/transfer_sufficient`
- Track / property class / proof family: `proof-only` / `balance_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_sufficient`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/TransferSufficient.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Proofs`

## Backlog

### `openzeppelin/erc4626_virtual_offset_deposit`
- Family / implementation: `openzeppelin` / `contracts`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Compile`
- Source ref: `https://github.com/OpenZeppelin/openzeppelin-contracts@45f032d1bcf1a88b7bc90154d7eef76c87bf9d45:contracts/token/ERC20/extensions/ERC4626.sol`
- Selected functions: `previewDeposit`, `deposit`
- Source artifact: `contracts/token/ERC20/extensions/ERC4626.sol`
- Notes: Backlog ERC-4626 benchmark slice derived from OpenZeppelin's virtual-offset design and inflation-attack analysis. The committed proof module validates the four arithmetic and state-transition theorems, so the case is runnable in the reference-solution benchmark path while remaining backlog-scoped.

### `uniswap_v2/pair_fee_adjusted_swap`
- Family / implementation: `uniswap_v2` / `v2_core`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Compile`
- Source ref: `https://github.com/Uniswap/v2-core@ee547b17853e71ed4e0101ccfd52e70d5acded58:contracts/UniswapV2Pair.sol`
- Selected functions: `swap`
- Source artifact: `contracts/UniswapV2Pair.sol`
- Notes: Backlog AMM benchmark slice for reasoning about fee-adjusted constant-product guards and post-swap reserve synchronization without exposing the full Uniswap execution path. The committed proof module makes the case runnable in the reference-solution benchmark path while it remains backlog-scoped.

### `unlink_xyz/placeholder`
- Family / implementation: `unlink_xyz` / `monorepo`
- Stage: `candidate`
- Status dimensions: translation=`blocked`, spec=`not_started`, proof=`blocked`
- Failure reason: `upstream_unavailable`
- Source ref: `unresolved:https://github.com/unlink-xyz/monorepo@unknown:TBD`
- Source artifact: `TBD`
- Notes: Referenced repository was not resolvable during setup, so no candidate contract was pinned.

### `usual/placeholder`
- Family / implementation: `usual` / `private_repo`
- Stage: `candidate`
- Status dimensions: translation=`blocked`, spec=`not_started`, proof=`blocked`
- Failure reason: `private_access`
- Source ref: `unresolved:usual/private_repo@unknown:TBD`
- Source artifact: `TBD`
- Notes: Pending private repository access and target selection.

## Commands

- Validate manifests: `python3 scripts/validate_manifests.py`
- Regenerate metadata: `python3 scripts/generate_metadata.py`
- Run one task: `./scripts/run_task.sh <project/case_id/task_id>`
- Run one case: `./scripts/run_case.sh <project/case_id>`
- Run active suite: `./scripts/run_all.sh`
- Run repo check: `./scripts/check.sh`
