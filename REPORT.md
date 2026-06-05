# Benchmark report

This report is generated from the benchmark manifests.

## Summary

- Families: 27
- Implementations: 28
- Active cases: 25
- Buildable active cases: 25
- Active tasks: 135
- Backlog cases: 3

## Buildable active cases

### `alchemix/earmark_conservation`
- Family / implementation: `alchemix` / `v3`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Alchemix.EarmarkConservation.Compile`
- Source ref: `https://github.com/alchemix-finance/v3@117c95b6ee11a75221d6fbdc79f16ac6acdb96f5:src/AlchemistV3.sol`
- Selected functions: `_earmark`, `_sync`, `_computeUnrealizedAccount`, `redeem`, `_subEarmarkedDebt`, `_subDebt`
- Upstream source artifact: `src/AlchemistV3.sol`
- Notes: Earmark conservation invariant for Alchemix V3 lazy-accrual debt accounting. The literal "sum of stored account.earmarked equals cumulativeEarmarked" is provably false on the deployed code (see AlchemistV3.sol:1014 comment "Global can lag local by rounding") because per-account earmarked is updated lazily inside _sync(tokenId). The lazy-projected version proven here is the property the design actually maintains and that downstream consumers (redemption math, collateral debit) rely on.

### `balancer/reclamm_swap_rounding`
- Family / implementation: `balancer` / `reclamm`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`draft`, proof=`complete`
- Lean target: `Benchmark.Cases.Balancer.ReClammSwapRounding.Compile`
- Source ref: `https://github.com/balancer/reclamm@cff18033d401a61326a2d6c078507084cbdc864b:contracts/lib/ReClammMath.sol`
- Selected functions: `computeOutGivenIn`, `computeInGivenOut`, `onSwap`
- Upstream source artifact: `contracts/lib/ReClammMath.sol`
- Notes: Certora I-01 identified that an intermediate floor division can undermine an intended rounding-up path. This case isolates the ReClamm arithmetic surface where that class of issue matters: exact-in swaps must not overpay output, and exact-out swaps must not undercharge input.

### `cork/pool_solvency`
- Family / implementation: `cork` / `phoenix`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Cork.PoolSolvency.Compile`
- Source ref: `https://github.com/Cork-Technology/phoenix@40d9b173c4b2262a93f36167355b5311d5f58e6b:contracts/libraries/PoolLib.sol`
- Selected functions: `previewUnwindExerciseOther`, `_unwindExercise`
- Upstream source artifact: `contracts/libraries/PoolLib.sol`
- Notes: Cork Phoenix pool solvency slice targeting the Certora P-02 gap. Based on the Certora formal verification report (September-December 2025). P-02 was verified for all functions except unwindExerciseOther (timeout).

### `damn_vulnerable_defi/side_entrance`
- Family / implementation: `damn_vulnerable_defi` / `v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Compile`
- Source ref: `https://github.com/OpenZeppelin/damn-vulnerable-defi@6797353c7cb5409e3d388e9e8f13954f9bb5f609:contracts/side-entrance/SideEntranceLenderPool.sol`
- Selected functions: `deposit`, `flashLoan`, `withdraw`
- Upstream source artifact: `contracts/side-entrance/SideEntranceLenderPool.sol`
- Notes: Compact Side Entrance benchmark focused on the broken coherence between pool assets and withdrawable credit when flash-loan repayment is routed through the deposit path.

### `ethereum/deposit_contract_minimal`
- Family / implementation: `ethereum` / `deposit_contract`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Ethereum.DepositContractMinimal.Compile`
- Source ref: `https://github.com/ethereum/deposit_contract@691feb18330d3d102b5a4b3d4434fac7571f51b8:deposit_contract/contracts/validator_registration.v.py`
- Selected functions: `deposit`
- Upstream source artifact: `deposit_contract/contracts/validator_registration.v.py`
- Notes: Counter-oriented slice of the deposit path. Merkle tree, SSZ hashing, and log emission are omitted so the benchmark can focus on threshold-driven state updates.

### `forgeyields/global_solvency`
- Family / implementation: `forgeyields` / `contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.ForgeYields.GlobalSolvency.Compile`
- Source ref: `https://etherscan.io/address/0xf1d326d806fa5d0d1f3747505397553cd31b191a#code@etherscan-verified-source:TokenGateway.sol`
- Selected functions: `deposit`, `requestRedeem`, `claimRedeem`, `redeemTokenGatewayDepreciated`, `transferRemote`, `handle`, `report`
- Upstream source artifact: `TokenGateway.sol`
- Notes: Reference proofs are complete for the guarded invariant across the modeled successful paths. Arithmetic hypotheses expose Solidity checked-arithmetic obligations needed by the focused model.

### `ipor/plasma_vault_redeem_split`
- Family / implementation: `ipor` / `ipor_fusion`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`revised_after_failed_fairness_target`, proof=`complete`
- Lean target: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Compile`
- Source ref: `https://github.com/IPOR-Labs/ipor-fusion/blob/3a83157ee75a7c1752d9151aff43eb92a50cb346/contracts/vaults/PlasmaVault.sol`
- Selected functions: `redeem`, `_redeem`, `_convertToAssets`, `withdrawFee`
- Upstream source artifact: `contracts/vaults/PlasmaVault.sol`
- Notes: This case is intentionally scoped to the safety property that remains true after the failed split-fairness target: a successful modeled redeem cannot decrease virtualized conversion PPS. It should be described as no decrease in the modeled ERC4626 redeemable-value ratio, not as a proof that fee-splitting is impossible or that the whole vault is bug-free.

### `kleros/sortition_trees`
- Family / implementation: `kleros` / `kleros_v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Kleros.SortitionTrees.Compile`
- Source ref: `https://github.com/kleros/kleros-v2@75125dfa54eee723cac239f20e5746d15786196b:contracts/src/libraries/SortitionTrees.sol`
- Selected functions: `set`, `updateParents`, `draw`
- Upstream source artifact: `contracts/src/libraries/SortitionTrees.sol`
- Notes: Sortition-tree slice focused on additive parent invariants, root conservation, interval-based draws, and ID/index correspondence.

### `lagoon/guardrails`
- Family / implementation: `lagoon` / `v0_6_0`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Lagoon.Guardrails.Compile`
- Source ref: `https://github.com/hopperlabsxyz/lagoon-v0@a8e73f5a5276aa4047b901083cbce127d7f7b470:src/v0.6.0/libraries/GuardrailsLib.sol`
- Selected functions: `isCompliant`
- Upstream source artifact: `src/v0.6.0/libraries/GuardrailsLib.sol`
- Notes: Proves that Lagoon guardrail compliance accepts exactly the annualized PPS variations admitted by the configured 1e18-scaled upper and signed lower bounds under the encoded successfulSolidityArithmeticScope.

### `lido/vaulthub_locked`
- Family / implementation: `lido` / `core`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Lido.VaulthubLocked.Compile`
- Source ref: `https://github.com/lidofinance/core@96738395ca3bffd6513700a45d4c9389662c5835:contracts/0.8.25/vaults/VaultHub.sol`
- Selected functions: `_locked`, `getPooledEthBySharesRoundUp`
- Upstream source artifact: `contracts/0.8.25/vaults/VaultHub.sol`
- Notes: Locked-amount arithmetic slice of Lido VaultHub (V3 vaults branch). Based on the Certora formal verification report (December 2025). F-01 could not be proven by Certora and is the primary benchmark task. P-VH-03 and P-VH-04 were proven by Certora and serve as supporting lemmas.

### `nexus_mutual/ramm_price_band`
- Family / implementation: `nexus_mutual` / `smart_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.NexusMutual.RammPriceBand.Compile`
- Source ref: `https://github.com/NexusMutual/smart-contracts@ad212043a78953a2cd98cd02b06c8e3e354c6023:contracts/modules/capital/Ramm.sol`
- Selected functions: `calculateNxm`, `_getReserves`, `getSpotPrices`, `getBookValue`
- Upstream source artifact: `contracts/modules/capital/Ramm.sol`
- Notes: Price-band slice of Nexus Mutual RAMM. The Verity model keeps the buffered book-value computation behind buy and sell spot prices and omits unrelated state evolution machinery.

### `onedelta/caller_address_integrity`
- Family / implementation: `onedelta` / `ethereum-composer`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`draft`, proof=`complete`
- Lean target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Compile`
- Source ref: `https://www.codeslaw.app/contracts/ethereum/0x97648606fcc22bd96f87345ac83bd6cfcdf0acba@verified-source-0x97648606fcc22bd96f87345ac83bd6cfcdf0acba:contracts/1delta/composer/chains/ethereum/Composer.sol`
- Selected functions: `deltaCompose`, `_deltaComposeInternal`, `_transfers`, `_transferFrom`, `_permit2TransferFrom`, `flashLoanCallback`, `swapCallback`, `clSwapCallback`
- Upstream source artifact: `contracts/1delta/composer/chains/ethereum/Composer.sol`
- Notes: This is a caller-identity benchmark, not an accounting benchmark. It proves that every modeled ERC20 and Permit2 fund-pull path uses the outer deltaCompose caller rather than an intermediate callback contract, the composer itself, or an embedded calldata address. The scope is transfer-command pulls plus the V3 callback direct-pull shortcut, not every transferFrom in the full composer source tree.

### `paladin_votes/stream_recovery_claim_usdc`
- Family / implementation: `paladin_votes` / `stream_recovery_claim`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Compile`
- Source ref: `https://github.com/Figu3/sonic-earn-recovery-system@699cbbc79def374cab9739e451acbbf866293d12:src/StreamRecoveryClaim.sol`
- Selected functions: `claimUsdc`, `_claimUsdc`, `claimWeth`, `_claimWeth`, `claimBoth`
- Upstream source artifact: `src/StreamRecoveryClaim.sol`
- Notes: Single-round accounting slice of the full USDC/WETH claim surface, including `claimBoth`. Merkle verification is abstracted as a boolean witness and token transfer side effects are omitted.

### `piku/fund_conservation`
- Family / implementation: `piku` / `inverter_oracle_queue`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Piku.FundConservation.Compile`
- Source ref: `https://github.com/InverterNetwork/contracts@8b7bc438344d646bab05b751c8eb4a7f0c8ca588:src/modules/fundingManager/oracle/FM_PC_Oracle_Redeeming_v1.sol`
- Selected functions: `_sellOrder`, `_createAndEmitOrder`, `_addToOpenRedemptionAmount`, `amountPaid`, `processPayments`, `executePaymentQueue`
- Upstream source artifact: `src/modules/fundingManager/oracle/FM_PC_Oracle_Redeeming_v1.sol`
- Notes: Fund-conservation benchmark for Piku's oracle-priced queued redemption flow: distributed backing + queued redemption backing + remaining backing + protocol treasury fees + project treasury fees equals initial backing. Queue execution functions are source context; the modeled settlement transition is the successful `amountPaid` callback.

### `polaris/bonding_curve`
- Family / implementation: `polaris` / `bonding_curve`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`complete`, proof=`complete`
- Lean target: `Benchmark.Cases.Polaris.BondingCurve.Compile`
- Source ref: `https://github.com/Polaris-Finance/bonding-curve@540c4ba5d0b86c0f42399d214f02120f3f8719b0:src/BaseBondingCurve.sol`
- Selected functions: `init`, `buy`, `sell`, `floorSellAndBurn`
- Upstream source artifact: `src/BaseBondingCurve.sol`
- Notes: Polaris' Foundry invariant asserts reserveRatioDeviation() == 0 and the same predicate for floorSupply/floorBalance. This case records the corresponding state-transition preservation property over the bonding curve accounting slice as Lean theorems with no custom axioms and no sorry/admit. The broad helper-output and raw-pow witness boundaries have been removed from the theorem statements: the proof now computes the helper's multiply and `(left + DECIMAL_PRECISION - 1) / B_PLUS_1` path around a linked external `curvePow` boundary. This benchmark still does not bit-prove PRB/ABDK pow. The generated task files remain open challenge entrypoints for agents; they do not contradict the reference proof.

### `polygon/agglayer_bridge`
- Family / implementation: `polygon` / `agglayer_bridge`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Polygon.AgglayerBridge.Compile`
- Source ref: `https://github.com/agglayer/agglayer-contracts@110bda5a03e70ee7331bc06407a8e79226d3e520:contracts/AgglayerBridge.sol`
- Selected functions: `claimAsset`, `claimMessage`, `_verifyLeafAndSetNullifier`, `_verifyLeaf`, `_setAndCheckClaimed`, `isClaimed`, `_validateAndDecodeGlobalIndex`, `_bitmapPositions`, `_addLeafBridge`, `_updateGlobalExitRoot`
- Upstream source artifact: `contracts/AgglayerBridge.sol`
- Notes: The public claim theorems show successful claims validate the leaf and consume the source-network/leaf-index bitmap entry. A private reachability lemma feeds the shared helper theorem that proves successful nullifier-helper execution flips the expected bitmap bit.

### `reserve/auction_price_band`
- Family / implementation: `reserve` / `dtfs`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Reserve.AuctionPriceBand.Compile`
- Source ref: `https://github.com/reserve-protocol/dtfs@14f75d18856d587adfaff24e77e5b20dda7c7267:contracts/utils/RebalancingLib.sol`
- Selected functions: `_price`
- Upstream source artifact: `contracts/utils/RebalancingLib.sol`
- Notes: Auction price band slice of Reserve DTF Protocol's RebalancingLib._price. The Verity model keeps the start/end branching plus the interior exponential decay; storage I/O and external view calls (auction + rebalance state) are folded into pure parameters.

### `rootstock/flyover_quote_lifecycle`
- Family / implementation: `rootstock` / `flyover-lbc`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`draft`, proof=`complete`
- Lean target: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Compile`
- Source ref: `https://github.com/rsksmart/liquidity-bridge-contract@88a6d1ad64aeb3ad24e01042f4211ad8649784b9:src/PegOutContract.sol`
- Selected functions: `depositPegOut`, `refundPegOut`, `refundUserPegOut`, `_increaseBalance`
- Upstream source artifact: `src/PegOutContract.sol`
- Notes: This case focuses on quote lifecycle conservation and single settlement for Rootstock Flyover / LBC peg-outs. The property proved here is not a Bitcoin proof verifier; it is the Rootstock-side accounting guarantee for the amount already registered by depositPegOut.

### `safe/owner_manager_reach`
- Family / implementation: `safe` / `smart_account`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Safe.OwnerManagerReach.Compile`
- Source ref: `https://github.com/safe-global/safe-smart-account@a2e19c6aa42a45ceec68057f3fa387f169c5b321:contracts/base/OwnerManager.sol`
- Selected functions: `addOwnerWithThreshold`, `removeOwner`, `swapOwner`, `setupOwners`
- Upstream source artifact: `contracts/base/OwnerManager.sol`
- Notes: Linked list reachability invariant preservation and functional correctness for the Safe OwnerManager. Based on the Certora OwnerReach.spec which defines the inListReachable and reachableInList invariants. All 15 proof tasks are complete (0 sorry) covering acyclicity, inListReachable, ownerListInvariant preservation, and isOwner functional correctness for all four operations. The unprovable stronglyAcyclic axiom was replaced with the provable uniquePredecessor property. Functional correctness proofs verify that each operation changes exactly the intended owners and leaves all others unchanged.

### `term_finance/term_auction_clearing`
- Family / implementation: `term_finance` / `term_finance_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`proof`
- Lean target: `Benchmark.Cases.TermFinance.TermAuctionClearing.Compile`
- Source ref: `https://github.com/term-finance/term-finance-contracts/blob/127b74d871fc74e3a03d6d3b0f1fafe7e5d10275/contracts/TermAuction.sol`
- Selected functions: `_calculateClearingPrice`, `_assignBids`, `_assignOffers`
- Upstream source artifact: `contracts/TermAuction.sol`
- Notes: Clearing assignment correctness for the weekly sealed-bid uniform-price double auction: positive bid assignments respect the clearing rate floor, positive offer assignments respect the clearing rate ceiling, and assigned purchase-token principal balances exactly across both sides.

### `termmax/order_v2_buy_xt_single_segment`
- Family / implementation: `termmax` / `contracts_v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Compile`
- Source ref: `https://github.com/term-structure/termmax-contract-v2@64bd47b98e064c7fb91ab4a59b70520e0ec285d5:contracts/v2/TermMaxOrderV2.sol`
- Selected functions: `swapExactTokenToToken`, `_swapAndUpdateReserves`, `_buyToken`, `_buyXt`, `_buyXtStep`, `buyXt`, `cutsReverseIter`, `calcIntervalProps`, `plusInt256`
- Upstream source artifact: `contracts/v2/TermMaxOrderV2.sol`
- Notes: TermMax range-order AMM slice for pricing-state transition correctness. The proof target is the highest-signal easy theorem in this family: on the successful single-segment `debtToken -> XT` exact-input path, the stored `virtualXtReserve` decreases by exactly the XT amount implied by the curve.

### `usual/dao_collateral`
- Family / implementation: `usual` / `verified_proxy`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Usual.DaoCollateral.Compile`
- Source ref: `https://etherscan.io/address/0x0eec861d49f15f585d6bb4301fc4f89bce22af4e#code`
- Selected functions: `swap`, `redeem`, `_calculateFee`, `_burnStableTokenAndTransferCollateral`, `_getTokenAmountForAmountInUSD`
- Upstream source artifact: `src/daoCollateral/DaoCollateral.sol`
- Notes: Usual USD0 DaoCollateral conservation case. It verifies that no direct swap/redeem transition can create unaccounted ghost USD0 supply or debit more ghost collateral than the contract's modeled accounting permits, modulo configured redeem fee, oracle price, CBR coefficient, token decimals, and floor rounding.

### `wildcat/borrow_liquidity_safety`
- Family / implementation: `wildcat` / `v2_protocol`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Compile`
- Source ref: `https://github.com/wildcat-finance/v2-protocol@a70f297fbd1b1ab597e0e9a3458a2d13a34b4657:src/market/WildcatMarket.sol`
- Selected functions: `borrow`, `_getUpdatedState`, `liquidityRequired`, `borrowableAssets`
- Upstream source artifact: `src/market/WildcatMarket.sol`
- Notes: Wildcat V2 borrow safety slice proving that a successful positive borrow cannot pull market assets below the liquidity requirement computed from the updated state used by the borrow guard. The required liquidity includes the reserve-ratio-backed portion of non-pending supply, 100% of pending withdrawals, 100% of normalized unclaimed withdrawals, and updated accrued protocol fees.

### `zama/erc7984_confidential_token`
- Family / implementation: `zama` / `confidential_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Compile`
- Source ref: `https://github.com/OpenZeppelin/openzeppelin-confidential-contracts@83364738f0d2b1655c60627588e3493099c359f7:contracts/token/ERC7984/ERC7984.sol`
- Selected functions: `_update`, `_transfer`, `_mint`, `_burn`, `confidentialTransferFrom`, `setOperator`
- Upstream source artifact: `contracts/token/ERC7984/ERC7984.sol`
- Notes: ERC-7984 is the confidential fungible token standard co-developed by Zama and OpenZeppelin for the fhEVM. The key verification targets are balance conservation (no tokens created/destroyed by transfers), correctness of the FHE.select pattern (insufficient balance → silent 0-transfer instead of revert), mint/burn accounting, overflow protection via FHESafeMath.tryIncrease, operator-gated transferFrom, functional correctness of setOperator, and the exact match between successful deposits and credited confidential tokens. Twelve proof tasks cover the 5 modeled functions.

### `zodiac/roles_decoder_faithfulness`
- Family / implementation: `zodiac` / `roles-v3`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Compile`
- Source ref: `https://github.com/gnosisguild/zodiac-modifier-roles@172723b165d482c5565e413e9927604b0dc168b6:packages/evm/contracts/common/AbiLocation.sol`
- Selected functions: `AbiLocation.children`, `AbiLocation.size`, `AbiLocation._tailLocation`, `Topology.isInlined`, `Topology.inlinedSize`, `ConditionEvaluator.__input`
- Upstream source artifact: `packages/evm/contracts/common/AbiLocation.sol`
- Notes: This case targets the v3 decoder/callee mismatch class that required custom verifiers in Zodiac Roles v2. The theorem scope covers static values, dynamic bytes/string, tuples, dynamic arrays, nested AbiEncoded, and transparent logical wrappers. Operator.Custom, Zip, Slice, Pluck, MultiSendUnwrapper, comparison consumption, and external calls are intentionally out of scope.

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

### `balancer/reclamm_swap_rounding/on_swap_fixed_virtual_balances_product_non_decreasing`
- Track / property class / proof family: `proof-only` / `arithmetic_rounding` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Balancer.ReClammSwapRounding.onSwap_fixed_virtual_balances_product_non_decreasing`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/balancer/reclamm_swap_rounding/verity/Contract.lean`, `Benchmark/Cases/Balancer/ReClammSwapRounding/Contract.lean`
- Specification files: `cases/balancer/reclamm_swap_rounding/verity/Specs.lean`, `Benchmark/Cases/Balancer/ReClammSwapRounding/Specs.lean`
- Editable proof file: `Benchmark/Generated/Balancer/ReClammSwapRounding/Tasks/OnSwapFixedVirtualBalancesProductNonDecreasing.lean`
- Hidden reference solution: `Benchmark.Cases.Balancer.ReClammSwapRounding.Proofs`

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

### `forgeyields/global_solvency/claim_redeem_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.claimRedeem_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/ClaimRedeemPreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `forgeyields/global_solvency/deposit_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.deposit_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/DepositPreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `forgeyields/global_solvency/handle_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.handle_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/HandlePreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `forgeyields/global_solvency/redeem_token_gateway_depreciated_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.redeemTokenGatewayDepreciated_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/RedeemTokenGatewayDepreciatedPreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `forgeyields/global_solvency/report_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.report_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/ReportPreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `forgeyields/global_solvency/request_redeem_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.requestRedeem_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/RequestRedeemPreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `forgeyields/global_solvency/transfer_remote_preserves_global_solvency`
- Track / property class / proof family: `proof-only` / `guarded_solvency` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ForgeYields.GlobalSolvency.transferRemote_preserves_global_solvency`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/forgeyields/global_solvency/verity/Contract.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Contract.lean`
- Specification files: `cases/forgeyields/global_solvency/verity/Specs.lean`, `Benchmark/Cases/ForgeYields/GlobalSolvency/Specs.lean`
- Editable proof file: `Benchmark/Generated/ForgeYields/GlobalSolvency/Tasks/TransferRemotePreservesGlobalSolvency.lean`
- Hidden reference solution: `Benchmark.Cases.ForgeYields.GlobalSolvency.Proofs`

### `ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free`
- Track / property class / proof family: `proof-only` / `fee_payout_bound` / `arithmetic_accounting`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.fee_payout_bounded_by_fee_free_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ipor/plasma_vault_redeem_split/verity/Contract.lean`, `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Contract.lean`
- Specification files: `cases/ipor/plasma_vault_redeem_split/verity/Specs.lean`, `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Specs.lean`
- Editable proof file: `Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks/FeePayoutBoundedByFeeFree.lean`
- Hidden reference solution: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Proofs`

### `ipor/plasma_vault_redeem_split/redeem_preserves_pps`
- Track / property class / proof family: `proof-only` / `pps_nondecrease` / `arithmetic_accounting`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.redeem_preserves_pps_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ipor/plasma_vault_redeem_split/verity/Contract.lean`, `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Contract.lean`
- Specification files: `cases/ipor/plasma_vault_redeem_split/verity/Specs.lean`, `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Specs.lean`
- Editable proof file: `Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks/RedeemPreservesPps.lean`
- Hidden reference solution: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Proofs`

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

### `lagoon/guardrails/exact_compliance`
- Track / property class / proof family: `proof-only` / `compliance_boundary` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lagoon.Guardrails.guardrails_exact_compliance`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lagoon/guardrails/verity/Contract.lean`, `Benchmark/Cases/Lagoon/Guardrails/Contract.lean`
- Specification files: `cases/lagoon/guardrails/verity/Specs.lean`, `Benchmark/Cases/Lagoon/Guardrails/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lagoon/Guardrails/Tasks/ExactCompliance.lean`
- Hidden reference solution: `Benchmark.Cases.Lagoon.Guardrails.Proofs`

### `lagoon/guardrails/negative_variation_bounded`
- Track / property class / proof family: `proof-only` / `compliance_boundary` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lagoon.Guardrails.guardrails_negative_bounded`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lagoon/guardrails/verity/Contract.lean`, `Benchmark/Cases/Lagoon/Guardrails/Contract.lean`
- Specification files: `cases/lagoon/guardrails/verity/Specs.lean`, `Benchmark/Cases/Lagoon/Guardrails/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lagoon/Guardrails/Tasks/NegativeVariationBounded.lean`
- Hidden reference solution: `Benchmark.Cases.Lagoon.Guardrails.Proofs`

### `lagoon/guardrails/positive_variation_bounded`
- Track / property class / proof family: `proof-only` / `compliance_boundary` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Lagoon.Guardrails.guardrails_positive_bounded`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lagoon/guardrails/verity/Contract.lean`, `Benchmark/Cases/Lagoon/Guardrails/Contract.lean`
- Specification files: `cases/lagoon/guardrails/verity/Specs.lean`, `Benchmark/Cases/Lagoon/Guardrails/Specs.lean`
- Editable proof file: `Benchmark/Generated/Lagoon/Guardrails/Tasks/PositiveVariationBounded.lean`
- Hidden reference solution: `Benchmark.Cases.Lagoon.Guardrails.Proofs`

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

### `onedelta/caller_address_integrity/delta_compose_internal_erc20_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.delta_compose_internal_erc20_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/DeltaComposeInternalErc20TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/delta_compose_internal_permit2_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.delta_compose_internal_permit2_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/DeltaComposeInternalPermit2TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/direct_erc20_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.direct_erc20_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/DirectErc20TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/direct_permit2_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.direct_permit2_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/DirectPermit2TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/flash_callback_erc20_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.flash_callback_erc20_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/FlashCallbackErc20TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/nested_flash_and_swap_callbacks_keep_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.nested_flash_and_swap_callbacks_keep_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/NestedFlashAndSwapCallbacksKeepOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/swap_callback_permit2_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.swap_callback_permit2_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/SwapCallbackPermit2TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/transfers_erc20_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.transfers_erc20_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/TransfersErc20TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/transfers_permit2_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.transfers_permit2_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/TransfersPermit2TransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

### `onedelta/caller_address_integrity/v3_callback_direct_transfer_from_uses_outer_caller`
- Track / property class / proof family: `proof-only` / `access_control_identity` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.v3_callback_direct_transferFrom_uses_outer_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/onedelta/caller_address_integrity/verity/Contract.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- Specification files: `cases/onedelta/caller_address_integrity/verity/Specs.lean`, `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/V3CallbackDirectTransferFromUsesOuterCaller.lean`
- Hidden reference solution: `Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`

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

### `piku/fund_conservation/amount_paid_preserves_fund_conservation`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Piku.FundConservation.amountPaid_preserves_fund_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/piku/fund_conservation/verity/Contract.lean`, `Benchmark/Cases/Piku/FundConservation/Contract.lean`
- Specification files: `cases/piku/fund_conservation/verity/Specs.lean`, `Benchmark/Cases/Piku/FundConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Piku/FundConservation/Tasks/AmountPaidPreservesFundConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Piku.FundConservation.Proofs`

### `piku/fund_conservation/amount_paid_records_distribution`
- Track / property class / proof family: `proof-only` / `accounting_effect` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Piku.FundConservation.amountPaid_records_distribution`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/piku/fund_conservation/verity/Contract.lean`, `Benchmark/Cases/Piku/FundConservation/Contract.lean`
- Specification files: `cases/piku/fund_conservation/verity/Specs.lean`, `Benchmark/Cases/Piku/FundConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Piku/FundConservation/Tasks/AmountPaidRecordsDistribution.lean`
- Hidden reference solution: `Benchmark.Cases.Piku.FundConservation.Proofs`

### `piku/fund_conservation/sell_order_preserves_fund_conservation`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Piku.FundConservation._sellOrder_preserves_fund_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/piku/fund_conservation/verity/Contract.lean`, `Benchmark/Cases/Piku/FundConservation/Contract.lean`
- Specification files: `cases/piku/fund_conservation/verity/Specs.lean`, `Benchmark/Cases/Piku/FundConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Piku/FundConservation/Tasks/SellOrderPreservesFundConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Piku.FundConservation.Proofs`

### `piku/fund_conservation/sell_order_records_redemption_buckets`
- Track / property class / proof family: `proof-only` / `accounting_effect` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Piku.FundConservation._sellOrder_records_redemption_buckets`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/piku/fund_conservation/verity/Contract.lean`, `Benchmark/Cases/Piku/FundConservation/Contract.lean`
- Specification files: `cases/piku/fund_conservation/verity/Specs.lean`, `Benchmark/Cases/Piku/FundConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Piku/FundConservation/Tasks/SellOrderRecordsRedemptionBuckets.lean`
- Hidden reference solution: `Benchmark.Cases.Piku.FundConservation.Proofs`

### `polaris/bonding_curve/buy_preserves_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.buy_preserves_reserve_ratio_zero_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/buy_preserves_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polaris/bonding_curve/floor_sell_and_burn_preserves_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.floor_sell_and_burn_preserves_reserve_ratio_zero_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/floor_sell_and_burn_preserves_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polaris/bonding_curve/init_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.init_reserve_ratio_zero_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/init_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polaris/bonding_curve/sell_preserves_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.sell_preserves_reserve_ratio_zero_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/sell_preserves_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polygon/agglayer_bridge/claimAsset_valid_leaf_and_consumes_unique_nullifier`
- Track / property class / proof family: `proof-only` / `authorization_state` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polygon.AgglayerBridge.claimAsset_valid_leaf_and_consumes_unique_nullifier`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polygon/agglayer_bridge/verity/Contract.lean`, `Benchmark/Cases/Polygon/AgglayerBridge/Contract.lean`
- Specification files: `cases/polygon/agglayer_bridge/verity/Specs.lean`, `Benchmark/Cases/Polygon/AgglayerBridge/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polygon/AgglayerBridge/Tasks/claimAsset_valid_leaf_and_consumes_unique_nullifier.lean`
- Hidden reference solution: `Benchmark.Cases.Polygon.AgglayerBridge.Proofs`

### `polygon/agglayer_bridge/claimMessage_valid_leaf_and_consumes_unique_nullifier`
- Track / property class / proof family: `proof-only` / `authorization_state` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polygon.AgglayerBridge.claimMessage_valid_leaf_and_consumes_unique_nullifier`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polygon/agglayer_bridge/verity/Contract.lean`, `Benchmark/Cases/Polygon/AgglayerBridge/Contract.lean`
- Specification files: `cases/polygon/agglayer_bridge/verity/Specs.lean`, `Benchmark/Cases/Polygon/AgglayerBridge/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polygon/AgglayerBridge/Tasks/claimMessage_valid_leaf_and_consumes_unique_nullifier.lean`
- Hidden reference solution: `Benchmark.Cases.Polygon.AgglayerBridge.Proofs`

### `reserve/auction_price_band/price_at_end_time`
- Track / property class / proof family: `proof-only` / `price_computation` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Reserve.AuctionPriceBand.price_at_end_time`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/reserve/auction_price_band/verity/Contract.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Contract.lean`
- Specification files: `cases/reserve/auction_price_band/verity/Specs.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/Reserve/AuctionPriceBand/Tasks/PriceAtEndTime.lean`
- Hidden reference solution: `Benchmark.Cases.Reserve.AuctionPriceBand.Proofs`

### `reserve/auction_price_band/price_at_start_time`
- Track / property class / proof family: `proof-only` / `price_computation` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Reserve.AuctionPriceBand.price_at_start_time`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/reserve/auction_price_band/verity/Contract.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Contract.lean`
- Specification files: `cases/reserve/auction_price_band/verity/Specs.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/Reserve/AuctionPriceBand/Tasks/PriceAtStartTime.lean`
- Hidden reference solution: `Benchmark.Cases.Reserve.AuctionPriceBand.Proofs`

### `reserve/auction_price_band/price_lower_bound`
- Track / property class / proof family: `proof-only` / `price_band` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Reserve.AuctionPriceBand.price_lower_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/reserve/auction_price_band/verity/Contract.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Contract.lean`
- Specification files: `cases/reserve/auction_price_band/verity/Specs.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/Reserve/AuctionPriceBand/Tasks/PriceLowerBound.lean`
- Hidden reference solution: `Benchmark.Cases.Reserve.AuctionPriceBand.Proofs`

### `reserve/auction_price_band/price_upper_bound`
- Track / property class / proof family: `proof-only` / `price_band` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Reserve.AuctionPriceBand.price_upper_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/reserve/auction_price_band/verity/Contract.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Contract.lean`
- Specification files: `cases/reserve/auction_price_band/verity/Specs.lean`, `Benchmark/Cases/Reserve/AuctionPriceBand/Specs.lean`
- Editable proof file: `Benchmark/Generated/Reserve/AuctionPriceBand/Tasks/PriceUpperBound.lean`
- Hidden reference solution: `Benchmark.Cases.Reserve.AuctionPriceBand.Proofs`

### `rootstock/flyover_quote_lifecycle/deposit_peg_out_registers_required_amount`
- Track / property class / proof family: `proof-only` / `lifecycle_accounting` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.depositPegOut_registers_required_amount`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/rootstock/flyover_quote_lifecycle/verity/Contract.lean`, `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Contract.lean`
- Specification files: `cases/rootstock/flyover_quote_lifecycle/verity/Specs.lean`, `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Specs.lean`
- Editable proof file: `Benchmark/Generated/Rootstock/FlyoverQuoteLifecycle/Tasks/DepositPegOutRegistersRequiredAmount.lean`
- Hidden reference solution: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Proofs`

### `rootstock/flyover_quote_lifecycle/refund_peg_out_conserves_quote_amount`
- Track / property class / proof family: `proof-only` / `lifecycle_accounting` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.refundPegOut_conserves_quote_amount`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/rootstock/flyover_quote_lifecycle/verity/Contract.lean`, `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Contract.lean`
- Specification files: `cases/rootstock/flyover_quote_lifecycle/verity/Specs.lean`, `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Specs.lean`
- Editable proof file: `Benchmark/Generated/Rootstock/FlyoverQuoteLifecycle/Tasks/RefundPegOutConservesQuoteAmount.lean`
- Hidden reference solution: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Proofs`

### `rootstock/flyover_quote_lifecycle/refund_user_peg_out_conserves_quote_amount`
- Track / property class / proof family: `proof-only` / `lifecycle_accounting` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.refundUserPegOut_conserves_quote_amount`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/rootstock/flyover_quote_lifecycle/verity/Contract.lean`, `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Contract.lean`
- Specification files: `cases/rootstock/flyover_quote_lifecycle/verity/Specs.lean`, `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Specs.lean`
- Editable proof file: `Benchmark/Generated/Rootstock/FlyoverQuoteLifecycle/Tasks/RefundUserPegOutConservesQuoteAmount.lean`
- Hidden reference solution: `Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Proofs`

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

### `term_finance/term_auction_clearing/clearing_assignment_correct`
- Track / property class / proof family: `proof-only` / `accounting_and_rate_guard` / `auction_clearing_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`blocked`, reference_solution=`blocked`
- Theorem target: `Benchmark.Cases.TermFinance.TermAuctionClearing.clearing_assignment_correct_task`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/term_finance/term_auction_clearing/verity/Contract.lean`, `Benchmark/Cases/TermFinance/TermAuctionClearing/Contract.lean`
- Specification files: `cases/term_finance/term_auction_clearing/verity/Specs.lean`, `Benchmark/Cases/TermFinance/TermAuctionClearing/Specs.lean`
- Editable proof file: `Benchmark/Generated/TermFinance/TermAuctionClearing/Tasks/ClearingAssignmentCorrect.lean`
- Hidden reference solution: `Benchmark.Cases.TermFinance.TermAuctionClearing.Proofs`

### `termmax/order_v2_buy_xt_single_segment/swap_debt_token_to_xt_updates_virtual_xt_reserve`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.swapDebtTokenToXt_updates_virtual_xt_reserve`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/termmax/order_v2_buy_xt_single_segment/verity/Contract.lean`, `Benchmark/Cases/TermMax/OrderV2BuyXtSingleSegment/Contract.lean`
- Specification files: `cases/termmax/order_v2_buy_xt_single_segment/verity/Specs.lean`, `Benchmark/Cases/TermMax/OrderV2BuyXtSingleSegment/Specs.lean`
- Editable proof file: `Benchmark/Generated/TermMax/OrderV2BuyXtSingleSegment/Tasks/SwapDebtTokenToXtUpdatesVirtualXtReserve.lean`
- Hidden reference solution: `Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Proofs`

### `usual/dao_collateral/redeem_conservation`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Usual.DaoCollateral.redeem_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/usual/dao_collateral/verity/Contract.lean`, `Benchmark/Cases/Usual/DaoCollateral/Contract.lean`
- Specification files: `cases/usual/dao_collateral/verity/Specs.lean`, `Benchmark/Cases/Usual/DaoCollateral/Specs.lean`
- Editable proof file: `Benchmark/Generated/Usual/DaoCollateral/Tasks/RedeemConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Usual.DaoCollateral.Proofs`

### `usual/dao_collateral/redeem_fee_formula`
- Track / property class / proof family: `proof-only` / `arithmetic_rounding` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Usual.DaoCollateral.redeem_fee_formula`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/usual/dao_collateral/verity/Contract.lean`, `Benchmark/Cases/Usual/DaoCollateral/Contract.lean`
- Specification files: `cases/usual/dao_collateral/verity/Specs.lean`, `Benchmark/Cases/Usual/DaoCollateral/Specs.lean`
- Editable proof file: `Benchmark/Generated/Usual/DaoCollateral/Tasks/RedeemFeeFormula.lean`
- Hidden reference solution: `Benchmark.Cases.Usual.DaoCollateral.Proofs`

### `usual/dao_collateral/redeem_return_formula`
- Track / property class / proof family: `proof-only` / `arithmetic_rounding` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Usual.DaoCollateral.redeem_return_formula`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/usual/dao_collateral/verity/Contract.lean`, `Benchmark/Cases/Usual/DaoCollateral/Contract.lean`
- Specification files: `cases/usual/dao_collateral/verity/Specs.lean`, `Benchmark/Cases/Usual/DaoCollateral/Specs.lean`
- Editable proof file: `Benchmark/Generated/Usual/DaoCollateral/Tasks/RedeemReturnFormula.lean`
- Hidden reference solution: `Benchmark.Cases.Usual.DaoCollateral.Proofs`

### `usual/dao_collateral/swap_conservation`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Usual.DaoCollateral.swap_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/usual/dao_collateral/verity/Contract.lean`, `Benchmark/Cases/Usual/DaoCollateral/Contract.lean`
- Specification files: `cases/usual/dao_collateral/verity/Specs.lean`, `Benchmark/Cases/Usual/DaoCollateral/Specs.lean`
- Editable proof file: `Benchmark/Generated/Usual/DaoCollateral/Tasks/SwapConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Usual.DaoCollateral.Proofs`

### `usual/dao_collateral/swap_value_conservation`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Usual.DaoCollateral.swap_value_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/usual/dao_collateral/verity/Contract.lean`, `Benchmark/Cases/Usual/DaoCollateral/Contract.lean`
- Specification files: `cases/usual/dao_collateral/verity/Specs.lean`, `Benchmark/Cases/Usual/DaoCollateral/Specs.lean`
- Editable proof file: `Benchmark/Generated/Usual/DaoCollateral/Tasks/SwapValueConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Usual.DaoCollateral.Proofs`

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

### `zama/erc7984_confidential_token/mint_ctokens_match_deposit`
- Track / property class / proof family: `proof-only` / `deposit_mint_exactness` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_ctokens_match_deposit`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama/erc7984_confidential_token/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Contract.lean`
- Specification files: `cases/zama/erc7984_confidential_token/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984ConfidentialToken/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984ConfidentialToken/Tasks/MintCTokensMatchDeposit.lean`
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

### `zodiac/roles_decoder_faithfulness/metadata_bridge`
- Track / property class / proof family: `proof-only` / `calldata_decoder_metadata` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.metadata_bridge`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zodiac/roles_decoder_faithfulness/verity/Contract.lean`, `Benchmark/Cases/Zodiac/RolesDecoderFaithfulness/Contract.lean`
- Specification files: `cases/zodiac/roles_decoder_faithfulness/verity/Specs.lean`, `Benchmark/Cases/Zodiac/RolesDecoderFaithfulness/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zodiac/RolesDecoderFaithfulness/Tasks/MetadataBridge.lean`
- Hidden reference solution: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Proofs`

### `zodiac/roles_decoder_faithfulness/roles_decoder_bounds_safe`
- Track / property class / proof family: `proof-only` / `calldata_decoder_bounds` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.roles_decoder_bounds_safe`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zodiac/roles_decoder_faithfulness/verity/Contract.lean`, `Benchmark/Cases/Zodiac/RolesDecoderFaithfulness/Contract.lean`
- Specification files: `cases/zodiac/roles_decoder_faithfulness/verity/Specs.lean`, `Benchmark/Cases/Zodiac/RolesDecoderFaithfulness/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zodiac/RolesDecoderFaithfulness/Tasks/RolesDecoderBoundsSafe.lean`
- Hidden reference solution: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Proofs`

### `zodiac/roles_decoder_faithfulness/roles_decoder_faithful`
- Track / property class / proof family: `proof-only` / `calldata_decoder_faithfulness` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.roles_decoder_faithful`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zodiac/roles_decoder_faithfulness/verity/Contract.lean`, `Benchmark/Cases/Zodiac/RolesDecoderFaithfulness/Contract.lean`
- Specification files: `cases/zodiac/roles_decoder_faithfulness/verity/Specs.lean`, `Benchmark/Cases/Zodiac/RolesDecoderFaithfulness/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zodiac/RolesDecoderFaithfulness/Tasks/RolesDecoderFaithful.lean`
- Hidden reference solution: `Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Proofs`

## Backlog

### `openzeppelin/erc4626_virtual_offset_deposit`
- Family / implementation: `openzeppelin` / `contracts`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Compile`
- Source ref: `https://github.com/OpenZeppelin/openzeppelin-contracts@45f032d1bcf1a88b7bc90154d7eef76c87bf9d45:contracts/token/ERC20/extensions/ERC4626.sol`
- Selected functions: `previewDeposit`, `deposit`
- Upstream source artifact: `contracts/token/ERC20/extensions/ERC4626.sol`
- Notes: Backlog ERC-4626 benchmark slice derived from OpenZeppelin's virtual-offset design and inflation-attack analysis. The committed proof module validates the four arithmetic and state-transition theorems, so the case is runnable in the reference-solution benchmark path while remaining backlog-scoped.

### `uniswap_v2/pair_fee_adjusted_swap`
- Family / implementation: `uniswap_v2` / `v2_core`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Compile`
- Source ref: `https://github.com/Uniswap/v2-core@ee547b17853e71ed4e0101ccfd52e70d5acded58:contracts/UniswapV2Pair.sol`
- Selected functions: `swap`
- Upstream source artifact: `contracts/UniswapV2Pair.sol`
- Notes: Backlog AMM benchmark slice for reasoning about fee-adjusted constant-product guards and post-swap reserve synchronization without exposing the full Uniswap execution path. The committed proof module makes the case runnable in the reference-solution benchmark path while it remains backlog-scoped.

### `usual/placeholder`
- Family / implementation: `usual` / `private_repo`
- Stage: `candidate`
- Status dimensions: translation=`blocked`, spec=`not_started`, proof=`blocked`
- Failure reason: `private_access`
- Source ref: `unresolved:usual/private_repo@unknown:TBD`
- Upstream source artifact: `TBD`
- Notes: Pending private repository access and target selection.

## Commands

- Validate manifests: `python3 scripts/validate_manifests.py`
- Regenerate metadata: `python3 scripts/generate_metadata.py`
- Run one task: `./scripts/run_task.sh <project/case_id/task_id>`
- Run one case: `./scripts/run_case.sh <project/case_id>`
- Run active suite: `./scripts/run_all.sh`
- Run repo check: `./scripts/check.sh`
