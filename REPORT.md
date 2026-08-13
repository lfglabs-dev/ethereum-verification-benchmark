# Benchmark report

This report is generated from the benchmark manifests.

## Summary

- Families: 41
- Implementations: 42
- Active cases: 41
- Buildable active cases: 41
- Active tasks: 263
- Backlog cases: 1

## Buildable active cases

### `1inch/xycswap_curve_safety`
- Family / implementation: `1inch` / `aqua_xycswap`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.OneInch.XYCSwapCurveSafety.Compile`
- Source ref: `https://github.com/1inch/aqua@81c26e4619ce21556ab02b3284ee2685de21fb18:examples/apps/XYCSwap.sol`
- Selected functions: `_quoteExactIn`, `swapExactIn`
- Upstream source artifact: `examples/apps/XYCSwap.sol`
- Notes: Benchmark case proving the fee-adjusted constant-product curve safety invariant for 1inch Aqua XYCSwap. The theorem states that the output amount computed by _quoteExactIn satisfies the integer-division rounding bound: output * denominator <= feeAdjustedInput * balanceOut. This is the direct analog of the Uniswap V2 K invariant, adapted to XYCSwap's basis-points fee structure.

### `alchemix/earmark_conservation`
- Family / implementation: `alchemix` / `v3`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Alchemix.EarmarkConservation.Compile`
- Source ref: `https://github.com/alchemix-finance/v3@117c95b6ee11a75221d6fbdc79f16ac6acdb96f5:src/AlchemistV3.sol`
- Selected functions: `_earmark`, `_sync`, `_computeUnrealizedAccount`, `redeem`, `_subEarmarkedDebt`, `_subDebt`
- Upstream source artifact: `src/AlchemistV3.sol`
- Notes: Earmark conservation invariant for Alchemix V3 lazy-accrual debt accounting. The literal "sum of stored account.earmarked equals cumulativeEarmarked" is provably false on the deployed code (see AlchemistV3.sol:1014 comment "Global can lag local by rounding") because per-account earmarked is updated lazily inside _sync(tokenId). The lazy-projected version proven here is the property the design actually maintains and that downstream consumers (redemption math, collateral debit) rely on.

### `aragon_osx/execute_authorization`
- Family / implementation: `aragon_osx` / `osx-dao`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Compile`
- Source ref: `https://github.com/aragon/osx@daf4fbb06b89ab0a05516bccb70b625a1a38303b:src/core/dao/DAO.sol`
- Selected functions: `DAO.execute`, `PermissionManager.isGranted`, `PermissionManager._auth`, `PermissionManager.grant`, `PermissionManager.grantWithCondition`, `PermissionManager.revoke`
- Upstream source artifact: `src/core/dao/DAO.sol`
- Notes: This is an authorization benchmark, not an action-execution correctness benchmark. A successful execute reaches the modeled execute-body boundary only after exact permission resolution. Action calldata, native-value transfers, allowFailureMap handling, result hashing, events, and reentrancy are outside the theorem scope. DAO.sol is the primary case source. Its inherited authorization path is pinned at src/core/permission/PermissionManager.sol in the same upstream commit and is the source for isGranted, _auth, grant, grantWithCondition, and revoke.

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

### `enzyme/onyx_fee_handler`
- Family / implementation: `enzyme` / `onyx_fee_handler`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Enzyme.OnyxFeeHandler.Compile`
- Source ref: `https://github.com/enzymefinance/protocol-onyx@8ae6f589b13a19d8390eb0956836c6a9f48fadab:src/components/fees/FeeHandler.sol`
- Selected functions: `settleDynamicFeesGivenPositionsValue`, `__increaseValueOwed`, `__updateValueOwed`, `settleManagementFee`, `settlePerformanceFee`
- Upstream source artifact: `src/components/fees/FeeHandler.sol`
- Notes: Proves with no custom axioms and no sorry/admit that a successful settlement with both dynamic trackers enabled uses the configured targets and exact management-then-performance calldata, increases total fees owed by exactly both arbitrary returned amounts, credits the configured recipients, handles recipient aliasing, and frames the selected dynamic-fee configuration projection. The arbitrary reentry hook may mutate all other state. The pinned FeeHandler has no reentrancy guard, so the projection-stability condition is an explicit deployment/callee rely condition, not a proved runtime source property. Separate theorems cover successful management-only, performance-only, and both-disabled branches plus transactional rollback for every modeled raw revert. Official onyx-sdk metadata independently identifies LIVE Ethereum v1 implementation addresses; it does not establish bytecode equivalence to the pinned protocol source commit.

### `erc4337/entry_point_invariant`
- Family / implementation: `erc4337` / `erc4337_v09`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.ERC4337.EntryPointInvariant.Compile`
- Source ref: `https://github.com/eth-infinitism/account-abstraction@b36a1ed52ae00da6f8a4c8d50181e2877e4fa410:contracts/core/EntryPoint.sol`
- Selected functions: `handleOps`, `_iterateValidationPhase`, `_executeUserOp`
- Upstream source artifact: `contracts/core/EntryPoint.sol`
- Notes: ERC-4337 EntryPoint control-flow invariant slice: the operation execution path is reached if and only if validation passed. This is not a full proof of arbitrary account/paymaster EVM behavior or `innerHandleOp` calldata effects; it proves the selected two-loop model for all possible validation outcomes.

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

### `hypernova/settled_payout_safety`
- Family / implementation: `hypernova` / `arbitrum-deployment`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Hypernova.SettledPayoutSafety.Compile`
- Source ref: `https://arbitrum.blockscout.com/address/0x429d8f223acb622e5e748f6a7bdf1235b2334fcb?tab=contract`
- Selected functions: `requestPayout`, `_executePayout`, `processPayout`
- Upstream source artifact: `TradingAccounts.sol + Vault.sol`
- Notes: The theorem proves on-chain accounting after canWithdraw is already true. It does not independently model getMaxWithdrawable or updateEquityAndSettle, nor prove off-chain P&L, flat-position detection, daily caps, owner honesty, proxy immutability, or reserve sufficiency beyond the actual trader transfer. Verified source SHA-256 values are recorded in the accompanying case-study research artifacts.

### `ipor/plasma_vault_redeem_split`
- Family / implementation: `ipor` / `ipor_fusion`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Compile`
- Source ref: `https://github.com/IPOR-Labs/ipor-fusion@3a83157ee75a7c1752d9151aff43eb92a50cb346:contracts/vaults/PlasmaVault.sol`
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

### `kyberswap/partial_fill_price_floor`
- Family / implementation: `kyberswap` / `meta-aggregation-router-v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.KyberSwap.PartialFillPriceFloor.Compile`
- Source ref: `https://www.codeslaw.app/contracts/ethereum/0x6131b5fae19ea4f9d964eac0408e4408b66337b5@verified-source-0x6131b5fae19ea4f9d964eac0408e4408b66337b5:contracts/MetaAggregationRouterV2.sol`
- Selected functions: `_checkReturnAmount`
- Upstream source artifact: `contracts/MetaAggregationRouterV2.sol`
- Notes: Helper-level proof only. The public paths compute `spentAmount` and `returnAmount` before calling `_checkReturnAmount`; this case proves the helper enforces the checked scaled inequality for successful partial-fill helper execution. Reading the guard as an effective-price floor additionally assumes `spentAmount <= amount`, which the helper does not enforce and the theorem does not assume.

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

### `lifi/swap_atomicity`
- Family / implementation: `lifi` / `contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.LiFi.SwapAtomicity.Compile`
- Source ref: `https://github.com/lifinance/contracts@62bed68d9ba6cd3cd7b92e917f2c47531b20f75d:src/Facets/GenericSwapFacet.sol`
- Selected functions: `GenericSwapFacet.swapTokensGeneric`, `SwapperV2._depositAndSwap`, `SwapperV2._executeSwaps`, `LibSwap.swap`, `LibAsset.depositAssets`, `LibUtil.revertWith`
- Upstream source artifact: `src/Facets/GenericSwapFacet.sol`
- Notes: This is an atomicity benchmark, not a price-quality or route-optimality benchmark. It proves that the modeled LI.FI route cannot commit a public final transfer unless every modeled public-route gate succeeds, every modeled route step succeeds, and the output amount meets the minimum.

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

### `openzeppelin/erc4626_virtual_offset_deposit`
- Family / implementation: `openzeppelin` / `contracts`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Compile`
- Source ref: `https://github.com/OpenZeppelin/openzeppelin-contracts@45f032d1bcf1a88b7bc90154d7eef76c87bf9d45:contracts/token/ERC20/extensions/ERC4626.sol`
- Selected functions: `previewDeposit`, `previewRedeem`, `deposit`
- Upstream source artifact: `contracts/token/ERC20/extensions/ERC4626.sol`
- Notes: Active ERC-4626 benchmark slice derived from OpenZeppelin's virtual-offset design and inflation-attack analysis. The committed proof module validates the four original arithmetic and state-transition theorems plus the two harder rounding tasks (deposit/redeem round-trip bound and share-price monotonicity under donation), so every task is runnable in the reference-solution benchmark path.

### `paladin_votes/stream_recovery_claim_usdc`
- Family / implementation: `paladin_votes` / `stream_recovery_claim`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Compile`
- Source ref: `https://github.com/Figu3/sonic-earn-recovery-system@699cbbc79def374cab9739e451acbbf866293d12:src/StreamRecoveryClaim.sol`
- Selected functions: `claimUsdc`, `_claimUsdc`, `claimWeth`, `_claimWeth`, `claimBoth`
- Upstream source artifact: `src/StreamRecoveryClaim.sol`
- Notes: Single-round accounting slice of the full USDC/WETH claim surface, including `claimBoth`. Merkle verification is abstracted as a boolean witness and token transfer side effects are omitted.

### `pareto/redemption_backing`
- Family / implementation: `pareto` / `usp`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Pareto.RedemptionBacking.Compile`
- Source ref: `https://github.com/pareto-credit/USP@2cb0a098c7ccb9813497ef3982d78c44a596c87b:src/ParetoDollarQueue.sol`
- Selected functions: `depositFunds`
- Upstream source artifact: `src/ParetoDollarQueue.sol`
- Notes: Reference proof is complete for the modeled successful depositFunds path under the source reserve require (`hReserveGuard`) and checked-arithmetic side conditions: the resulting state satisfies the closed-epoch reserve guard.

### `pendle/py_supply_pairing`
- Family / implementation: `pendle` / `core_v2_public`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Pendle.PySupplyPairing.Compile`
- Source ref: `https://github.com/pendle-finance/pendle-core-v2-public@e8c2cca4c9b329ba8a383a27d7318e5f8b35c843:contracts/core/YieldContracts/PendleYieldToken.sol`
- Selected functions: `PendleYieldToken.mintPY`, `PendleYieldToken._mintPY`, `PendleYieldToken.redeemPY`, `PendleYieldToken._redeemPY`, `PendleYieldToken._getAmountPYToRedeem`, `PendlePrincipalToken.mintByYT`, `PendlePrincipalToken.burnByYT`, `SYUtils.syToAsset`, `SYUtils.assetToSy`
- Upstream source artifact: `contracts/core/YieldContracts/PendleYieldToken.sol`
- Notes: Proves that successful mintPY and successful pre-expiry redeemPY preserve the equality of PT and YT total supplies when that pairing held before the call. Post-expiry redeem is intentionally excluded from the preservation theorem because Pendle burns PT but not YT after maturity.

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
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
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

### `starkware/starkgate_escrow`
- Family / implementation: `starkware` / `starkgate_bridge`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Starkware.StarkgateEscrow.Compile`
- Source ref: `https://github.com/starknet-io/starkgate-contracts@07e11c39119a10d5742735be5b1d51894ebf5311:src/solidity/StarknetTokenBridge.sol`
- Selected functions: `deposit`, `withdraw`, `depositReclaim`
- Upstream source artifact: `src/solidity/StarknetTokenBridge.sol`
- Notes: Reference proofs are complete for the escrow lower-bound invariant across the three modeled transitions (deposit, withdraw, depositReclaim). Arithmetic hypotheses expose Solidity checked-arithmetic obligations (no-overflow on additions, sufficient-balance on subtractions).

### `superfluid/realtime_balance_conservation`
- Family / implementation: `superfluid` / `cfa_realtime_accounting`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Compile`
- Source ref: `https://github.com/superfluid-finance/protocol-monorepo@414109689d9041a8b6900b67b947f3f203c1da5d:packages/ethereum-contracts/contracts/agreements/ConstantFlowAgreementV1.sol`
- Selected functions: `SuperfluidToken.realtimeBalanceOf`, `ConstantFlowAgreementV1._createFlow`, `ConstantFlowAgreementV1._updateFlow`, `ConstantFlowAgreementV1._deleteFlow`, `ConstantFlowAgreementV1._changeFlowToNonApp`, `ConstantFlowAgreementV1._changeFlowToApp`, `ConstantFlowAgreementV1._changeFlow`, `ConstantFlowAgreementV1._updateAccountFlowState`, `SelfDeletingFlowTestApp.afterAgreementCreated`, `Superfluid.callAgreementWithContext`, `Superfluid._updateContext`
- Upstream source artifact: `packages/ethereum-contracts/contracts/agreements/ConstantFlowAgreementV1.sol`
- Notes: This case does not prove SuperToken supply conservation and does not equate its modulo-2^256 CFA projection sum to native `realtimeBalanceOf` outside the stated relation. All 22 task declarations have kernel-checked reference proofs, including the nine finite-global, future-time, callback-composition, rollback, and concrete factored-instance strengthening tasks. Translation fidelity is an audited trust boundary, separate from the kernel-checked Lean proof of the model.

### `t3tris/hwm_performance_fee`
- Family / implementation: `t3tris` / `t3tris_vault`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.T3tris.HwmPerformanceFee.Compile`
- Source ref: `https://github.com/t3tris-finance/T3tris-Vault@89ad64a8e945214cd40a18db146e1feed83e417f:src/libraries/feature/FeatureFeesLib.sol`
- Selected functions: `FeatureFeesLib._computeLastPeriodFeesAndUpdateResult`, `ReleaseFeesLib.computeAndRecordAccruedFees`, `FeatureSettlementLib._updateSettlementValues`
- Upstream source artifact: `src/libraries/feature/FeatureFeesLib.sol`
- Notes: This case targets the coverage gap not present in Cyfrin's T3tris suite: structural HWM facts are already proved, but the multi-step economic property that recovery up to the fee-accounted HWM charges no second performance fee is not.

### `term_finance/term_auction_clearing`
- Family / implementation: `term_finance` / `term_finance_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.TermFinance.TermAuctionClearing.Compile`
- Source ref: `https://github.com/term-finance/term-finance-contracts@127b74d871fc74e3a03d6d3b0f1fafe7e5d10275:contracts/TermAuction.sol`
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

### `uniswap_v2/pair_fee_adjusted_swap`
- Family / implementation: `uniswap_v2` / `v2_core`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Compile`
- Source ref: `https://github.com/Uniswap/v2-core@ee547b17853e71ed4e0101ccfd52e70d5acded58:contracts/UniswapV2Pair.sol`
- Selected functions: `swap`
- Upstream source artifact: `contracts/UniswapV2Pair.sol`
- Notes: Active AMM benchmark slice for reasoning about fee-adjusted constant-product guards and post-swap reserve synchronization without exposing the full Uniswap execution path. Promoted from the backlog with complete hidden reference proofs, plus harder multi-swap monotonicity and sandwich output-bound tasks layered on the same slice.

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

### `yo_protocol/async_redemption_escrow`
- Family / implementation: `yo_protocol` / `core_v2`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Compile`
- Source ref: `https://github.com/yoprotocol/core-v2@7b023145cc99bc424e57ffa554584c609a1ecb30:src/YoVault.sol`
- Selected functions: `YoVault.requestRedeem`, `YoVault.redeem`, `YoVault.fulfillRedeem`, `YoVault.cancelRedeem`, `YoVault.updateWithdrawFee`, `YoVault.updateFeeRecipient`, `YoVault._withdraw`, `YoVault._getAvailableBalance`, `AuthUpgradeable.isAuthorized`
- Upstream source artifact: `src/YoVault.sol`
- Notes: The reviewed case has 14 generated theorem interfaces, all version 2, with matching proof-complete reference declarations. Independent Phase 2 and Phase 3 review gates passed. The deployment context is Base yoUSD at block 48,628,300 as recorded in Phase 1; this case proves the pinned source lifecycle, not the snapshot's current configuration.

### `zama/erc7984_confidential_token`
- Family / implementation: `zama` / `confidential_contracts`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`partial`
- Lean target: `Benchmark.Cases.Zama.ERC7984ConfidentialToken.Compile`
- Source ref: `https://github.com/OpenZeppelin/openzeppelin-confidential-contracts@83364738f0d2b1655c60627588e3493099c359f7:contracts/token/ERC7984/ERC7984.sol`
- Selected functions: `_update`, `_transfer`, `_mint`, `_burn`, `confidentialTransferFrom`, `setOperator`
- Upstream source artifact: `contracts/token/ERC7984/ERC7984.sol`
- Notes: ERC-7984 is the confidential fungible token standard co-developed by Zama and OpenZeppelin for the fhEVM. The key verification targets are balance conservation (no tokens created/destroyed by transfers), correctness of the FHE.select pattern (insufficient balance → silent 0-transfer instead of revert), mint/burn accounting, overflow protection via FHESafeMath.tryIncrease, operator-gated transferFrom, functional correctness of setOperator, and the exact match between successful deposits and credited confidential tokens. Twelve proof tasks cover the 5 modeled functions.

### `zama_protocol_apps/erc7984_upgradeable_exact_source`
- Family / implementation: `zama_protocol_apps` / `protocol_apps_confidential_wrapper`
- Stage: `proof_complete`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`complete`
- Lean target: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Compile`
- Source ref: `https://github.com/zama-ai/protocol-apps@2f88eef1d0b545438b1f74e21cdff7ea771805da:contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol`
- Selected functions: `_update`, `_transfer`, `confidentialTransfer`
- Upstream source artifact: `contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol`
- Notes: Distinct exact-source Zama protocol-apps case. Four complete reference proofs establish, under explicit euint64-domain hypotheses: uninitialized senders return the modeled ERC7984ZeroBalance error class with unchanged modeled accounting state even for amount zero; initialized senders do not balance-revert after explicit wrapper and plaintext guards pass; insufficient initialized transfers return zero and preserve the two distinct parties' plaintext-equivalent balances; and distinct-party pair accounting is conserved when destination addition cannot wrap for the amount actually transferred. The revert proof does not model custom-error payload/returndata or full EVM/FHE/global state. Generated task modules keep explicit `exact ?_` placeholders for benchmark evaluation. The separate retained OpenZeppelin case `zama/erc7984_confidential_token` at commit 83364738f0d2b1655c60627588e3493099c359f7 remains unchanged.

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

### `1inch/xycswap_curve_safety/quote_exact_in_curve_safety`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OneInch.XYCSwapCurveSafety.quoteExactIn_curve_safety`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/1inch/xycswap_curve_safety/verity/Contract.lean`, `Benchmark/Cases/OneInch/XYCSwapCurveSafety/Contract.lean`
- Specification files: `cases/1inch/xycswap_curve_safety/verity/Specs.lean`, `Benchmark/Cases/OneInch/XYCSwapCurveSafety/Specs.lean`
- Editable proof file: `Benchmark/Generated/OneInch/XYCSwapCurveSafety/Tasks/QuoteExactInCurveSafety.lean`
- Hidden reference solution: `Benchmark.Cases.OneInch.XYCSwapCurveSafety.Proofs`

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

### `aragon_osx/execute_authorization/execute_success_implies_authorized`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.execute_success_implies_authorized`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/ExecuteSuccessImpliesAuthorized.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_execute_condition_rejects_wildcard_caller`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_execute_condition_rejects_wildcard_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantExecuteConditionRejectsWildcardCaller.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_execute_condition_rejects_wildcard_target`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_execute_condition_rejects_wildcard_target`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantExecuteConditionRejectsWildcardTarget.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_execute_rejects_wildcard_caller`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_execute_rejects_wildcard_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantExecuteRejectsWildcardCaller.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_execute_rejects_wildcard_target`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_execute_rejects_wildcard_target`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantExecuteRejectsWildcardTarget.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_execute_requires_root`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_execute_requires_root`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantExecuteRequiresRoot.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_execute_with_condition_requires_root`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_execute_with_condition_requires_root`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantExecuteWithConditionRequiresRoot.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_root_condition_rejects_wildcard_caller`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_root_condition_rejects_wildcard_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantRootConditionRejectsWildcardCaller.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_root_condition_rejects_wildcard_target`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_root_condition_rejects_wildcard_target`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantRootConditionRejectsWildcardTarget.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_root_rejects_wildcard_caller`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_root_rejects_wildcard_caller`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantRootRejectsWildcardCaller.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_root_rejects_wildcard_target`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_root_rejects_wildcard_target`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantRootRejectsWildcardTarget.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_root_requires_root`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_root_requires_root`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantRootRequiresRoot.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/grant_root_with_condition_requires_root`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.grant_root_with_condition_requires_root`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/GrantRootWithConditionRequiresRoot.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/revoke_execute_requires_root`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.revoke_execute_requires_root`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/RevokeExecuteRequiresRoot.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/revoke_root_requires_root`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.revoke_root_requires_root`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/RevokeRootRequiresRoot.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

### `aragon_osx/execute_authorization/specific_condition_denial_is_terminal`
- Track / property class / proof family: `proof-only` / `access_control_authorization` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.specific_condition_denial_is_terminal`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/aragon_osx/execute_authorization/verity/Contract.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Contract.lean`
- Specification files: `cases/aragon_osx/execute_authorization/verity/Specs.lean`, `Benchmark/Cases/AragonOSx/ExecuteAuthorization/Specs.lean`
- Editable proof file: `Benchmark/Generated/AragonOSx/ExecuteAuthorization/Tasks/SpecificConditionDenialIsTerminal.lean`
- Hidden reference solution: `Benchmark.Cases.AragonOSx.ExecuteAuthorization.Proofs`

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

### `enzyme/onyx_fee_handler/settle_dynamic_fees_exact_accounting`
- Track / property class / proof family: `proof-only` / `cross_contract_fee_accounting` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Enzyme.OnyxFeeHandler.settleDynamicFeesGivenPositionsValue_exact_accounting`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/enzyme/onyx_fee_handler/verity/Contract.lean`, `Benchmark/Cases/Enzyme/OnyxFeeHandler/Contract.lean`
- Specification files: `cases/enzyme/onyx_fee_handler/verity/Specs.lean`, `Benchmark/Cases/Enzyme/OnyxFeeHandler/Specs.lean`
- Editable proof file: `Benchmark/Generated/Enzyme/OnyxFeeHandler/Tasks/settle_dynamic_fees_exact_accounting.lean`
- Hidden reference solution: `Benchmark.Cases.Enzyme.OnyxFeeHandler.Proofs`

### `erc4337/entry_point_invariant/account_rejection_reverts`
- Track / property class / proof family: `proof-only` / `authority_required` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.account_rejection_reverts`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/AccountRejectionReverts.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/all_executed_on_success`
- Track / property class / proof family: `proof-only` / `batch_completeness` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.all_executed_on_success`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/AllExecutedOnSuccess.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/all_validated_on_success`
- Track / property class / proof family: `proof-only` / `batch_completeness` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.all_validated_on_success`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/AllValidatedOnSuccess.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/beneficiary_eq_total_prefund`
- Track / property class / proof family: `proof-only` / `fee_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.beneficiary_eq_total_prefund`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/BeneficiaryEqTotalPrefund.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/count_executed_eq_validated`
- Track / property class / proof family: `proof-only` / `counting_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.count_executed_eq_validated`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/CountExecutedEqValidated.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/executed_index_in_bounds`
- Track / property class / proof family: `proof-only` / `bounds_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.executed_index_in_bounds`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ExecutedIndexInBounds.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/execution_iff_validation`
- Track / property class / proof family: `proof-only` / `biconditional_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.execution_iff_validation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ExecutionIffValidation.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/execution_implies_validation`
- Track / property class / proof family: `proof-only` / `safety_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.execution_implies_validation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ExecutionImpliesValidation.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/execution_independent_of_inner_revert`
- Track / property class / proof family: `proof-only` / `independence_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.execution_independent_of_inner_revert`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ExecutionIndependentOfInnerRevert.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/execution_length_eq_validation_length`
- Track / property class / proof family: `proof-only` / `length_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.execution_length_eq_validation_length`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ExecutionLengthEqValidationLength.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/execution_r_iff_in_bounds`
- Track / property class / proof family: `proof-only` / `biconditional_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.executionR_iff_in_bounds`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ExecutionRIffInBounds.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/fees_collected_eq_ops_length`
- Track / property class / proof family: `proof-only` / `fee_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.fees_collected_eq_ops_length`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/FeesCollectedEqOpsLength.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/fees_concat_additive`
- Track / property class / proof family: `proof-only` / `fee_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.fees_concat_additive`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/FeesConcatAdditive.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/full_success_implies_all_account_approved`
- Track / property class / proof family: `proof-only` / `safety_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.full_success_implies_all_account_approved`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/FullSuccessImpliesAllAccountApproved.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/handle_ops_deterministic`
- Track / property class / proof family: `proof-only` / `functional_property` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.handleOps_deterministic`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/HandleOpsDeterministic.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/handle_ops_empty`
- Track / property class / proof family: `proof-only` / `base_case_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.handleOps_empty`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/HandleOpsEmpty.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/no_beneficiary_payout_on_revert`
- Track / property class / proof family: `proof-only` / `fee_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.no_beneficiary_payout_on_revert`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/NoBeneficiaryPayoutOnRevert.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/no_execution_on_revert`
- Track / property class / proof family: `proof-only` / `revert_safety` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.no_execution_on_revert`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/NoExecutionOnRevert.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/no_fees_on_revert`
- Track / property class / proof family: `proof-only` / `fee_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.no_fees_on_revert`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/NoFeesOnRevert.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/nonce_advances_by_batch_size`
- Track / property class / proof family: `proof-only` / `nonce_monotonicity` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.nonce_advances_by_batch_size`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/NonceAdvancesByBatchSize.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/nonce_mismatch_reverts`
- Track / property class / proof family: `proof-only` / `replay_protection` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.nonce_mismatch_reverts`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/NonceMismatchReverts.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/nonce_strictly_increases`
- Track / property class / proof family: `proof-only` / `replay_protection` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.nonce_strictly_increases`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/NonceStrictlyIncreases.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/paymaster_irrelevant_when_absent`
- Track / property class / proof family: `proof-only` / `scope_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.paymaster_irrelevant_when_absent`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/PaymasterIrrelevantWhenAbsent.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/paymaster_rejection_reverts_when_present`
- Track / property class / proof family: `proof-only` / `authority_required` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.paymaster_rejection_reverts_when_present`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/PaymasterRejectionRevertsWhenPresent.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/sender_call_iff_validated_and_calldata`
- Track / property class / proof family: `proof-only` / `biconditional_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.sender_call_iff_validated_and_calldata`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/SenderCallIffValidatedAndCalldata.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/single_failure_reverts`
- Track / property class / proof family: `proof-only` / `all_or_nothing` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.single_failure_reverts`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/SingleFailureReverts.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/single_op_execution_on_validation`
- Track / property class / proof family: `proof-only` / `storage_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.single_op_execution_on_validation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/SingleOpExecutionOnValidation.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/single_op_fee_collected`
- Track / property class / proof family: `proof-only` / `storage_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.single_op_fee_collected`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/SingleOpFeeCollected.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/total_prefund_concat`
- Track / property class / proof family: `proof-only` / `additivity` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.total_prefund_concat`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/TotalPrefundConcat.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/validation_concat`
- Track / property class / proof family: `proof-only` / `composition_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.validation_concat`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ValidationConcat.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/validation_concat_fail_left`
- Track / property class / proof family: `proof-only` / `failure_propagation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.validation_concat_fail_left`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ValidationConcatFailLeft.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/validation_concat_fail_right`
- Track / property class / proof family: `proof-only` / `failure_propagation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.validation_concat_fail_right`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ValidationConcatFailRight.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

### `erc4337/entry_point_invariant/validation_implies_execution`
- Track / property class / proof family: `proof-only` / `liveness_invariant` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.ERC4337.EntryPointInvariant.validation_implies_execution`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/erc4337/entry_point_invariant/verity/Contract.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Contract.lean`
- Specification files: `cases/erc4337/entry_point_invariant/verity/Specs.lean`, `Benchmark/Cases/ERC4337/EntryPointInvariant/Specs.lean`
- Editable proof file: `Benchmark/Generated/ERC4337/EntryPointInvariant/Tasks/ValidationImpliesExecution.lean`
- Hidden reference solution: `Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs`

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

### `hypernova/settled_payout_safety/successful_payout_never_overpays`
- Track / property class / proof family: `proof-only` / `payout_safety` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Hypernova.SettledPayoutSafety.successfulPayout_never_overpays`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/hypernova/settled_payout_safety/verity/Contract.lean`, `Benchmark/Cases/Hypernova/SettledPayoutSafety/Contract.lean`
- Specification files: `cases/hypernova/settled_payout_safety/verity/Specs.lean`, `Benchmark/Cases/Hypernova/SettledPayoutSafety/Specs.lean`
- Editable proof file: `Benchmark/Generated/Hypernova/SettledPayoutSafety/Tasks/SuccessfulPayoutNeverOverpays.lean`
- Hidden reference solution: `Benchmark.Cases.Hypernova.SettledPayoutSafety.Proofs`

### `hypernova/settled_payout_safety/valid_settled_payout_is_safe`
- Track / property class / proof family: `proof-only` / `payout_safety` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Hypernova.SettledPayoutSafety.validSettledPayout_is_safe`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/hypernova/settled_payout_safety/verity/Contract.lean`, `Benchmark/Cases/Hypernova/SettledPayoutSafety/Contract.lean`
- Specification files: `cases/hypernova/settled_payout_safety/verity/Specs.lean`, `Benchmark/Cases/Hypernova/SettledPayoutSafety/Specs.lean`
- Editable proof file: `Benchmark/Generated/Hypernova/SettledPayoutSafety/Tasks/ValidSettledPayoutIsSafe.lean`
- Hidden reference solution: `Benchmark.Cases.Hypernova.SettledPayoutSafety.Proofs`

### `ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free`
- Track / property class / proof family: `proof-only` / `fee_payout_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.fee_payout_bounded_by_fee_free`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/ipor/plasma_vault_redeem_split/verity/Contract.lean`, `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Contract.lean`
- Specification files: `cases/ipor/plasma_vault_redeem_split/verity/Specs.lean`, `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Specs.lean`
- Editable proof file: `Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks/FeePayoutBoundedByFeeFree.lean`
- Hidden reference solution: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Proofs`

### `ipor/plasma_vault_redeem_split/redeem_preserves_pps`
- Track / property class / proof family: `proof-only` / `pps_nondecrease` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.redeem_preserves_pps`
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

### `kyberswap/partial_fill_price_floor/check_return_amount_partial_fill_price_floor`
- Track / property class / proof family: `proof-only` / `price_floor` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.KyberSwap.PartialFillPriceFloor.checkReturnAmount_partial_fill_price_floor`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/kyberswap/partial_fill_price_floor/verity/Contract.lean`, `Benchmark/Cases/KyberSwap/PartialFillPriceFloor/Contract.lean`
- Specification files: `cases/kyberswap/partial_fill_price_floor/verity/Specs.lean`, `Benchmark/Cases/KyberSwap/PartialFillPriceFloor/Specs.lean`
- Editable proof file: `Benchmark/Generated/KyberSwap/PartialFillPriceFloor/Tasks/CheckReturnAmountPartialFillPriceFloor.lean`
- Hidden reference solution: `Benchmark.Cases.KyberSwap.PartialFillPriceFloor.Proofs`

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

### `lifi/swap_atomicity/committed_route_executes_every_step`
- Track / property class / proof family: `proof-only` / `no_partial_success` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.LiFi.SwapAtomicity.committed_route_executes_every_step`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lifi/swap_atomicity/verity/Contract.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Contract.lean`
- Specification files: `cases/lifi/swap_atomicity/verity/Specs.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Specs.lean`
- Editable proof file: `Benchmark/Generated/LiFi/SwapAtomicity/Tasks/CommittedRouteExecutesEveryStep.lean`
- Hidden reference solution: `Benchmark.Cases.LiFi.SwapAtomicity.Proofs`

### `lifi/swap_atomicity/failed_step_reverts`
- Track / property class / proof family: `proof-only` / `all_or_nothing` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.LiFi.SwapAtomicity.failed_step_reverts`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lifi/swap_atomicity/verity/Contract.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Contract.lean`
- Specification files: `cases/lifi/swap_atomicity/verity/Specs.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Specs.lean`
- Editable proof file: `Benchmark/Generated/LiFi/SwapAtomicity/Tasks/FailedStepReverts.lean`
- Hidden reference solution: `Benchmark.Cases.LiFi.SwapAtomicity.Proofs`

### `lifi/swap_atomicity/final_transfer_implies_all_steps_succeeded`
- Track / property class / proof family: `proof-only` / `all_or_nothing` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.LiFi.SwapAtomicity.final_transfer_implies_all_steps_succeeded`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lifi/swap_atomicity/verity/Contract.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Contract.lean`
- Specification files: `cases/lifi/swap_atomicity/verity/Specs.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Specs.lean`
- Editable proof file: `Benchmark/Generated/LiFi/SwapAtomicity/Tasks/FinalTransferImpliesAllStepsSucceeded.lean`
- Hidden reference solution: `Benchmark.Cases.LiFi.SwapAtomicity.Proofs`

### `lifi/swap_atomicity/min_output_required_for_commit`
- Track / property class / proof family: `proof-only` / `minimum_output_gate` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.LiFi.SwapAtomicity.min_output_required_for_commit`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lifi/swap_atomicity/verity/Contract.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Contract.lean`
- Specification files: `cases/lifi/swap_atomicity/verity/Specs.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Specs.lean`
- Editable proof file: `Benchmark/Generated/LiFi/SwapAtomicity/Tasks/MinOutputRequiredForCommit.lean`
- Hidden reference solution: `Benchmark.Cases.LiFi.SwapAtomicity.Proofs`

### `lifi/swap_atomicity/no_final_transfer_on_failed_step`
- Track / property class / proof family: `proof-only` / `atomic_finalization` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.LiFi.SwapAtomicity.no_final_transfer_on_failed_step`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lifi/swap_atomicity/verity/Contract.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Contract.lean`
- Specification files: `cases/lifi/swap_atomicity/verity/Specs.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Specs.lean`
- Editable proof file: `Benchmark/Generated/LiFi/SwapAtomicity/Tasks/NoFinalTransferOnFailedStep.lean`
- Hidden reference solution: `Benchmark.Cases.LiFi.SwapAtomicity.Proofs`

### `lifi/swap_atomicity/route_gate_failure_prevents_commit`
- Track / property class / proof family: `proof-only` / `atomic_finalization` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.LiFi.SwapAtomicity.route_gate_failure_prevents_commit`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/lifi/swap_atomicity/verity/Contract.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Contract.lean`
- Specification files: `cases/lifi/swap_atomicity/verity/Specs.lean`, `Benchmark/Cases/LiFi/SwapAtomicity/Specs.lean`
- Editable proof file: `Benchmark/Generated/LiFi/SwapAtomicity/Tasks/RouteGateFailurePreventsCommit.lean`
- Hidden reference solution: `Benchmark.Cases.LiFi.SwapAtomicity.Proofs`

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

### `openzeppelin/erc4626_virtual_offset_deposit/deposit_redeem_round_trip_bound`
- Track / property class / proof family: `proof-only` / `arithmetic_rounding` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.deposit_redeem_round_trip_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Contract.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Contract.lean`
- Specification files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Specs.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean`
- Editable proof file: `Benchmark/Generated/OpenZeppelin/ERC4626VirtualOffsetDeposit/Tasks/DepositRedeemRoundTripBound.lean`
- Hidden reference solution: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Proofs`

### `openzeppelin/erc4626_virtual_offset_deposit/deposit_sets_total_assets`
- Track / property class / proof family: `proof-only` / `storage_write` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.deposit_sets_totalAssets`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Contract.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Contract.lean`
- Specification files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Specs.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean`
- Editable proof file: `Benchmark/Generated/OpenZeppelin/ERC4626VirtualOffsetDeposit/Tasks/DepositSetsTotalAssets.lean`
- Hidden reference solution: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Proofs`

### `openzeppelin/erc4626_virtual_offset_deposit/deposit_sets_total_shares`
- Track / property class / proof family: `proof-only` / `storage_write` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.deposit_sets_totalShares`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Contract.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Contract.lean`
- Specification files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Specs.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean`
- Editable proof file: `Benchmark/Generated/OpenZeppelin/ERC4626VirtualOffsetDeposit/Tasks/DepositSetsTotalShares.lean`
- Hidden reference solution: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Proofs`

### `openzeppelin/erc4626_virtual_offset_deposit/positive_deposit_mints_positive_shares_under_rate_bound`
- Track / property class / proof family: `proof-only` / `output_range` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.positive_deposit_mints_positive_shares_under_rate_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Contract.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Contract.lean`
- Specification files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Specs.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean`
- Editable proof file: `Benchmark/Generated/OpenZeppelin/ERC4626VirtualOffsetDeposit/Tasks/PositiveDepositMintsPositiveSharesUnderRateBound.lean`
- Hidden reference solution: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Proofs`

### `openzeppelin/erc4626_virtual_offset_deposit/preview_deposit_rounds_down`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.previewDeposit_rounds_down`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Contract.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Contract.lean`
- Specification files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Specs.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean`
- Editable proof file: `Benchmark/Generated/OpenZeppelin/ERC4626VirtualOffsetDeposit/Tasks/PreviewDepositRoundsDown.lean`
- Hidden reference solution: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Proofs`

### `openzeppelin/erc4626_virtual_offset_deposit/share_price_monotone_under_donation`
- Track / property class / proof family: `proof-only` / `arithmetic_rounding` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.share_price_monotone_under_donation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Contract.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Contract.lean`
- Specification files: `cases/openzeppelin/erc4626_virtual_offset_deposit/verity/Specs.lean`, `Benchmark/Cases/OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean`
- Editable proof file: `Benchmark/Generated/OpenZeppelin/ERC4626VirtualOffsetDeposit/Tasks/SharePriceMonotoneUnderDonation.lean`
- Hidden reference solution: `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Proofs`

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

### `pareto/redemption_backing/deposit_funds_preserves_closed_epoch_reserve_guard`
- Track / property class / proof family: `proof-only` / `redemption_reserve_guard` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Pareto.RedemptionBacking.depositFunds_preserves_closed_epoch_reserve_guard`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/pareto/redemption_backing/verity/Contract.lean`, `Benchmark/Cases/Pareto/RedemptionBacking/Contract.lean`
- Specification files: `cases/pareto/redemption_backing/verity/Specs.lean`, `Benchmark/Cases/Pareto/RedemptionBacking/Specs.lean`
- Editable proof file: `Benchmark/Generated/Pareto/RedemptionBacking/Tasks/DepositFundsPreservesClosedEpochReserveGuard.lean`
- Hidden reference solution: `Benchmark.Cases.Pareto.RedemptionBacking.Proofs`

### `pendle/py_supply_pairing/mint_py_mints_equal_amount`
- Track / property class / proof family: `proof-only` / `accounting_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Pendle.PySupplyPairing.mint_py_mints_equal_amount`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/pendle/py_supply_pairing/verity/Contract.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Contract.lean`
- Specification files: `cases/pendle/py_supply_pairing/verity/Specs.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Specs.lean`
- Editable proof file: `Benchmark/Generated/Pendle/PySupplyPairing/Tasks/MintPyMintsEqualAmount.lean`
- Hidden reference solution: `Benchmark.Cases.Pendle.PySupplyPairing.Proofs`

### `pendle/py_supply_pairing/mint_py_preserves_supply_pairing`
- Track / property class / proof family: `proof-only` / `accounting_invariant` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Pendle.PySupplyPairing.mint_py_preserves_supply_pairing`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/pendle/py_supply_pairing/verity/Contract.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Contract.lean`
- Specification files: `cases/pendle/py_supply_pairing/verity/Specs.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Specs.lean`
- Editable proof file: `Benchmark/Generated/Pendle/PySupplyPairing/Tasks/MintPyPreservesSupplyPairing.lean`
- Hidden reference solution: `Benchmark.Cases.Pendle.PySupplyPairing.Proofs`

### `pendle/py_supply_pairing/redeem_py_pre_expiry_burns_equal_amount`
- Track / property class / proof family: `proof-only` / `accounting_update` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Pendle.PySupplyPairing.redeem_py_pre_expiry_burns_equal_amount`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/pendle/py_supply_pairing/verity/Contract.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Contract.lean`
- Specification files: `cases/pendle/py_supply_pairing/verity/Specs.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Specs.lean`
- Editable proof file: `Benchmark/Generated/Pendle/PySupplyPairing/Tasks/RedeemPyPreExpiryBurnsEqualAmount.lean`
- Hidden reference solution: `Benchmark.Cases.Pendle.PySupplyPairing.Proofs`

### `pendle/py_supply_pairing/redeem_py_pre_expiry_preserves_supply_pairing`
- Track / property class / proof family: `proof-only` / `accounting_invariant` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Pendle.PySupplyPairing.redeem_py_pre_expiry_preserves_supply_pairing`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/pendle/py_supply_pairing/verity/Contract.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Contract.lean`
- Specification files: `cases/pendle/py_supply_pairing/verity/Specs.lean`, `Benchmark/Cases/Pendle/PySupplyPairing/Specs.lean`
- Editable proof file: `Benchmark/Generated/Pendle/PySupplyPairing/Tasks/RedeemPyPreExpiryPreservesSupplyPairing.lean`
- Hidden reference solution: `Benchmark.Cases.Pendle.PySupplyPairing.Proofs`

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
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.buy_preserves_reserve_ratio_zero`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/buy_preserves_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polaris/bonding_curve/floor_sell_and_burn_preserves_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.floorSellAndBurn_preserves_reserve_ratio_zero`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/floor_sell_and_burn_preserves_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polaris/bonding_curve/init_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.init_reserve_ratio_zero`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/polaris/bonding_curve/verity/Contract.lean`, `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- Specification files: `cases/polaris/bonding_curve/verity/Specs.lean`, `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- Editable proof file: `Benchmark/Generated/Polaris/BondingCurve/Tasks/init_reserve_ratio_zero.lean`
- Hidden reference solution: `Benchmark.Cases.Polaris.BondingCurve.Proofs`

### `polaris/bonding_curve/sell_preserves_reserve_ratio_zero`
- Track / property class / proof family: `proof-only` / `reserve_state_transition` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Polaris.BondingCurve.sell_preserves_reserve_ratio_zero`
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

### `starkware/starkgate_escrow/deposit_preserves_escrow_lower_bound`
- Track / property class / proof family: `proof-only` / `escrow_lower_bound` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Starkware.StarkgateEscrow.deposit_preserves_escrow_lower_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/starkware/starkgate_escrow/verity/Contract.lean`, `Benchmark/Cases/Starkware/StarkgateEscrow/Contract.lean`
- Specification files: `cases/starkware/starkgate_escrow/verity/Specs.lean`, `Benchmark/Cases/Starkware/StarkgateEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/Starkware/StarkgateEscrow/Tasks/DepositPreservesEscrowLowerBound.lean`
- Hidden reference solution: `Benchmark.Cases.Starkware.StarkgateEscrow.Proofs`

### `starkware/starkgate_escrow/deposit_reclaim_preserves_escrow_lower_bound`
- Track / property class / proof family: `proof-only` / `escrow_lower_bound` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Starkware.StarkgateEscrow.depositReclaim_preserves_escrow_lower_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/starkware/starkgate_escrow/verity/Contract.lean`, `Benchmark/Cases/Starkware/StarkgateEscrow/Contract.lean`
- Specification files: `cases/starkware/starkgate_escrow/verity/Specs.lean`, `Benchmark/Cases/Starkware/StarkgateEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/Starkware/StarkgateEscrow/Tasks/DepositReclaimPreservesEscrowLowerBound.lean`
- Hidden reference solution: `Benchmark.Cases.Starkware.StarkgateEscrow.Proofs`

### `starkware/starkgate_escrow/withdraw_preserves_escrow_lower_bound`
- Track / property class / proof family: `proof-only` / `escrow_lower_bound` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Starkware.StarkgateEscrow.withdraw_preserves_escrow_lower_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/starkware/starkgate_escrow/verity/Contract.lean`, `Benchmark/Cases/Starkware/StarkgateEscrow/Contract.lean`
- Specification files: `cases/starkware/starkgate_escrow/verity/Specs.lean`, `Benchmark/Cases/Starkware/StarkgateEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/Starkware/StarkgateEscrow/Tasks/WithdrawPreservesEscrowLowerBound.lean`
- Hidden reference solution: `Benchmark.Cases.Starkware.StarkgateEscrow.Proofs`

### `superfluid/realtime_balance_conservation/callback_level_two_is_rejected`
- Track / property class / proof family: `proof-only` / `failure_propagation` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.callbackLevelTwo_is_rejected`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/CallbackLevelTwoIsRejected.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/create_non_app_frames_unrelated_account`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.createNonApp_frames_unrelated_account`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/CreateNonAppFramesUnrelatedAccount.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/create_non_app_preserves_cfa_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.createNonApp_preserves_cfa_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/CreateNonAppPreservesCfaProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/create_non_app_preserves_future_modular_cfa_global_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.createNonApp_preserves_future_modular_cfa_global_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/CreateNonAppPreservesFutureModularCfaGlobalProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/create_non_app_preserves_pair_net_flow_rate`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.createNonApp_preserves_pair_net_flow_rate`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/CreateNonAppPreservesPairNetFlowRate.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/delete_non_app_frames_unrelated_account`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.deleteNonApp_frames_unrelated_account`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/DeleteNonAppFramesUnrelatedAccount.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/delete_non_app_preserves_cfa_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.deleteNonApp_preserves_cfa_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/DeleteNonAppPreservesCfaProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/delete_non_app_preserves_future_modular_cfa_global_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.deleteNonApp_preserves_future_modular_cfa_global_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/DeleteNonAppPreservesFutureModularCfaGlobalProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/delete_non_app_preserves_pair_net_flow_rate`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.deleteNonApp_preserves_pair_net_flow_rate`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/DeleteNonAppPreservesPairNetFlowRate.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/failed_nested_rolls_back_and_prevents_resume`
- Track / property class / proof family: `proof-only` / `revert_safety` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.failedNested_rolls_back_and_prevents_resume`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/FailedNestedRollsBackAndPreventsResume.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/pair_and_frame_implies_modular_cfa_global_projection`
- Track / property class / proof family: `proof-only` / `composition_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.pairAndFrame_implies_modular_cfa_global_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/PairAndFrameImpliesModularCfaGlobalProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/receiver_delete_callback_frames_unrelated_account`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.receiverDeleteCallback_frames_unrelated_account`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/ReceiverDeleteCallbackFramesUnrelatedAccount.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/receiver_delete_callback_matches_factored_instance_behavior`
- Track / property class / proof family: `proof-only` / `functional_property` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.receiverDeleteCallback_matches_factored_instance_behavior`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/ReceiverDeleteCallbackMatchesFactoredInstanceBehavior.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/receiver_delete_callback_preserves_cfa_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.receiverDeleteCallback_preserves_cfa_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/ReceiverDeleteCallbackPreservesCfaProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/receiver_delete_callback_preserves_future_modular_cfa_global_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.receiverDeleteCallback_preserves_future_modular_cfa_global_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/ReceiverDeleteCallbackPreservesFutureModularCfaGlobalProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/receiver_delete_callback_preserves_pair_net_flow_rate`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.receiverDeleteCallback_preserves_pair_net_flow_rate`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/ReceiverDeleteCallbackPreservesPairNetFlowRate.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/receiver_delete_callback_reloads_final_zero`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.receiverDeleteCallback_reloads_final_zero`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/ReceiverDeleteCallbackReloadsFinalZero.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/successful_one_level_components_compose`
- Track / property class / proof family: `proof-only` / `composition_invariant` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.successfulOneLevel_components_compose`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/SuccessfulOneLevelComponentsCompose.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/update_non_app_frames_unrelated_account`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.updateNonApp_frames_unrelated_account`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/UpdateNonAppFramesUnrelatedAccount.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/update_non_app_preserves_cfa_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.updateNonApp_preserves_cfa_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/UpdateNonAppPreservesCfaProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/update_non_app_preserves_future_modular_cfa_global_projection`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.updateNonApp_preserves_future_modular_cfa_global_projection`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/UpdateNonAppPreservesFutureModularCfaGlobalProjection.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `superfluid/realtime_balance_conservation/update_non_app_preserves_pair_net_flow_rate`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.updateNonApp_preserves_pair_net_flow_rate`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/superfluid/realtime_balance_conservation/verity/Contract.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Contract.lean`
- Specification files: `cases/superfluid/realtime_balance_conservation/verity/Specs.lean`, `Benchmark/Cases/Superfluid/RealtimeBalanceConservation/Specs.lean`
- Editable proof file: `Benchmark/Generated/Superfluid/RealtimeBalanceConservation/Tasks/UpdateNonAppPreservesPairNetFlowRate.lean`
- Hidden reference solution: `Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Proofs`

### `t3tris/hwm_performance_fee/fee_claim_preserves_unclaimed_le_supply`
- Track / property class / proof family: `proof-only` / `fee_accounting_bounds` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.fee_claim_preserves_unclaimed_le_supply`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/FeeClaimPreservesUnclaimedLeSupply.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/gain_loss_recovery_no_double_charge`
- Track / property class / proof family: `proof-only` / `economic_no_double_charge` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.gain_loss_recovery_no_double_charge`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/GainLossRecoveryNoDoubleCharge.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/no_performance_fee_when_pre_pps_le_hwm`
- Track / property class / proof family: `proof-only` / `fee_trigger` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.no_performance_fee_when_pre_pps_le_hwm`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/NoPerformanceFeeWhenPrePpsLeHwm.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/period_fee_accounting_preserves_structural_assumptions`
- Track / property class / proof family: `proof-only` / `fee_accounting_bounds` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.period_fee_accounting_preserves_structural_assumptions`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/PeriodFeeAccountingPreservesStructuralAssumptions.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/profit_pnl_uses_cached_hwm`
- Track / property class / proof family: `proof-only` / `fee_base_correctness` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.profit_pnl_uses_cached_hwm`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/ProfitPnlUsesCachedHwm.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/recovery_then_new_high_uses_stored_hwm`
- Track / property class / proof family: `proof-only` / `fee_base_correctness` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.recovery_then_new_high_uses_stored_hwm`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/RecoveryThenNewHighUsesStoredHwm.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/validated_initial_state_satisfies_successful_assumptions`
- Track / property class / proof family: `proof-only` / `configuration_safety` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.validated_initial_state_satisfies_successful_assumptions`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/ValidatedInitialStateSatisfiesSuccessfulAssumptions.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `t3tris/hwm_performance_fee/validated_performance_fee_update_preserves_cap`
- Track / property class / proof family: `proof-only` / `configuration_safety` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.T3tris.HwmPerformanceFee.validated_performance_fee_update_preserves_cap`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/t3tris/hwm_performance_fee/verity/Contract.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Contract.lean`
- Specification files: `cases/t3tris/hwm_performance_fee/verity/Specs.lean`, `Benchmark/Cases/T3tris/HwmPerformanceFee/Specs.lean`
- Editable proof file: `Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks/ValidatedPerformanceFeeUpdatePreservesCap.lean`
- Hidden reference solution: `Benchmark.Cases.T3tris.HwmPerformanceFee.Proofs`

### `term_finance/term_auction_clearing/clearing_assignment_correct`
- Track / property class / proof family: `proof-only` / `accounting_and_rate_guard` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.TermFinance.TermAuctionClearing.clearing_assignment_correct`
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

### `uniswap_v2/pair_fee_adjusted_swap/swap_enforces_fee_adjusted_invariant`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.applySwap_enforces_fee_adjusted_invariant`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Contract.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Contract.lean`
- Specification files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Specs.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Specs.lean`
- Editable proof file: `Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/SwapEnforcesFeeAdjustedInvariant.lean`
- Hidden reference solution: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs`

### `uniswap_v2/pair_fee_adjusted_swap/swap_sandwich_output_bound`
- Track / property class / proof family: `proof-only` / `accounting_bound` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.applySwap_swap_sandwich_output_bound`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Contract.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Contract.lean`
- Specification files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Specs.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Specs.lean`
- Editable proof file: `Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/SwapSandwichOutputBound.lean`
- Hidden reference solution: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs`

### `uniswap_v2/pair_fee_adjusted_swap/swap_sets_reserve0`
- Track / property class / proof family: `proof-only` / `storage_write` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.applySwap_sets_reserve0`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Contract.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Contract.lean`
- Specification files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Specs.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Specs.lean`
- Editable proof file: `Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/SwapSetsReserve0.lean`
- Hidden reference solution: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs`

### `uniswap_v2/pair_fee_adjusted_swap/swap_sets_reserve1`
- Track / property class / proof family: `proof-only` / `storage_write` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.applySwap_sets_reserve1`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Contract.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Contract.lean`
- Specification files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Specs.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Specs.lean`
- Editable proof file: `Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/SwapSetsReserve1.lean`
- Hidden reference solution: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs`

### `uniswap_v2/pair_fee_adjusted_swap/swap_sets_reserve_product`
- Track / property class / proof family: `proof-only` / `accounting_conservation` / `refinement_equivalence`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.applySwap_sets_reserve_product`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Contract.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Contract.lean`
- Specification files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Specs.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Specs.lean`
- Editable proof file: `Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/SwapSetsReserveProduct.lean`
- Hidden reference solution: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs`

### `uniswap_v2/pair_fee_adjusted_swap/two_swap_k_monotone`
- Track / property class / proof family: `proof-only` / `arithmetic_rounding` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.applySwap_two_swap_k_monotone`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Contract.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Contract.lean`
- Specification files: `cases/uniswap_v2/pair_fee_adjusted_swap/verity/Specs.lean`, `Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Specs.lean`
- Editable proof file: `Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/TwoSwapKMonotone.lean`
- Hidden reference solution: `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs`

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

### `yo_protocol/async_redemption_escrow/cancel_redeem_accounting`
- Track / property class / proof family: `proof-only` / `accounting_update` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.cancel_redeem_accounting`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/CancelRedeemExactAccounting.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/candidate_g_source_reachability`
- Track / property class / proof family: `proof-only` / `source_reachable_counterexample_coverage` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.candidate_g_source_reachability`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/CandidateGSourceReachability.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/fee_aliasing`
- Track / property class / proof family: `proof-only` / `fee_rounding_and_aliasing` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.fee_aliasing`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/FeeAliasingUsesCurrentFee.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/fulfill_redeem_accounting`
- Track / property class / proof family: `proof-only` / `accounting_invariant` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.fulfill_redeem_accounting`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/FulfillRedeemExactAccounting.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/full_clear_requeue_replay`
- Track / property class / proof family: `proof-only` / `replay_lifecycle` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.full_clear_requeue_replay`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/FullClearRequeueReplay.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/lifecycle_bounds_and_isolation`
- Track / property class / proof family: `proof-only` / `per_receiver_isolation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.lifecycle_bounds_and_isolation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/LifecycleBoundsAndIsolation.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/lifecycle_rollback`
- Track / property class / proof family: `proof-only` / `revert_atomicity` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.lifecycle_rollback`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/LifecycleFailureRollsBack.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/malformed_pair_lifecycle`
- Track / property class / proof family: `proof-only` / `malformed_record_behavior` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.malformed_pair_lifecycle`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/MalformedPairDormancyAndRevival.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/owner_fallback_authorization`
- Track / property class / proof family: `proof-only` / `owner_fallback_and_authority_order` / `authorization_enablement`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.owner_fallback_authorization`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/OwnerFallbackAuthorization.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/queued_request_aggregation`
- Track / property class / proof family: `proof-only` / `accounting_update` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.queued_request_aggregation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/QueuedRequestAggregatesReceiver.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/redeem_wrapper`
- Track / property class / proof family: `proof-only` / `wrapper_delegation_and_pause` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.redeem_wrapper`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/RedeemWrapperDelegates.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/request_redeem_branching`
- Track / property class / proof family: `proof-only` / `branch_correctness` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.request_redeem_branching`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/RequestRedeemPreservesBranches.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/two_owner_queue_aggregation`
- Track / property class / proof family: `proof-only` / `receiver_aggregation` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.two_owner_queue_aggregation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/TwoOwnerQueueAggregatesReceiver.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

### `yo_protocol/async_redemption_escrow/zero_component_lifecycle`
- Track / property class / proof family: `proof-only` / `source_permitted_noop` / `protocol_transition_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.zero_component_lifecycle`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/yo_protocol/async_redemption_escrow/verity/Contract.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Contract.lean`
- Specification files: `cases/yo_protocol/async_redemption_escrow/verity/Specs.lean`, `Benchmark/Cases/YOProtocol/AsyncRedemptionEscrow/Specs.lean`
- Editable proof file: `Benchmark/Generated/YOProtocol/AsyncRedemptionEscrow/Tasks/ZeroComponentLifecycleNoop.lean`
- Hidden reference solution: `Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Proofs`

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

### `zama_protocol_apps/erc7984_upgradeable_exact_source/initialized_insufficient_transfer_zero`
- Track / property class / proof family: `proof-only` / `insufficient_balance_zero_transfer` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.initialized_insufficient_transfer_zero`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Contract.lean`
- Specification files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984UpgradeableExactSource/Tasks/InitializedInsufficientTransferZero.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Proofs`

### `zama_protocol_apps/erc7984_upgradeable_exact_source/initialized_transfer_no_balance_revert`
- Track / property class / proof family: `proof-only` / `non_reversion` / `functional_correctness`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.initialized_transfer_no_balance_revert`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Contract.lean`
- Specification files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984UpgradeableExactSource/Tasks/InitializedTransferNoBalanceRevert.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Proofs`

### `zama_protocol_apps/erc7984_upgradeable_exact_source/initialized_transfer_pair_conservation`
- Track / property class / proof family: `proof-only` / `balance_conservation` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.initialized_transfer_pair_conservation`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Contract.lean`
- Specification files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984UpgradeableExactSource/Tasks/InitializedTransferPairConservation.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Proofs`

### `zama_protocol_apps/erc7984_upgradeable_exact_source/uninitialized_sender_reverts_without_writes`
- Track / property class / proof family: `proof-only` / `revert_rollback` / `state_preservation_local_effects`
- Readiness: prompt_context=`ready`, editable_proof=`ready`, reference_solution=`ready`
- Theorem target: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.uninitialized_sender_reverts_without_writes`
- Evaluation: engine=`lean_proof_generation`, target_kind=`proof_generation`
- Implementation files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Contract.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Contract.lean`
- Specification files: `cases/zama_protocol_apps/erc7984_upgradeable_exact_source/verity/Specs.lean`, `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Specs.lean`
- Editable proof file: `Benchmark/Generated/Zama/ERC7984UpgradeableExactSource/Tasks/UninitializedSenderRevertsWithoutWrites.lean`
- Hidden reference solution: `Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Proofs`

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
- Run mutable full suite: `./scripts/run_all.sh`
- Run frozen v0.2 suite: `./scripts/run_all.sh --suite v0.2`
- Run repo check: `./scripts/check.sh`
