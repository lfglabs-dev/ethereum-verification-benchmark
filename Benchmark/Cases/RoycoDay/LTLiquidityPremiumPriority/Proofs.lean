import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

private theorem natUint256EncodingExact_of_le
    (n : Nat) (h : n ≤ UINT256_MAX) : natUint256EncodingExact n := by
  unfold natUint256EncodingExact
  rw [Verity.Core.Uint256.val_ofNat]
  apply Nat.mod_eq_of_lt
  rw [← Verity.Core.Uint256.max_uint256_succ_eq_modulus]
  exact Nat.lt_succ_iff.mpr (by simpa [UINT256_MAX, Verity.Core.MAX_UINT256] using h)

private theorem natInt256EncodingExact_of_le
    (n : Nat) (h : n ≤ INT256_MAX) : natInt256EncodingExact n := by
  have hUint : natUint256EncodingExact n :=
    natUint256EncodingExact_of_le n (by
      unfold INT256_MAX at h
      unfold UINT256_MAX
      omega)
  have hSign : n < Verity.Core.Int256.signBit := by
    unfold INT256_MAX at h
    unfold Verity.Core.Int256.signBit
    omega
  have hNonnegative : ¬ (Int.ofNat n) < 0 :=
    not_lt_of_ge (Int.natCast_nonneg n)
  have hOfInt :
      Verity.Core.Int256.ofInt (Int.ofNat n) =
        Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat n) := by
    unfold Verity.Core.Int256.ofInt
    rw [if_neg hNonnegative]
    simp
  unfold natUint256EncodingExact at hUint
  unfold natInt256EncodingExact int256EncodingExact
  rw [hOfInt]
  rw [Verity.Core.Int256.toInt_of_lt_signBit]
  · exact congrArg Int.ofNat hUint
  · change (Verity.Core.Uint256.ofNat n).val < Verity.Core.Int256.signBit
    rw [hUint]
    exact hSign

private theorem checkedArithmeticRefinesNat_proof :
    checkedArithmeticRefinesNat := by
  intro a b ha hb
  have haExact := natUint256EncodingExact_of_le a ha
  have hbExact := natUint256EncodingExact_of_le b hb
  unfold natUint256EncodingExact at haExact hbExact
  have haVal : ((Verity.Core.Uint256.ofNat a : Verity.Core.Uint256) : Nat) = a := haExact
  have hbVal : ((Verity.Core.Uint256.ofNat b : Verity.Core.Uint256) : Nat) = b := hbExact
  constructor
  · intro hAdd
    have hAdd' : a + b ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa [UINT256_MAX, Verity.Core.MAX_UINT256] using hAdd
    unfold Verity.Stdlib.Math.safeAdd
    rw [haVal, hbVal]
    simp only [if_neg (Nat.not_lt.mpr hAdd')]
    congr 1
    simp
  · intro hSub
    have hNoUnderflow :
        (Verity.Core.Uint256.ofNat b).val ≤ (Verity.Core.Uint256.ofNat a).val := by
      rw [hbExact, haExact]
      exact hSub
    unfold Verity.Stdlib.Math.safeSub
    rw [haVal, hbVal]
    simp only [if_neg (Nat.not_lt.mpr hSub)]
    congr 1
    apply Verity.Core.Uint256.ext
    rw [Verity.Core.Uint256.sub_eq_of_le hNoUnderflow]
    rw [haExact, hbExact]
    have hDifferenceExact := natUint256EncodingExact_of_le (a - b)
      (Nat.le_trans (Nat.sub_le a b) ha)
    unfold natUint256EncodingExact at hDifferenceExact
    exact hDifferenceExact.symm

private theorem fullPrecisionMulDivRefinesNat_proof :
    fullPrecisionMulDivRefinesNat := by
  intro a b denominator ha hb hDenominator hNonzero
  have haExact := natUint256EncodingExact_of_le a ha
  have hbExact := natUint256EncodingExact_of_le b hb
  have hDenominatorExact := natUint256EncodingExact_of_le denominator hDenominator
  unfold natUint256EncodingExact at haExact hbExact hDenominatorExact
  have haVal : ((Verity.Core.Uint256.ofNat a : Verity.Core.Uint256) : Nat) = a := haExact
  have hbVal : ((Verity.Core.Uint256.ofNat b : Verity.Core.Uint256) : Nat) = b := hbExact
  have hDenominatorVal :
      ((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) = denominator :=
    hDenominatorExact
  have hWordDenominatorNonzero :
      ((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) ≠ 0 := by
    rw [hDenominatorVal]
    exact hNonzero
  constructor
  · intro hFit
    have hWordFit :
        (((Verity.Core.Uint256.ofNat a : Verity.Core.Uint256) : Nat) *
          ((Verity.Core.Uint256.ofNat b : Verity.Core.Uint256) : Nat)) /
            ((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) ≤
              Verity.Stdlib.Math.MAX_UINT256 := by
      rw [haVal, hbVal, hDenominatorVal]
      simpa [UINT256_MAX, Verity.Core.MAX_UINT256, mulDivDown] using hFit
    rw [Verity.Proofs.Stdlib.Math.mulDiv512Down?_some
      (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b)
      (Verity.Core.Uint256.ofNat denominator) hWordDenominatorNonzero hWordFit]
    congr 2
    rw [haVal, hbVal, hDenominatorVal]
    rfl
  · intro hFit
    have hCeil : a * b + (denominator - 1) = a * b + denominator - 1 := by omega
    have hWordFit :
        ((((Verity.Core.Uint256.ofNat a : Verity.Core.Uint256) : Nat) *
          ((Verity.Core.Uint256.ofNat b : Verity.Core.Uint256) : Nat)) +
            (((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) - 1)) /
              ((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) ≤
                Verity.Stdlib.Math.MAX_UINT256 := by
      rw [haVal, hbVal, hDenominatorVal]
      simpa [UINT256_MAX, Verity.Core.MAX_UINT256, mulDivUp, hCeil] using hFit
    rw [Verity.Proofs.Stdlib.Math.mulDiv512Up?_some
      (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b)
      (Verity.Core.Uint256.ofNat denominator) hWordDenominatorNonzero hWordFit]
    congr 2
    rw [haVal, hbVal, hDenominatorVal]
    unfold mulDivUp
    exact congrArg (fun n => n / denominator) hCeil

private theorem AccountingState.uint256EncodingExact_of_bounded
    (s : AccountingState) (h : s.uint256Bounded) : s.uint256EncodingExact := by
  rcases h with ⟨hCollateral, hLPT, hST, hJT, hIL, _⟩
  exact ⟨natUint256EncodingExact_of_le _ hCollateral,
    natUint256EncodingExact_of_le _ hLPT,
    natUint256EncodingExact_of_le _ hST,
    natUint256EncodingExact_of_le _ hJT,
    natUint256EncodingExact_of_le _ hIL⟩

private theorem SyncConfig.uint256EncodingExact_of_bounded
    (cfg : SyncConfig) (h : cfg.uint256Bounded) : cfg.uint256EncodingExact := by
  rcases h with ⟨hDust, hCoverage, hLiquidity, hLiquidation⟩
  have hWidth : UINT64_MAX ≤ UINT256_MAX := by
    norm_num [UINT64_MAX, UINT256_MAX]
  exact ⟨natUint256EncodingExact_of_le _ hDust,
    natUint256EncodingExact_of_le _ (le_trans hCoverage hWidth),
    natUint256EncodingExact_of_le _ (le_trans hLiquidity hWidth),
    natUint256EncodingExact_of_le _ hLiquidation⟩

private theorem YieldConfig.uintEncodingExact_of_bounded
    (cfg : YieldConfig) (h : cfg.uintBounded) : cfg.uintEncodingExact := by
  rcases h with ⟨hElapsed, hJT, hLPT, _, hSTFee, hJTFee, hJTYieldFee, hLPTYieldFee⟩
  have hJT256 : cfg.twJTYieldShareAccruedWAD ≤ UINT256_MAX := by
    unfold UINT128_MAX at hJT
    unfold UINT256_MAX
    omega
  have hLPT256 : cfg.twLPTYieldShareAccruedWAD ≤ UINT256_MAX := by
    unfold UINT128_MAX at hLPT
    unfold UINT256_MAX
    omega
  have hWidth : UINT64_MAX ≤ UINT256_MAX := by
    norm_num [UINT64_MAX, UINT256_MAX]
  exact ⟨natUint256EncodingExact_of_le _ hElapsed,
    natUint256EncodingExact_of_le _ hJT256,
    natUint256EncodingExact_of_le _ hLPT256,
    natUint256EncodingExact_of_le _ (le_trans hSTFee hWidth),
    natUint256EncodingExact_of_le _ (le_trans hJTFee hWidth),
    natUint256EncodingExact_of_le _ (le_trans hJTYieldFee hWidth),
    natUint256EncodingExact_of_le _ (le_trans hLPTYieldFee hWidth)⟩

private theorem YieldOutputs.uint256EncodingExact_of_bounded
    (o : YieldOutputs) (h : o.uint256Bounded) : o.uint256EncodingExact := by
  rcases h with ⟨hLPT, hST, hJT, hLPTFee⟩
  exact ⟨natUint256EncodingExact_of_le _ hLPT,
    natUint256EncodingExact_of_le _ hST,
    natUint256EncodingExact_of_le _ hJT,
    natUint256EncodingExact_of_le _ hLPTFee⟩

private theorem SyncResult.uint256EncodingExact_of_bounded
    (r : SyncResult) (h : r.uint256Bounded) : r.uint256EncodingExact := by
  rcases h with ⟨hAccounting, hOutputs, hRepaid, hRemaining, hResidual,
    hSTGain, hJTGain, hJTPremium, hJTYieldFee, hJTLoss, hSTLoss, hCoverage, hLiquidity⟩
  exact ⟨AccountingState.uint256EncodingExact_of_bounded _ hAccounting,
    YieldOutputs.uint256EncodingExact_of_bounded _ hOutputs,
    natUint256EncodingExact_of_le _ hRepaid,
    natUint256EncodingExact_of_le _ hRemaining,
    natUint256EncodingExact_of_le _ hResidual,
    natUint256EncodingExact_of_le _ hSTGain,
    natUint256EncodingExact_of_le _ hJTGain,
    natUint256EncodingExact_of_le _ hJTPremium,
    natUint256EncodingExact_of_le _ hJTYieldFee,
    natUint256EncodingExact_of_le _ hJTLoss,
    natUint256EncodingExact_of_le _ hSTLoss,
    natUint256EncodingExact_of_le _ hCoverage,
    natUint256EncodingExact_of_le _ hLiquidity⟩

@[simp] private theorem applyMarketTransition_conserves
    (r : SyncResult) (cfg : SyncConfig) :
    (applyMarketTransition r cfg).accounting.conserves ↔ r.accounting.conserves := by
  unfold applyMarketTransition AccountingState.conserves
  by_cases h : shouldBePerpetual r.accounting cfg = true <;> simp [h]

theorem _nat_uint256_refinement
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last currentCollateralNAV syncCfg yieldCfg) :
    NatUint256RefinementSpec
      last currentCollateralNAV syncCfg yieldCfg := by
  rcases hDomain with
    ⟨hSuccessful, hLast, hCurrent, hSyncCfg, hYieldCfg, hResult⟩
  unfold NatUint256RefinementSpec
  exact ⟨hSuccessful, hResult,
    AccountingState.uint256EncodingExact_of_bounded _ hLast,
    natUint256EncodingExact_of_le _ hCurrent,
    SyncConfig.uint256EncodingExact_of_bounded _ hSyncCfg,
    YieldConfig.uintEncodingExact_of_bounded _ hYieldCfg,
    SyncResult.uint256EncodingExact_of_bounded _ hResult,
    checkedArithmeticRefinesNat_proof,
    fullPrecisionMulDivRefinesNat_proof⟩

theorem _recovery_before_yield
    (last : AccountingState)
    (gain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (_hDomain : sourceSyncDomain last (last.collateralNAV + gain)
      syncCfg yieldCfg) :
    RecoveryBeforeYieldSpec last gain syncCfg yieldCfg := by
  by_cases hGain : gain = 0
  · subst gain
    simp [RecoveryBeforeYieldSpec, previewSyncTrancheAccounting,
      finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition]
  · have hIncrease : last.collateralNAV < last.collateralNAV + gain := by omega
    unfold RecoveryBeforeYieldSpec
    simp [previewSyncTrancheAccounting, hIncrease, handleCollateralGain,
      finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition]
    intro hRecovery
    have hResidual : gain - min gain last.jtImpermanentLoss = 0 := by omega
    simp [residualSTGain, hResidual, grossPremium, mulDivDown, YieldOutputs.zero]

theorem _combined_premium_bound
    (stGain : Nat)
    (cfg : YieldConfig)
    (hCfg : cfg.valid)
    (_hUint256 : stGain ≤ UINT256_MAX ∧ cfg.uintBounded) :
    CombinedPremiumBoundSpec stGain cfg := by
  unfold CombinedPremiumBoundSpec grossPremium mulDivDown
  apply le_trans (Nat.add_div_le_add_div _ _ _)
  apply Nat.div_le_of_le_mul
  rcases hCfg with ⟨_, hAccrued, _⟩
  have hScaled := Nat.mul_le_mul_left stGain hAccrued
  calc
    stGain * cfg.twJTYieldShareAccruedWAD +
        stGain * cfg.twLPTYieldShareAccruedWAD =
      stGain * (cfg.twJTYieldShareAccruedWAD +
        cfg.twLPTYieldShareAccruedWAD) := by rw [Nat.mul_add]
    _ ≤ stGain * (cfg.elapsedSinceLastPremiumPayments * WAD) := hScaled
    _ = (cfg.elapsedSinceLastPremiumPayments * WAD) * stGain := Nat.mul_comm _ _

theorem _lpt_premium_coverage_neutral
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (cfg : YieldConfig)
    (lptAccruedA lptAccruedB : Nat)
    (_hCfgA : ({ cfg with twLPTYieldShareAccruedWAD := lptAccruedA }).valid)
    (_hCfgB : ({ cfg with twLPTYieldShareAccruedWAD := lptAccruedB }).valid)
    (_hDomainA : sourceSyncDomain last currentCollateralNAV syncCfg
      { cfg with twLPTYieldShareAccruedWAD := lptAccruedA })
    (_hDomainB : sourceSyncDomain last currentCollateralNAV syncCfg
      { cfg with twLPTYieldShareAccruedWAD := lptAccruedB }) :
    LPTPremiumCoverageNeutralSpec last currentCollateralNAV
      syncCfg cfg lptAccruedA lptAccruedB := by
  by_cases hLoss : currentCollateralNAV < last.collateralNAV
  · simp [LPTPremiumCoverageNeutralSpec, previewSyncTrancheAccounting, hLoss]
  by_cases hGain : last.collateralNAV < currentCollateralNAV
  · simp [LPTPremiumCoverageNeutralSpec, previewSyncTrancheAccounting, hLoss, hGain,
      handleCollateralGain, finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition]
  · simp [LPTPremiumCoverageNeutralSpec, previewSyncTrancheAccounting, hLoss, hGain]

theorem _lpt_premium_mint_split
    (input : FeeMintInput)
    (hDomain : successfulMintDomain input) :
    LPTPremiumMintSplitSpec input := by
  dsimp [successfulMintDomain] at hDomain
  rcases hDomain with
    ⟨_, _, _, hFee, _, _, _, _, _, _, _, _, _⟩
  unfold LPTPremiumMintSplitSpec processFeesAndLiquidityPremium
  simp [Nat.sub_add_cancel hFee]

theorem _st_loss_coverage_priority
    (last : AccountingState)
    (loss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hLossBound : loss ≤ last.collateralNAV)
    (_hDomain : sourceSyncDomain last (last.collateralNAV - loss)
      syncCfg yieldCfg) :
    STLossCoveragePrioritySpec last loss syncCfg yieldCfg := by
  by_cases hZero : loss = 0
  · subst loss
    simp [STLossCoveragePrioritySpec, previewSyncTrancheAccounting,
      finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition]
  · have hDecrease : last.collateralNAV - loss < last.collateralNAV := by omega
    simp [STLossCoveragePrioritySpec, previewSyncTrancheAccounting, hDecrease,
      handleCollateralLoss, finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition,
      Nat.sub_sub_self hLossBound]

theorem _sync_conserves_nav
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last currentCollateralNAV syncCfg yieldCfg) :
    SyncConservationSpec last currentCollateralNAV
      syncCfg yieldCfg := by
  rcases hDomain.1 with ⟨hLast, _, hLossSafe, hGainSafe⟩
  unfold SyncConservationSpec previewSyncTrancheAccounting
  by_cases hLoss : currentCollateralNAV < last.collateralNAV
  · have hSafe := hLossSafe hLoss
    simp [hLoss, handleCollateralLoss, finalizePreviewSyncResult, finalizeSyncResult]
    unfold AccountingState.conserves at hLast ⊢
    dsimp at hSafe ⊢
    omega
  by_cases hGain : last.collateralNAV < currentCollateralNAV
  · have hSafe := (hGainSafe hGain).1
    simp [hLoss, hGain, handleCollateralGain, finalizePreviewSyncResult,
      finalizeSyncResult]
    unfold AccountingState.conserves at hLast ⊢
    dsimp at hSafe ⊢
    omega
  · have hEqual : currentCollateralNAV = last.collateralNAV := by omega
    simpa [hEqual, finalizePreviewSyncResult, finalizeSyncResult] using hLast

theorem _fees_require_full_recovery
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (_hDomain : sourceSyncDomain
      last currentCollateralNAV syncCfg yieldCfg) :
    FeesRequireFullRecoverySpec last currentCollateralNAV
      syncCfg yieldCfg := by
  unfold FeesRequireFullRecoverySpec previewSyncTrancheAccounting
  by_cases hLoss : currentCollateralNAV < last.collateralNAV
  · simp [hLoss, handleCollateralLoss, finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition]
  by_cases hGain : last.collateralNAV < currentCollateralNAV
  · simp [hLoss, hGain, handleCollateralGain, finalizePreviewSyncResult, finalizeSyncResult,
      applyMarketTransition]
    intro hRemaining
    have hResidual :
        currentCollateralNAV - last.collateralNAV -
          min (currentCollateralNAV - last.collateralNAV)
            last.jtImpermanentLoss = 0 := by omega
    simp [residualSTGain, hResidual, grossPremium, mulDivDown, YieldOutputs.zero]
  · simp [hLoss, hGain, finalizePreviewSyncResult, finalizeSyncResult, applyMarketTransition]

theorem _post_op_no_yield
    (before : AccountingState)
    (op : Operation)
    (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat)
    (_hDomain : successfulPostOpSourceDomain before op input
      minCoverageWAD minLiquidityWAD) :
    PostOpNoYieldSpec before op input minCoverageWAD minLiquidityWAD := by
  rfl

theorem _post_op_conserves_nav
    (before : AccountingState)
    (op : Operation)
    (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat)
    (hDomain : successfulPostOpSourceDomain before op input
      minCoverageWAD minLiquidityWAD) :
    PostOpConservationSpec before op input minCoverageWAD minLiquidityWAD := by
  rcases hDomain with ⟨hConserves, _, _, _, _, _, _, _, _, hInput, _⟩
  cases op <;>
    simp [PostOpConservationSpec, postOpSyncTrancheAccounting,
      AccountingState.conserves, successfulPostOpInput] at * <;>
    omega

theorem _inner_reinvestment_coverage_neutral
    (before : ReinvestmentState)
    (requestedShares minLPTAssetsOut lptAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool)
    (_hDomain : successfulReinvestmentDomain before requestedShares
      minLPTAssetsOut lptAssetsMinted minCoverageWAD venueCallSucceeded) :
    InnerReinvestmentCoverageNeutralSpec before requestedShares
      minLPTAssetsOut lptAssetsMinted minCoverageWAD venueCallSucceeded := by
  unfold InnerReinvestmentCoverageNeutralSpec
  by_cases hShares : min requestedShares before.lptOwnedSeniorTrancheShares = 0
  · simp [attemptLiquidityPremiumReinvestment, hShares]
  by_cases hMin : minLPTAssetsOut = 0
  · simp [attemptLiquidityPremiumReinvestment, hShares, hMin]
  cases hVenue : venueCallSucceeded
  · simp [attemptLiquidityPremiumReinvestment, hShares, hMin]
  · have hFloor : minLPTAssetsOut ≤ lptAssetsMinted :=
      _hDomain.2.2.2.2.2.1 hVenue
    simp [attemptLiquidityPremiumReinvestment, hShares, hMin, hFloor]

theorem _partial_recovery_no_fee_regression : PartialRecoveryNoFeeRegressionSpec := by
  norm_num [PartialRecoveryNoFeeRegressionSpec, partialRecoveryLast,
    partialRecoverySyncConfig, partialRecoveryYieldConfig,
    previewSyncTrancheAccounting, handleCollateralGain, residualSTGain,
    finalizePreviewSyncResult, finalizeSyncResult,
    applyMarketTransition, shouldBePerpetual, AccountingState.conserves,
    YieldOutputs.zero, grossPremium, mulDivDown, mulDivUp,
    coverageUtilizationWAD, liquidityUtilizationWAD, WAD, UINT256_MAX]

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
