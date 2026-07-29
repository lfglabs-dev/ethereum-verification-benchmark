import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

private theorem natUint256EncodingExact_of_le
    (n : Nat) (h : n ≤ UINT256_MAX) :
    natUint256EncodingExact n := by
  unfold natUint256EncodingExact
  rw [Verity.Core.Uint256.val_ofNat]
  apply Nat.mod_eq_of_lt
  rw [← Verity.Core.Uint256.max_uint256_succ_eq_modulus]
  exact Nat.lt_succ_iff.mpr (by simpa [UINT256_MAX, Verity.Core.MAX_UINT256] using h)

private theorem natInt256EncodingExact_of_le
    (n : Nat) (h : n ≤ INT256_MAX) :
    natInt256EncodingExact n := by
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

private theorem negInt256EncodingExact_of_le
    (n : Nat) (h : n ≤ INT256_MAX) :
    int256EncodingExact (-(Int.ofNat n)) := by
  cases n with
  | zero =>
      norm_num [int256EncodingExact, Verity.Core.Int256.ofInt,
        Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
        Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
        Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS]
  | succ k =>
      let n := Nat.succ k
      have hNegative : -(Int.ofNat n) < 0 := by
        dsimp [n]
        omega
      have hNltModulus : n < Verity.Core.Int256.modulus := by
        dsimp [n]
        unfold INT256_MAX at h
        unfold Verity.Core.Int256.modulus Verity.Core.Uint256.modulus
          Verity.Core.UINT256_MODULUS
        omega
      have hSubLtModulus :
          Verity.Core.Int256.modulus - n < Verity.Core.Int256.modulus := by
        have hNPositive : 0 < n := by simp [n]
        omega
      have hSubLtUintModulus :
          Verity.Core.Int256.modulus - n < Verity.Core.Uint256.modulus := by
        simpa [Verity.Core.Int256.modulus] using hSubLtModulus
      have hWord :
          (Verity.Core.Int256.ofInt (-(Int.ofNat n))).word.val =
            Verity.Core.Int256.modulus - n := by
        change (Verity.Core.Int256.ofInt (-(Int.ofNat n))).toUint256.val = _
        rw [Verity.Core.Int256.ofInt_neg _ hNegative]
        simp [Verity.Core.Uint256.val_ofNat,
          Nat.mod_eq_of_lt hNltModulus,
          Nat.mod_eq_of_lt hSubLtUintModulus]
      have hWordGeSign :
          Verity.Core.Int256.signBit ≤
            (Verity.Core.Int256.ofInt (-(Int.ofNat n))).word.val := by
        rw [hWord]
        dsimp [n]
        unfold INT256_MAX at h
        unfold Verity.Core.Int256.modulus Verity.Core.Uint256.modulus
          Verity.Core.Int256.signBit Verity.Core.UINT256_MODULUS
        omega
      unfold int256EncodingExact
      rw [Verity.Core.Int256.toInt_of_ge_signBit hWordGeSign]
      rw [hWord]
      change ((Verity.Core.Int256.modulus - n : Nat) : Int) -
        (Verity.Core.Int256.modulus : Nat) = -(n : Nat)
      omega

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
      (Verity.Core.Uint256.ofNat a)
      (Verity.Core.Uint256.ofNat b)
      (Verity.Core.Uint256.ofNat denominator)
      hWordDenominatorNonzero
      hWordFit]
    congr 2
    rw [haVal, hbVal, hDenominatorVal]
    rfl
  · intro hFit
    have hCeil :
        a * b + (denominator - 1) = a * b + denominator - 1 := by
      omega
    have hWordFit :
        ((((Verity.Core.Uint256.ofNat a : Verity.Core.Uint256) : Nat) *
          ((Verity.Core.Uint256.ofNat b : Verity.Core.Uint256) : Nat)) +
            (((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) - 1)) /
              ((Verity.Core.Uint256.ofNat denominator : Verity.Core.Uint256) : Nat) ≤
                Verity.Stdlib.Math.MAX_UINT256 := by
      rw [haVal, hbVal, hDenominatorVal]
      simpa [UINT256_MAX, Verity.Core.MAX_UINT256, mulDivUp, hCeil] using hFit
    rw [Verity.Proofs.Stdlib.Math.mulDiv512Up?_some
      (Verity.Core.Uint256.ofNat a)
      (Verity.Core.Uint256.ofNat b)
      (Verity.Core.Uint256.ofNat denominator)
      hWordDenominatorNonzero
      hWordFit]
    congr 2
    rw [haVal, hbVal, hDenominatorVal]
    unfold mulDivUp
    exact congrArg (fun n => n / denominator) hCeil

private theorem RawNAVs.uint256EncodingExact_of_bounded
    (raw : RawNAVs) (h : raw.uint256Bounded) :
    raw.uint256EncodingExact := by
  rcases h with ⟨hST, hJT, hLT, _⟩
  exact ⟨natUint256EncodingExact_of_le _ hST,
    natUint256EncodingExact_of_le _ hJT,
    natUint256EncodingExact_of_le _ hLT⟩

private theorem AccountingState.uint256EncodingExact_of_bounded
    (s : AccountingState) (h : s.uint256Bounded) :
    s.uint256EncodingExact := by
  rcases h with ⟨hRaw, hST, hJT, hIL, _⟩
  exact ⟨RawNAVs.uint256EncodingExact_of_bounded _ hRaw,
    natUint256EncodingExact_of_le _ hST,
    natUint256EncodingExact_of_le _ hJT,
    natUint256EncodingExact_of_le _ hIL⟩

private theorem SyncConfig.uint256EncodingExact_of_bounded
    (cfg : SyncConfig) (h : cfg.uint256Bounded) :
    cfg.uint256EncodingExact := by
  rcases h with ⟨hDust, hCoverage, hLiquidity⟩
  exact ⟨natUint256EncodingExact_of_le _ hDust,
    natUint256EncodingExact_of_le _ hCoverage,
    natUint256EncodingExact_of_le _ hLiquidity⟩

private theorem YieldConfig.uint256EncodingExact_of_bounded
    (cfg : YieldConfig) (h : cfg.uint256Bounded) :
    cfg.uint256EncodingExact := by
  rcases h with
    ⟨hElapsed, hJT, hLT, _, hSTFee, hJTFee, hJTYieldFee, hLTYieldFee⟩
  exact ⟨natUint256EncodingExact_of_le _ hElapsed,
    natUint256EncodingExact_of_le _ hJT,
    natUint256EncodingExact_of_le _ hLT,
    natUint256EncodingExact_of_le _ hSTFee,
    natUint256EncodingExact_of_le _ hJTFee,
    natUint256EncodingExact_of_le _ hJTYieldFee,
    natUint256EncodingExact_of_le _ hLTYieldFee⟩

private theorem SignedDelta.uint256EncodingExact_of_bounded
    (delta : SignedDelta)
    (h : match delta with
      | .loss amount | .gain amount => amount ≤ UINT256_MAX
      | .flat => True) :
    delta.uint256EncodingExact := by
  cases delta with
  | loss amount => exact natUint256EncodingExact_of_le amount h
  | flat => trivial
  | gain amount => exact natUint256EncodingExact_of_le amount h

private theorem RawNAVs.sourceInt256EncodingExact_of_bounded
    (raw : RawNAVs)
    (hST : raw.stRawNAV ≤ INT256_MAX)
    (hJT : raw.jtRawNAV ≤ INT256_MAX) :
    raw.sourceInt256EncodingExact := by
  exact ⟨natInt256EncodingExact_of_le _ hST,
    natInt256EncodingExact_of_le _ hJT⟩

private theorem SignedDelta.int256EncodingExact_of_bounded
    (delta : SignedDelta)
    (h : match delta with
      | .loss amount | .gain amount => amount ≤ INT256_MAX
      | .flat => True) :
    delta.int256EncodingExact := by
  cases delta with
  | loss amount => exact negInt256EncodingExact_of_le amount h
  | flat =>
      have hZero : (0 : Nat) ≤ INT256_MAX := by
        unfold INT256_MAX
        omega
      exact natInt256EncodingExact_of_le 0 hZero
  | gain amount => exact natInt256EncodingExact_of_le amount h

private theorem SyncResult.uint256EncodingExact_of_bounded
    (result : SyncResult) (h : result.uint256Bounded) :
    result.uint256EncodingExact := by
  rcases h with ⟨hAccounting, hLTPremium, hSTFee, hJTFee, hLTFee,
    hRecovered, hRemaining, hResidualYield, hJTRiskPremium, hJTYieldFee,
    hPriorJTFee, hCoverageApplied, hResidualLoss, hCoverage, hLiquidity⟩
  exact ⟨AccountingState.uint256EncodingExact_of_bounded _ hAccounting,
    ⟨natUint256EncodingExact_of_le _ hLTPremium,
      natUint256EncodingExact_of_le _ hSTFee,
      natUint256EncodingExact_of_le _ hJTFee,
      natUint256EncodingExact_of_le _ hLTFee⟩,
    natUint256EncodingExact_of_le _ hRecovered,
    natUint256EncodingExact_of_le _ hRemaining,
    natUint256EncodingExact_of_le _ hResidualYield,
    natUint256EncodingExact_of_le _ hJTRiskPremium,
    natUint256EncodingExact_of_le _ hJTYieldFee,
    natUint256EncodingExact_of_le _ hPriorJTFee,
    natUint256EncodingExact_of_le _ hCoverageApplied,
    natUint256EncodingExact_of_le _ hResidualLoss,
    natUint256EncodingExact_of_le _ hCoverage,
    natUint256EncodingExact_of_le _ hLiquidity⟩

theorem _nat_uint256_refinement
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last current deltaJT deltaST syncCfg yieldCfg) :
    NatUint256RefinementSpec
      last current deltaJT deltaST syncCfg yieldCfg := by
  rcases hDomain with
    ⟨_, _, hIntSafe, hLast, hCurrent, hSyncCfg, hYieldCfg,
      hDeltaJT, hDeltaST, hResult⟩
  rcases hIntSafe with
    ⟨hLastSTInt, hLastJTInt, hCurrentSTInt, hCurrentJTInt, hDeltaJTInt, hDeltaSTInt, _⟩
  unfold NatUint256RefinementSpec
  exact ⟨AccountingState.uint256EncodingExact_of_bounded _ hLast,
    RawNAVs.uint256EncodingExact_of_bounded _ hCurrent,
    RawNAVs.sourceInt256EncodingExact_of_bounded _ hLastSTInt hLastJTInt,
    RawNAVs.sourceInt256EncodingExact_of_bounded _ hCurrentSTInt hCurrentJTInt,
    SignedDelta.uint256EncodingExact_of_bounded _ hDeltaJT,
    SignedDelta.uint256EncodingExact_of_bounded _ hDeltaST,
    SignedDelta.int256EncodingExact_of_bounded _ hDeltaJTInt,
    SignedDelta.int256EncodingExact_of_bounded _ hDeltaSTInt,
    SyncConfig.uint256EncodingExact_of_bounded _ hSyncCfg,
    YieldConfig.uint256EncodingExact_of_bounded _ hYieldCfg,
    SyncResult.uint256EncodingExact_of_bounded _ hResult,
    checkedArithmeticRefinesNat_proof,
    fullPrecisionMulDivRefinesNat_proof⟩


theorem _recovery_before_yield
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT : SignedDelta)
    (stGain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (_hDomain : sourceSyncDomain
      last current deltaJT (.gain stGain) syncCfg yieldCfg) :
    RecoveryBeforeYieldSpec
      last current deltaJT stGain syncCfg yieldCfg := by
  unfold RecoveryBeforeYieldSpec
  simp [previewSyncTrancheAccounting, handleSTGain, coverageRecovery,
    finalizeSyncResult]
  intro hGain
  by_cases hFixed : syncCfg.resultingMarketState = .fixedTerm <;>
    simp [hGain, hFixed, grossPremium, mulDivDown, YieldOutputs.zero]

theorem _combined_premium_bound
    (stGain coverageIL : Nat)
    (cfg : YieldConfig)
    (hCfg : cfg.valid)
    (_hUint256 :
      stGain ≤ UINT256_MAX ∧ coverageIL ≤ UINT256_MAX ∧
      cfg.uint256Bounded) :
    CombinedPremiumBoundSpec stGain coverageIL cfg := by
  unfold CombinedPremiumBoundSpec grossPremium mulDivDown
  apply le_trans (Nat.add_div_le_add_div _ _ _)
  apply Nat.div_le_of_le_mul
  rcases hCfg with ⟨_, hAccrued, _⟩
  have hScaled := Nat.mul_le_mul_left
    (residualSeniorYield stGain coverageIL) hAccrued
  calc
    residualSeniorYield stGain coverageIL * cfg.twJTYieldShareAccruedWAD +
        residualSeniorYield stGain coverageIL * cfg.twLTYieldShareAccruedWAD =
      residualSeniorYield stGain coverageIL *
        (cfg.twJTYieldShareAccruedWAD + cfg.twLTYieldShareAccruedWAD) := by
          rw [Nat.mul_add]
    _ ≤ residualSeniorYield stGain coverageIL *
        (cfg.elapsedSinceLastPremiumPayments * WAD) := hScaled
    _ = (cfg.elapsedSinceLastPremiumPayments * WAD) *
        residualSeniorYield stGain coverageIL := Nat.mul_comm _ _

theorem _lt_premium_coverage_neutral
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (cfg : YieldConfig)
    (ltAccruedA ltAccruedB : Nat)
    (_hCfgA : ({ cfg with twLTYieldShareAccruedWAD := ltAccruedA }).valid)
    (_hCfgB : ({ cfg with twLTYieldShareAccruedWAD := ltAccruedB }).valid)
    (hDomainA : sourceSyncDomain
      last current deltaJT deltaST syncCfg
      { cfg with twLTYieldShareAccruedWAD := ltAccruedA })
    (hDomainB : sourceSyncDomain
      last current deltaJT deltaST syncCfg
      { cfg with twLTYieldShareAccruedWAD := ltAccruedB }) :
    LTPremiumCoverageNeutralSpec
      last current deltaJT deltaST syncCfg cfg ltAccruedA ltAccruedB := by
  cases deltaST <;>
    simp [LTPremiumCoverageNeutralSpec, previewSyncTrancheAccounting,
      handleSTLoss, handleSTFlat, handleSTGain, finalizeSyncResult]

theorem _lt_premium_mint_split
    (input : FeeMintInput)
    (hDomain : successfulMintDomain input) :
    LTPremiumMintSplitSpec input := by
  rcases hDomain with ⟨_, hFee, _, _⟩
  unfold LTPremiumMintSplitSpec processFeesAndLiquidityPremium
  simp [Nat.sub_add_cancel hFee]

theorem _st_loss_coverage_priority
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT : SignedDelta)
    (stLoss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (_hDomain : sourceSyncDomain
      last current deltaJT (.loss stLoss) syncCfg yieldCfg) :
    STLossCoveragePrioritySpec
      last current deltaJT stLoss syncCfg yieldCfg := by
  unfold STLossCoveragePrioritySpec
  simp [previewSyncTrancheAccounting, handleSTLoss, finalizeSyncResult]
  by_cases hFixed : syncCfg.resultingMarketState = .fixedTerm <;>
    simp [hFixed, YieldOutputs.zero]

theorem _sync_conserves_nav
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last current deltaJT deltaST syncCfg yieldCfg) :
    SyncConservationSpec
      last current deltaJT deltaST syncCfg yieldCfg := by
  rcases hDomain with ⟨hSuccess, hIntermediate, _⟩
  rcases hSuccess with ⟨hLast, hCfg, hDeltas, hJTLoss, hSTLoss⟩
  cases hErase : syncCfg.eraseCoverageIL <;>
  cases deltaJT <;> cases deltaST <;>
    simp [SyncConservationSpec, previewSyncTrancheAccounting,
      applyJTEffectiveDelta, handleSTLoss, handleSTFlat, handleSTGain,
      finalizeSyncResult, AccountingState.conserves,
      signedDeltasMatchRaw, syncIntermediateUint256Safe,
      coverageRecovery, hErase] at * <;>
    omega

theorem _post_op_no_yield
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat)
    (_hDomain : successfulPostOpSourceDomain
      before op amounts minCoverageWAD minLiquidityWAD) :
    PostOpNoYieldSpec
      before op amounts minCoverageWAD minLiquidityWAD := by
  rfl

theorem _post_op_conserves_nav
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat)
    (hDomain : successfulPostOpSourceDomain
      before op amounts minCoverageWAD minLiquidityWAD) :
    PostOpConservationSpec
      before op amounts minCoverageWAD minLiquidityWAD := by
  rcases hDomain with ⟨hConserves, _, _, _, _, hInput, _⟩
  cases op <;>
    simp [PostOpConservationSpec, postOpSyncTrancheAccountingUnchecked,
      AccountingState.conserves, successfulPostOpInput] at * <;>
    omega

theorem _inner_reinvestment_coverage_neutral
    (before : ReinvestmentState)
    (requestedShares minLTAssetsOut ltAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool)
    (hDomain : successfulReinvestmentDomain
      before requestedShares minLTAssetsOut ltAssetsMinted
      minCoverageWAD venueCallSucceeded) :
    InnerReinvestmentCoverageNeutralSpec
      before requestedShares minLTAssetsOut ltAssetsMinted
      minCoverageWAD venueCallSucceeded := by
  unfold InnerReinvestmentCoverageNeutralSpec
  by_cases hShares : min requestedShares before.ltOwnedSeniorTrancheShares = 0
  · simp [attemptLiquidityPremiumReinvestment, hShares]
  by_cases hMin : minLTAssetsOut = 0
  · simp [attemptLiquidityPremiumReinvestment, hShares, hMin]
  cases venueCallSucceeded <;>
    simp [attemptLiquidityPremiumReinvestment, hShares, hMin]

theorem _independent_jt_fee_counterexample : IndependentJTFeeCounterexampleSpec := by
  have hMarket : MarketState.perpetual ≠ MarketState.fixedTerm := by decide
  norm_num [IndependentJTFeeCounterexampleSpec, sourceSyncDomain,
    successfulSyncDomain, signedDeltasMatchRaw, syncIntermediateUint256Safe,
    sourceAttributionInt256Safe, RawNAVs.uint256Bounded,
    AccountingState.uint256Bounded, SyncConfig.uint256Bounded,
    YieldConfig.uint256Bounded, SyncResult.uint256Bounded,
    SignedDelta.magnitude, YieldOutputs.zero,
    dustCounterexampleLast, dustCounterexampleCurrentRaw,
    dustCounterexampleSyncConfig, dustCounterexampleYieldConfig,
    YieldConfig.valid, AccountingState.conserves,
    previewSyncTrancheAccounting, applyJTEffectiveDelta,
    handleSTGain, finalizeSyncResult, coverageRecovery,
    residualSeniorYield, grossPremium, mulDivDown, mulDivUp,
    coverageUtilizationWAD, liquidityUtilizationWAD,
    UINT256_MAX, INT256_MAX, WAD, hMarket]

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
