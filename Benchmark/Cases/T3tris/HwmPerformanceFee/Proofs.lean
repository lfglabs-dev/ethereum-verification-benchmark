import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs
import Mathlib.Tactic.Linarith

/-!
Reference proofs for the task obligations generated under
`Benchmark/Generated/T3tris/HwmPerformanceFee/Tasks`.
-/

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

private theorem not_gt_of_le {a b : Nat} (h : a <= b) : Not (a > b) := by
  omega

private theorem absDist_eq_sub_of_gt {a b : Nat} (h : a > b) :
    absDist a b = a - b := by
  unfold absDist
  split <;> omega

private theorem isPerformanceProfit_eq_false_of_prePps_le
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel)
    (h : prePerformancePps gross managementFee <= params.ppsHighWaterMark) :
    isPerformanceProfit gross params managementFee = false := by
  unfold isPerformanceProfit
  simp [not_gt_of_le h]

private theorem performanceFeeSharesCandidate_eq_zero_of_prePps_le
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel)
    (h : prePerformancePps gross managementFee <= params.ppsHighWaterMark) :
    performanceFeeSharesCandidate gross params managementFee = 0 := by
  simp [performanceFeeSharesCandidate, isPerformanceProfit_eq_false_of_prePps_le gross params managementFee h]

private theorem performanceFeeAssets_eq_zero_of_prePps_le
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel)
    (h : prePerformancePps gross managementFee <= params.ppsHighWaterMark) :
    performanceFeeAssets gross params managementFee = 0 := by
  simp [performanceFeeAssets, performanceFeeSharesCandidate_eq_zero_of_prePps_le gross params managementFee h]

private theorem finalUpdatedPps_eq_prePerformancePps_of_prePps_le
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel)
    (h : prePerformancePps gross managementFee <= params.ppsHighWaterMark) :
    finalUpdatedPps gross params managementFee = prePerformancePps gross managementFee := by
  unfold finalUpdatedPps finalSupply prePerformancePps
  rw [performanceFeeSharesCandidate_eq_zero_of_prePps_le gross params managementFee h]
  simp [supplyAfterManagement]

private theorem hwm_ratchet_unchanged_of_prePps_le
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel)
    (h : prePerformancePps gross managementFee <= params.ppsHighWaterMark) :
    max params.ppsHighWaterMark (finalUpdatedPps gross params managementFee) =
      params.ppsHighWaterMark := by
  rw [finalUpdatedPps_eq_prePerformancePps_of_prePps_le gross params managementFee h]
  exact Nat.max_eq_left h

private theorem periodStep_performanceFeeAssets_eq_zero_of_prePps_le
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel)
    (h : (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.prePerformancePps <=
      s.ppsHighWaterMark) :
    (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.performanceFeeAssets = 0 := by
  dsimp [periodStepNoReanchor, computeLastPeriodFeesAndUpdateResult] at h
  dsimp [periodStepNoReanchor, computeLastPeriodFeesAndUpdateResult]
  exact performanceFeeAssets_eq_zero_of_prePps_le
    { totalAssets := totalAssets, totalSupply := s.grossSupply }
    {
      unclaimedSharesFee := s.unclaimedSharesFee
      ppsHighWaterMark := s.ppsHighWaterMark
      performanceFeeWad := s.performanceFeeWad
    }
    managementFee h

private theorem periodStep_performanceFeeShares_eq_zero_of_prePps_le
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel)
    (h : (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.prePerformancePps <=
      s.ppsHighWaterMark) :
    (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.performanceFeeShares = 0 := by
  dsimp [periodStepNoReanchor, computeLastPeriodFeesAndUpdateResult] at h
  dsimp [periodStepNoReanchor, computeLastPeriodFeesAndUpdateResult]
  exact performanceFeeSharesCandidate_eq_zero_of_prePps_le
    { totalAssets := totalAssets, totalSupply := s.grossSupply }
    {
      unclaimedSharesFee := s.unclaimedSharesFee
      ppsHighWaterMark := s.ppsHighWaterMark
      performanceFeeWad := s.performanceFeeWad
    }
    managementFee h

private theorem periodStep_hwm_eq_of_prePps_le
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel)
    (h : (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.prePerformancePps <=
      s.ppsHighWaterMark) :
    (periodStepNoReanchor s totalAssets managementFee).fst.ppsHighWaterMark = s.ppsHighWaterMark := by
  dsimp [periodStepNoReanchor, recordAccruedFeesNoReanchor, computeLastPeriodFeesAndUpdateResult] at h
  dsimp [periodStepNoReanchor, recordAccruedFeesNoReanchor, computeLastPeriodFeesAndUpdateResult]
  exact hwm_ratchet_unchanged_of_prePps_le
    { totalAssets := totalAssets, totalSupply := s.grossSupply }
    {
      unclaimedSharesFee := s.unclaimedSharesFee
      ppsHighWaterMark := s.ppsHighWaterMark
      performanceFeeWad := s.performanceFeeWad
    }
    managementFee h

private theorem periodStep_hwm_eq_max
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel) :
    (periodStepNoReanchor s totalAssets managementFee).fst.ppsHighWaterMark =
      max s.ppsHighWaterMark
        (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.updatedPps := by
  dsimp [periodStepNoReanchor, recordAccruedFeesNoReanchor]

private theorem periodStep_pnl_uses_hwm_of_prePps_gt
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel)
    (h : (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.prePerformancePps >
      s.ppsHighWaterMark) :
    (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.pnl =
      ((periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.prePerformancePps -
          s.ppsHighWaterMark) *
        (periodStepNoReanchor s totalAssets managementFee).snd.lastPeriodData.oldTotalNetSupply / WAD := by
  dsimp [periodStepNoReanchor, computeLastPeriodFeesAndUpdateResult] at h
  dsimp [periodStepNoReanchor, computeLastPeriodFeesAndUpdateResult]
  unfold performancePnl
  rw [absDist_eq_sub_of_gt h]
  simp [fullMulDiv, WAD]

theorem no_performance_fee_when_pre_pps_le_hwm
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) :
    no_performance_fee_when_pre_pps_le_hwm_spec gross params managementFee := by
  dsimp [no_performance_fee_when_pre_pps_le_hwm_spec]
  intro hLe
  dsimp [computeLastPeriodFeesAndUpdateResult] at hLe
  dsimp [computeLastPeriodFeesAndUpdateResult]
  exact And.intro
    (performanceFeeAssets_eq_zero_of_prePps_le gross params managementFee hLe)
    (performanceFeeSharesCandidate_eq_zero_of_prePps_le gross params managementFee hLe)

theorem profit_pnl_uses_cached_hwm
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) :
    profit_pnl_uses_cached_hwm_spec gross params managementFee := by
  dsimp [profit_pnl_uses_cached_hwm_spec]
  intro hGt
  dsimp [computeLastPeriodFeesAndUpdateResult] at hGt
  dsimp [computeLastPeriodFeesAndUpdateResult]
  unfold performancePnl
  rw [absDist_eq_sub_of_gt hGt]
  simp [fullMulDiv, WAD]

theorem gain_loss_recovery_no_double_charge
    (s0 : FeeState)
    (gainAssets lossAssets recoveryAssets : Nat)
    (gainManagementFee : ManagementFeeModel := noManagementFee)
    (lossManagementFee : ManagementFeeModel := noManagementFee)
    (recoveryManagementFee : ManagementFeeModel := noManagementFee) :
    gain_loss_recovery_no_double_charge_spec
      s0 gainAssets lossAssets recoveryAssets
      gainManagementFee lossManagementFee recoveryManagementFee := by
  dsimp [gain_loss_recovery_no_double_charge_spec]
  intro _hGainOk _hLossOk _hRecoveryOk hGain hFee hLossLt hRecoveryFromLoss hRecoveryLe
  let step1 := periodStepNoReanchor s0 gainAssets gainManagementFee
  let s1 := step1.fst
  let r1 := step1.snd
  let step2 := periodStepNoReanchor s1 lossAssets lossManagementFee
  let s2 := step2.fst
  let r2 := step2.snd
  let step3 := periodStepNoReanchor s2 recoveryAssets recoveryManagementFee
  let r3 := step3.snd
  have hLossLeRaw := Nat.le_of_lt hLossLt
  have hLossLe :
      step2.snd.lastPeriodData.prePerformancePps <= s1.ppsHighWaterMark := by
    simpa [step1, s1, step2] using hLossLeRaw
  have hLossHwm : s2.ppsHighWaterMark = s1.ppsHighWaterMark := by
    exact periodStep_hwm_eq_of_prePps_le s1 lossAssets lossManagementFee hLossLe
  have hRecoveryLeS2 :
      step3.snd.lastPeriodData.prePerformancePps <= s2.ppsHighWaterMark := by
    rw [hLossHwm]
    exact hRecoveryLe
  constructor
  · exact periodStep_pnl_uses_hwm_of_prePps_gt s0 gainAssets gainManagementFee hGain
  constructor
  · exact hFee
  constructor
  · exact periodStep_hwm_eq_max s0 gainAssets gainManagementFee
  constructor
  · intro hUpdatedGt
    calc
      s1.ppsHighWaterMark = max s0.ppsHighWaterMark r1.lastPeriodData.updatedPps :=
        periodStep_hwm_eq_max s0 gainAssets gainManagementFee
      _ = r1.lastPeriodData.updatedPps := Nat.max_eq_right (Nat.le_of_lt hUpdatedGt)
  constructor
  · exact hRecoveryFromLoss
  constructor
  · exact periodStep_performanceFeeAssets_eq_zero_of_prePps_le
      s1 lossAssets lossManagementFee hLossLe
  constructor
  · exact periodStep_performanceFeeShares_eq_zero_of_prePps_le
      s1 lossAssets lossManagementFee hLossLe
  constructor
  · exact hLossHwm
  constructor
  · exact periodStep_performanceFeeAssets_eq_zero_of_prePps_le
      s2 recoveryAssets recoveryManagementFee hRecoveryLeS2
  constructor
  · exact periodStep_performanceFeeShares_eq_zero_of_prePps_le
      s2 recoveryAssets recoveryManagementFee hRecoveryLeS2
  · calc
      step3.fst.ppsHighWaterMark = s2.ppsHighWaterMark :=
        periodStep_hwm_eq_of_prePps_le s2 recoveryAssets recoveryManagementFee hRecoveryLeS2
      _ = s1.ppsHighWaterMark := hLossHwm

theorem recovery_then_new_high_uses_stored_hwm
    (s0 : FeeState)
    (gainAssets lossAssets recoveryAssets newHighAssets : Nat)
    (gainManagementFee : ManagementFeeModel := noManagementFee)
    (lossManagementFee : ManagementFeeModel := noManagementFee)
    (recoveryManagementFee : ManagementFeeModel := noManagementFee)
    (newHighManagementFee : ManagementFeeModel := noManagementFee) :
    recovery_then_new_high_uses_stored_hwm_spec
      s0 gainAssets lossAssets recoveryAssets newHighAssets
      gainManagementFee lossManagementFee recoveryManagementFee newHighManagementFee := by
  dsimp [recovery_then_new_high_uses_stored_hwm_spec]
  intro _hGainOk _hLossOk _hRecoveryOk _hNewHighOk _hGain _hFee
    hLossLt _hRecoveryFromLoss hRecoveryLe hNewHigh
  let step1 := periodStepNoReanchor s0 gainAssets gainManagementFee
  let s1 := step1.fst
  let step2 := periodStepNoReanchor s1 lossAssets lossManagementFee
  let s2 := step2.fst
  let step3 := periodStepNoReanchor s2 recoveryAssets recoveryManagementFee
  let s3 := step3.fst
  have hLossLeRaw := Nat.le_of_lt hLossLt
  have hLossLe :
      step2.snd.lastPeriodData.prePerformancePps <= s1.ppsHighWaterMark := by
    simpa [step1, s1, step2] using hLossLeRaw
  have hLossHwm : s2.ppsHighWaterMark = s1.ppsHighWaterMark := by
    exact periodStep_hwm_eq_of_prePps_le s1 lossAssets lossManagementFee hLossLe
  have hRecoveryLeS2 :
      step3.snd.lastPeriodData.prePerformancePps <= s2.ppsHighWaterMark := by
    rw [hLossHwm]
    exact hRecoveryLe
  have hStored : s3.ppsHighWaterMark = s1.ppsHighWaterMark := by
    calc
      s3.ppsHighWaterMark = s2.ppsHighWaterMark :=
        periodStep_hwm_eq_of_prePps_le s2 recoveryAssets recoveryManagementFee hRecoveryLeS2
      _ = s1.ppsHighWaterMark := hLossHwm
  calc
    (periodStepNoReanchor s3 newHighAssets newHighManagementFee).snd.lastPeriodData.pnl =
        ((periodStepNoReanchor s3 newHighAssets newHighManagementFee).snd.lastPeriodData.prePerformancePps -
            s3.ppsHighWaterMark) *
          (periodStepNoReanchor s3 newHighAssets newHighManagementFee).snd.lastPeriodData.oldTotalNetSupply / WAD :=
      periodStep_pnl_uses_hwm_of_prePps_gt s3 newHighAssets newHighManagementFee hNewHigh
    _ =
        ((periodStepNoReanchor s3 newHighAssets newHighManagementFee).snd.lastPeriodData.prePerformancePps -
            s1.ppsHighWaterMark) *
          (periodStepNoReanchor s3 newHighAssets newHighManagementFee).snd.lastPeriodData.oldTotalNetSupply / WAD := by
      rw [hStored]

end Benchmark.Cases.T3tris.HwmPerformanceFee
