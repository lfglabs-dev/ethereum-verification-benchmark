import Benchmark.Cases.Royco.DawnValuationRecovery.Specs
import Verity.Proofs.Stdlib.Automation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Benchmark.Cases.Royco.DawnValuationRecovery

theorem attribution_residual_absorbed_by_junior
    (s : AccountantState) (input : SyncInput) :
    attribution_residual_absorbed_by_junior_spec s input := by
  unfold attribution_residual_absorbed_by_junior_spec
  simp [computeEffectiveDeltas]

theorem forced_perpetual_erasure_is_explicit
    (s : AccountantState) (input : SyncInput) :
    forced_perpetual_erasure_is_explicit_spec s input := by
  unfold forced_perpetual_erasure_is_explicit_spec
  dsimp
  intro h
  have hforce :
      forcedPerpetual s input
        (applySTEffectiveDelta s input
          (applyJTEffectiveDelta s (computeEffectiveDeltas s input).deltaJTEffectiveNAV)
          (computeEffectiveDeltas s input).deltaSTEffectiveNAV)
        (computeUtilization input.stRawNAV input.jtRawNAV s.betaWAD s.coverageWAD
          (applySTEffectiveDelta s input
            (applyJTEffectiveDelta s (computeEffectiveDeltas s input).deltaJTEffectiveNAV)
            (computeEffectiveDeltas s input).deltaSTEffectiveNAV).jtEffectiveNAV) = true := by
    simpa [previewSyncTrancheAccounting] using h
  simp [previewSyncTrancheAccounting, resolveMarketState, hforce]

theorem signed_delta_overflow_boundary_rejected :
    signed_delta_overflow_boundary_rejected_spec := by
  unfold signed_delta_overflow_boundary_rejected_spec
  intro h
  simp [successfulSyncAssumptions, signedAttributionArithmeticSafe,
    signedOverflowBoundaryState, signedOverflowBoundaryInput, sourceValuesFit,
    preStateConserved, computeEffectiveDeltas, computeNAVDelta,
    attributeDeltaToClaimOnRawNAV, saturatingSub,
    safeNegatableInt256, fitsInt256] at h
  have hzero : INT256_MAX = 0 := h.1.1.2
  norm_num [INT256_MAX] at hzero

private theorem jt_residual_implies_st_il_zero
    (s : AccountantState) (delta : Int) :
    let gain := if delta > 0 then delta.natAbs else 0
    gain - min gain s.lastSTImpermanentLoss > 0 →
      (applyJTEffectiveDelta s delta).stImpermanentLoss = 0 := by
  dsimp
  by_cases hn : delta < 0
  · have hnp : ¬ 0 < delta := by omega
    simp [applyJTEffectiveDelta, hn, hnp]
  · by_cases hp : delta > 0
    · simp [applyJTEffectiveDelta, hn, hp, initialAllocationState]
      omega
    · simp [applyJTEffectiveDelta, hn, hp]

private theorem st_jt_recovery_implies_st_il_zero
    (s : AccountantState) (input : SyncInput) (state : AllocationState) (delta : Int) :
    let gain := if delta > 0 then delta.natAbs else 0
    let stRecovery := min gain state.stImpermanentLoss
    let jtRecovery := min (gain - stRecovery) state.jtImpermanentLoss
    jtRecovery > 0 →
      (applySTEffectiveDelta s input state delta).stImpermanentLoss = 0 := by
  dsimp
  by_cases hn : delta < 0
  · have hnp : ¬ 0 < delta := by omega
    simp [applySTEffectiveDelta, hn, hnp]
  · by_cases hp : delta > 0
    · simp [applySTEffectiveDelta, hn, hp]
      omega
    · simp [applySTEffectiveDelta, hn, hp]

private theorem st_residual_implies_liabilities_zero
    (s : AccountantState) (input : SyncInput) (state : AllocationState) (delta : Int) :
    let gain := if delta > 0 then delta.natAbs else 0
    let stRecovery := min gain state.stImpermanentLoss
    let jtRecovery := min (gain - stRecovery) state.jtImpermanentLoss
    let residual := gain - stRecovery - jtRecovery
    residual > 0 →
      (applySTEffectiveDelta s input state delta).stImpermanentLoss = 0 ∧
      (applySTEffectiveDelta s input state delta).jtImpermanentLoss = 0 := by
  dsimp
  by_cases hn : delta < 0
  · have hnp : ¬ 0 < delta := by omega
    simp [applySTEffectiveDelta, hn, hnp]
  · by_cases hp : delta > 0
    · simp [applySTEffectiveDelta, hn, hp]
      omega
    · simp [applySTEffectiveDelta, hn, hp]

theorem recovery_waterfall_orders_liabilities
    (s : AccountantState) (input : SyncInput) :
    recovery_waterfall_orders_liabilities_spec s input := by
  unfold recovery_waterfall_orders_liabilities_spec
  intro _
  simp [previewSyncTrancheAccounting, computeRecoveryTrace]
  constructor
  · intro hlt
    apply jt_residual_implies_st_il_zero s
    rw [Nat.min_eq_right (Nat.le_of_lt hlt)]
    exact Nat.sub_pos_of_lt hlt
  constructor
  · intro hst hjt
    by_cases hp : 0 < (computeEffectiveDeltas s input).deltaSTEffectiveNAV
    · apply st_jt_recovery_implies_st_il_zero s input _ _
      simpa [hp] using And.intro hst hjt
    · simp [hp] at hst
  · intro hres
    by_cases hp : 0 < (computeEffectiveDeltas s input).deltaSTEffectiveNAV
    · apply st_residual_implies_liabilities_zero s input _ _
      simpa [hp] using hres
    · simp [hp] at hres

theorem losses_are_booked_to_the_correct_liability
    (s : AccountantState) (input : SyncInput) :
    losses_are_booked_to_the_correct_liability_spec s input := by
  unfold losses_are_booked_to_the_correct_liability_spec
  intro _
  constructor
  · split <;> simp_all [applyJTEffectiveDelta, initialAllocationState]
  · split <;> simp_all [applySTEffectiveDelta]

private theorem apply_jt_delta_total
    (s : AccountantState) (delta : Int)
    (hsafe : jtLegArithmeticSafe s delta) :
    Int.ofNat (allocationEffectiveNAV (applyJTEffectiveDelta s delta)) =
      Int.ofNat (s.lastSTEffectiveNAV + s.lastJTEffectiveNAV) + delta := by
  unfold jtLegArithmeticSafe at hsafe
  by_cases hn : delta < 0
  · have hmag : (Int.ofNat delta.natAbs) = -delta := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    simp [applyJTEffectiveDelta, initialAllocationState,
      allocationEffectiveNAV, hn, abs_of_neg hn] at hsafe ⊢
    omega
  · by_cases hp : delta > 0
    · have hmag : (Int.ofNat delta.natAbs) = delta :=
        Int.natAbs_of_nonneg (by omega)
      simp [applyJTEffectiveDelta, initialAllocationState,
        allocationEffectiveNAV, hn, hp, abs_of_pos hp] at hsafe ⊢
      omega
    · have hz : delta = 0 := by omega
      simp [applyJTEffectiveDelta, initialAllocationState,
        allocationEffectiveNAV, hz]

private theorem apply_st_delta_total
    (s : AccountantState) (input : SyncInput) (state : AllocationState) (delta : Int)
    (hsafe : stLegArithmeticSafe s input state delta) :
    Int.ofNat (allocationEffectiveNAV (applySTEffectiveDelta s input state delta)) =
      Int.ofNat (allocationEffectiveNAV state) + delta := by
  unfold stLegArithmeticSafe at hsafe
  by_cases hn : delta < 0
  · have hmag : (Int.ofNat delta.natAbs) = -delta := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    simp [applySTEffectiveDelta, allocationEffectiveNAV, hn,
      abs_of_neg hn] at hsafe ⊢
    omega
  · by_cases hp : delta > 0
    · have hmag : (Int.ofNat delta.natAbs) = delta :=
        Int.natAbs_of_nonneg (by omega)
      let residual :=
        delta.natAbs - min delta.natAbs state.stImpermanentLoss -
          min (delta.natAbs - min delta.natAbs state.stImpermanentLoss)
            state.jtImpermanentLoss
      by_cases hres : residual = 0
      · simp [applySTEffectiveDelta, allocationEffectiveNAV, hn, hp,
          abs_of_pos hp, residual, hres] at hsafe ⊢
        omega
      · simp [applySTEffectiveDelta, allocationEffectiveNAV, hn, hp,
          abs_of_pos hp, residual, hres] at hsafe ⊢
        omega
    · have hz : delta = 0 := by omega
      simp [applySTEffectiveDelta, allocationEffectiveNAV, hz]

theorem preview_sync_preserves_nav_conservation
    (s : AccountantState) (input : SyncInput) :
    preview_sync_preserves_nav_conservation_spec s input := by
  unfold preview_sync_preserves_nav_conservation_spec
  intro h
  dsimp [successfulSyncAssumptions] at h
  rcases h with
    ⟨_, hpre, _, _, _, _, _, _, hjtSafe, _, _, _, _, _, hstSafe,
      _, _, _, _, _, _, _, _, _, _, _, _⟩
  let deltas := computeEffectiveDeltas s input
  let afterJT := applyJTEffectiveDelta s deltas.deltaJTEffectiveNAV
  let allocated := applySTEffectiveDelta s input afterJT deltas.deltaSTEffectiveNAV
  have hjt := apply_jt_delta_total s deltas.deltaJTEffectiveNAV hjtSafe
  have hst :=
    apply_st_delta_total s input afterJT deltas.deltaSTEffectiveNAV hstSafe
  have hdelta :
      deltas.deltaSTEffectiveNAV + deltas.deltaJTEffectiveNAV =
        deltas.deltaSTRawNAV + deltas.deltaJTRawNAV := by
    simpa [deltas] using attribution_residual_absorbed_by_junior s input
  have hsum :
      deltas.deltaJTEffectiveNAV + deltas.deltaSTEffectiveNAV =
        deltas.deltaSTRawNAV + deltas.deltaJTRawNAV := by
    omega
  have hpreInt := congrArg Int.ofNat hpre
  have hallocatedInt :
      Int.ofNat (allocationEffectiveNAV allocated) =
        Int.ofNat (input.stRawNAV + input.jtRawNAV) := by
    calc
      Int.ofNat (allocationEffectiveNAV allocated) =
          Int.ofNat (allocationEffectiveNAV afterJT) +
            deltas.deltaSTEffectiveNAV := hst
      _ = Int.ofNat (s.lastSTEffectiveNAV + s.lastJTEffectiveNAV) +
            deltas.deltaJTEffectiveNAV + deltas.deltaSTEffectiveNAV := by
          rw [hjt]
      _ = Int.ofNat (s.lastSTEffectiveNAV + s.lastJTEffectiveNAV) +
            (deltas.deltaJTEffectiveNAV + deltas.deltaSTEffectiveNAV) := by
          ring
      _ = Int.ofNat (s.lastSTRawNAV + s.lastJTRawNAV) +
            (deltas.deltaSTRawNAV + deltas.deltaJTRawNAV) := by
          rw [hpreInt, hsum]
      _ = Int.ofNat (s.lastSTRawNAV + s.lastJTRawNAV) +
            deltas.deltaSTRawNAV + deltas.deltaJTRawNAV := by
          ring
      _ = Int.ofNat (input.stRawNAV + input.jtRawNAV) := by
          simp [deltas, computeEffectiveDeltas, computeNAVDelta]
          ring
  have hallocated :
      allocationEffectiveNAV allocated = input.stRawNAV + input.jtRawNAV :=
    Int.ofNat.inj hallocatedInt
  simpa [previewSyncTrancheAccounting, allocated, afterJT, deltas,
    allocationEffectiveNAV, totalEffectiveNAV, totalRawNAV] using
      And.intro hallocated hallocated

end Benchmark.Cases.Royco.DawnValuationRecovery
