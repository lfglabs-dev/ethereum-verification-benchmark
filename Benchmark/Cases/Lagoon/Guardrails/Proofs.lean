import Benchmark.Cases.Lagoon.Guardrails.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Lagoon.Guardrails

open Verity
open Verity.EVM

theorem positive_variation_upper_only
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    positiveVariationUpperOnlySpec currentPps nextPps timePast upperRate lowerRate := by
  unfold positiveVariationUpperOnlySpec
  by_cases h : (lowerRate : Int) < 0 ∧ uint256Nat nextPps ≥ uint256Nat currentPps
  · simp [h, isCompliant, positiveBranchCompliant]
  · simp [h]

theorem positive_variation_bounded
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    positiveVariationBoundedSpec currentPps nextPps timePast upperRate lowerRate := by
  unfold positiveVariationBoundedSpec
  by_cases h : 0 ≤ (lowerRate : Int) ∧ uint256Nat nextPps ≥ uint256Nat currentPps
  · have hNotNeg : ¬ (lowerRate : Int) < 0 := by omega
    simp [h, isCompliant, positiveBranchCompliant, hNotNeg]
    constructor <;> intro hBoth <;> exact ⟨hBoth.2, hBoth.1⟩
  · simp [h]

theorem nonnegative_lower_rejects_decrease
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    nonnegativeLowerRejectsDecreaseSpec currentPps nextPps timePast upperRate lowerRate := by
  unfold nonnegativeLowerRejectsDecreaseSpec
  by_cases h : 0 ≤ (lowerRate : Int) ∧ uint256Nat nextPps < uint256Nat currentPps
  · have hNotGe : ¬ uint256Nat nextPps ≥ uint256Nat currentPps := by omega
    simp [h, isCompliant, negativeBranchCompliant, hNotGe]
  · simp [h]

theorem negative_variation_bounded
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    negativeVariationBoundedSpec currentPps nextPps timePast upperRate lowerRate := by
  unfold negativeVariationBoundedSpec
  by_cases h : lowerRateNotMin lowerRate ∧ (lowerRate : Int) < 0 ∧ uint256Nat nextPps < uint256Nat currentPps
  · have hNotGe : ¬ uint256Nat nextPps ≥ uint256Nat currentPps := by omega
    have hNotLowerGe : ¬ 0 ≤ (lowerRate : Int) := by omega
    simp [h, isCompliant, negativeBranchCompliant, hNotGe, hNotLowerGe]
  · simp [h]

theorem exact_compliance
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    exactComplianceSpec currentPps nextPps timePast upperRate lowerRate := by
  unfold exactComplianceSpec
  by_cases hNotMin : lowerRateNotMin lowerRate
  · simp [successfulSolidityArithmeticScope, hNotMin]
    unfold annualizedVariationInsideGuardrails isCompliant
    by_cases hPps : uint256Nat nextPps ≥ uint256Nat currentPps
    · simp [hPps, positiveBranchCompliant]
      by_cases hLowerNeg : (lowerRate : Int) < 0
      · simp [hLowerNeg]
      · simp [hLowerNeg]
        intro _hCurrentNonzero _hTimeNonzero _hArithmeticSafe
        constructor <;> intro hBoth <;> exact ⟨hBoth.2, hBoth.1⟩
    · simp [hPps, negativeBranchCompliant]
  · simp [successfulSolidityArithmeticScope, hNotMin]

abbrev guardrails_positive_upper_only := @positive_variation_upper_only
abbrev guardrails_positive_bounded := @positive_variation_bounded
abbrev guardrails_nonnegative_lower_rejects_decrease := @nonnegative_lower_rejects_decrease
abbrev guardrails_negative_bounded := @negative_variation_bounded
abbrev guardrails_exact_compliance := @exact_compliance

end Benchmark.Cases.Lagoon.Guardrails
