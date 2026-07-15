import Benchmark.Cases.OneInch.XYCSwapCurveSafety.Specs
import Verity.Proofs.Stdlib.Automation

set_option maxHeartbeats 4000000

namespace Benchmark.Cases.OneInch.XYCSwapCurveSafety

open Verity
open Verity.EVM.Uint256

/-!
  Helper lemmas: bridging Uint256 arithmetic to Nat under no-overflow.
-/

private theorem mul_val_of_lt (a b : Uint256) (h : a.val * b.val < modulus) :
    (mul a b).val = a.val * b.val := by
  show (Verity.Core.Uint256.mul a b).val = a.val * b.val
  unfold Verity.Core.Uint256.mul
  rw [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem add_val_of_lt (a b : Uint256) (h : a.val + b.val < modulus) :
    (add a b).val = a.val + b.val := by
  show (Verity.Core.Uint256.add a b).val = a.val + b.val
  unfold Verity.Core.Uint256.add
  rw [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem sub_val_of_le (a b : Uint256) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  show (Verity.Core.Uint256.sub a b).val = a.val - b.val
  unfold Verity.Core.Uint256.sub
  rw [if_pos h]
  show (Verity.Core.Uint256.ofNat (a.val - b.val)).val = a.val - b.val
  rw [Verity.Core.Uint256.val_ofNat]
  have hlt : a.val - b.val < modulus := Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  exact Nat.mod_eq_of_lt hlt

/-- div by nonzero: (div a b).val = a.val / b.val when b ≠ 0 and no overflow -/
private theorem div_val_of_ne_zero (a b : Uint256) (hb : b.val ≠ 0)
    (hDivLt : a.val / b.val < modulus) :
    (div a b).val = a.val / b.val := by
  show (Verity.Core.Uint256.div a b).val = a.val / b.val
  unfold Verity.Core.Uint256.div
  rw [if_neg hb]
  show (Verity.Core.Uint256.ofNat (a.val / b.val)).val = a.val / b.val
  rw [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hDivLt

/-- div by zero: (div a b).val = 0 when b.val = 0 -/
private theorem div_val_of_zero_denom (a b : Uint256) (hb : b.val = 0) :
    (div a b).val = 0 := by
  show (Verity.Core.Uint256.div a b).val = 0
  unfold Verity.Core.Uint256.div
  rw [if_pos hb]
  exact Verity.Core.Uint256.val_zero

private theorem val_10000 : (10000 : Uint256).val = 10000 := by
  show (Verity.Core.Uint256.ofNat 10000).val = 10000
  rw [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt (by decide)

/-!
  Step 1: (sub 10000 feeBps).val = 10000 - feeBps.val when feeBps ≤ 10000.
-/

private theorem sub_10000_feeBps_val (feeBps : Uint256)
    (h : feeBps.val ≤ 10000) :
    (sub 10000 feeBps).val = 10000 - feeBps.val := by
  rw [← val_10000]
  exact sub_val_of_le 10000 feeBps h

/-!
  Step 2: (amountInWithFee amountIn feeBps).val = amountIn.val * (10000 - feeBps.val) / 10000
-/

private theorem amountInWithFee_val
    (amountIn feeBps : Uint256)
    (hFeeRange : feeBps.val ≤ 10000)
    (hMulNoOvf : amountIn.val * (10000 - feeBps.val) < modulus) :
    (amountInWithFee amountIn feeBps).val
      = amountIn.val * (10000 - feeBps.val) / 10000 := by
  -- Unfold amountInWithFee to div form
  show (div (mul amountIn (sub 10000 feeBps)) 10000).val
      = amountIn.val * (10000 - feeBps.val) / 10000
  -- Compute intermediate values
  have hSubVal : (sub 10000 feeBps).val = 10000 - feeBps.val :=
    sub_10000_feeBps_val feeBps hFeeRange
  have hMulNoOvf' : amountIn.val * (sub 10000 feeBps).val < modulus := by
    rw [hSubVal]; exact hMulNoOvf
  have hMulVal : (mul amountIn (sub 10000 feeBps)).val
      = amountIn.val * (10000 - feeBps.val) := by
    rw [mul_val_of_lt _ _ hMulNoOvf', hSubVal]
  -- Peel off the div .val
  have h10000Ne : (10000 : Uint256).val ≠ 0 := by decide
  have hDivLt : (mul amountIn (sub 10000 feeBps)).val / (10000 : Uint256).val < modulus := by
    rw [hMulVal, val_10000]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hMulNoOvf
  rw [div_val_of_ne_zero _ _ h10000Ne hDivLt, hMulVal, val_10000]

/-!
  Step 3: (curveDenominator balanceIn amountIn feeBps).val
         = balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)
-/

private theorem curveDenominator_val
    (balanceIn amountIn feeBps : Uint256)
    (hFeeRange : feeBps.val ≤ 10000)
    (hMulNoOvf : amountIn.val * (10000 - feeBps.val) < modulus)
    (hAddNoOvf : balanceIn.val
      + (amountIn.val * (10000 - feeBps.val) / 10000) < modulus) :
    (curveDenominator balanceIn amountIn feeBps).val
      = balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000) := by
  show (add balanceIn (amountInWithFee amountIn feeBps)).val
      = balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)
  have hFeeVal : (amountInWithFee amountIn feeBps).val
      = amountIn.val * (10000 - feeBps.val) / 10000 :=
    amountInWithFee_val amountIn feeBps hFeeRange hMulNoOvf
  have hAddNoOvf' : balanceIn.val + (amountInWithFee amountIn feeBps).val < modulus := by
    rw [hFeeVal]; exact hAddNoOvf
  rw [add_val_of_lt _ _ hAddNoOvf', hFeeVal]

/-!
  Main theorem: curve safety.

  output * denom ≤ feeAdjusted * balanceOut

  This follows from the integer division rounding-down property.
-/

theorem quoteExactIn_curve_safety
    (balanceIn balanceOut amountIn feeBps : Uint256)
    (hFeeRange : feeBps.val ≤ 10000)
    (hFeeMulNoOvf : amountIn.val * (10000 - feeBps.val) < modulus)
    (hDenomNoOvf : balanceIn.val
      + (amountIn.val * (10000 - feeBps.val) / 10000) < modulus)
    (hProductNoOvf :
      (amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val < modulus) :
    quoteExactIn_curve_safety_spec balanceIn balanceOut amountIn feeBps := by
  -- Unfold the spec
  unfold quoteExactIn_curve_safety_spec quoteExactInOutput
  -- Convert to Nat-level comparison
  simp only [Verity.Core.Uint256.le_def]
  -- Compute intermediate Uint256 values at the Nat level
  have hFeeVal : (amountInWithFee amountIn feeBps).val
      = amountIn.val * (10000 - feeBps.val) / 10000 :=
    amountInWithFee_val amountIn feeBps hFeeRange hFeeMulNoOvf
  have hDenomVal : (curveDenominator balanceIn amountIn feeBps).val
      = balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000) :=
    curveDenominator_val balanceIn amountIn feeBps hFeeRange hFeeMulNoOvf hDenomNoOvf
  -- fee * balanceOut (no overflow)
  have hFeeBalOutNoOvf : (amountInWithFee amountIn feeBps).val * balanceOut.val < modulus := by
    rw [hFeeVal]; exact hProductNoOvf
  have hFeeBalOutVal : (mul (amountInWithFee amountIn feeBps) balanceOut).val
      = (amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val := by
    rw [mul_val_of_lt _ _ hFeeBalOutNoOvf, hFeeVal]
  -- Case split on whether denom = 0
  by_cases hDenomZero :
      balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000) = 0
  · -- denom = 0: EVM div returns 0
    have hDenomUintZero : (curveDenominator balanceIn amountIn feeBps).val = 0 := by
      rw [hDenomVal]; exact hDenomZero
    have hDivZero : (div (mul (amountInWithFee amountIn feeBps) balanceOut)
        (curveDenominator balanceIn amountIn feeBps)).val = 0 :=
      div_val_of_zero_denom _ _ hDenomUintZero
    -- LHS: (mul (div ...) denom).val = 0
    have hLHS : (mul
        (div (mul (amountInWithFee amountIn feeBps) balanceOut)
          (curveDenominator balanceIn amountIn feeBps))
        (curveDenominator balanceIn amountIn feeBps)).val = 0 := by
      show (Verity.Core.Uint256.ofNat
        ((div (mul (amountInWithFee amountIn feeBps) balanceOut)
          (curveDenominator balanceIn amountIn feeBps)).val
         * (curveDenominator balanceIn amountIn feeBps).val)).val = 0
      rw [hDivZero, Verity.Core.Uint256.val_ofNat]
      simp
    rw [hLHS, hFeeBalOutVal]
    omega
  · -- denom > 0
    have hDenomPos : 0 < balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000) :=
      Nat.pos_of_ne_zero hDenomZero
    -- Compute div output value at Nat level
    have hDivNatLt :
      (mul (amountInWithFee amountIn feeBps) balanceOut).val
        / (curveDenominator balanceIn amountIn feeBps).val < modulus := by
      rw [hFeeBalOutVal, hDenomVal]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hProductNoOvf
    have hDivVal : (div (mul (amountInWithFee amountIn feeBps) balanceOut)
        (curveDenominator balanceIn amountIn feeBps)).val
        = (amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val
          / (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)) := by
      rw [div_val_of_ne_zero _ _]
      · rw [hFeeBalOutVal, hDenomVal]
      · rw [hDenomVal]; exact ne_of_gt hDenomPos
      · exact hDivNatLt
    -- LHS * denom product (no overflow)
    have hOutputTimesDenomLt :
      ((amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val
        / (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)))
      * (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)) < modulus := by
      calc ((amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val
            / (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)))
          * (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000))
          ≤ (amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val :=
            Nat.div_mul_le_self _ _
        _ < modulus := hProductNoOvf
    have hLHS : (mul
        (div (mul (amountInWithFee amountIn feeBps) balanceOut)
          (curveDenominator balanceIn amountIn feeBps))
        (curveDenominator balanceIn amountIn feeBps)).val
        = ((amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val
          / (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)))
        * (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)) := by
      show (Verity.Core.Uint256.ofNat
        ((div (mul (amountInWithFee amountIn feeBps) balanceOut)
          (curveDenominator balanceIn amountIn feeBps)).val
         * (curveDenominator balanceIn amountIn feeBps).val)).val
        = ((amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val
          / (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000)))
        * (balanceIn.val + (amountIn.val * (10000 - feeBps.val) / 10000))
      rw [hDivVal, hDenomVal, Verity.Core.Uint256.val_ofNat]
      exact Nat.mod_eq_of_lt hOutputTimesDenomLt
    -- Final: LHS ≤ RHS (integer division rounding down)
    rw [hLHS, hFeeBalOutVal]
    exact Nat.div_mul_le_self _ _

end Benchmark.Cases.OneInch.XYCSwapCurveSafety
