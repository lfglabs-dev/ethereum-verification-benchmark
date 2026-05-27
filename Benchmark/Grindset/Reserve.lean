import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Benchmark.Grindset.Attr
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Grindset.Reserve

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Math
open Benchmark.Cases.Reserve.AuctionPriceBand

private theorem neg_ofUint256_toInt_nonpositive
    (v : Uint256)
    (hFits : v.val ≤ Verity.EVM.MAX_INT256.toNat) :
    Verity.EVM.Int256.toInt
      (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)) ≤ 0 := by
  have hSigBit : v.val < Verity.Core.Int256.signBit := by
    have h : Verity.EVM.MAX_INT256.toNat = Verity.Core.Int256.signBit - 1 := by
      decide
    rw [h] at hFits
    have : 0 < Verity.Core.Int256.signBit := by decide
    omega
  have hVLtMod : v.val < Verity.Core.Uint256.modulus := v.isLt
  have hMod : Verity.Core.Uint256.modulus = 2 * Verity.Core.Int256.signBit := by
    decide
  by_cases hZero : v.val = 0
  · have hWordEqZero :
        (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val = 0 := by
      show (Verity.Core.Uint256.ofNat
              (Verity.Core.Int256.modulus
                - (Verity.Core.Int256.ofUint256 v).word.val)).val = 0
      have hOfUint : (Verity.Core.Int256.ofUint256 v).word = v := rfl
      rw [hOfUint, hZero]
      show (Verity.Core.Uint256.ofNat (Verity.Core.Int256.modulus - 0)).val = 0
      simp [Verity.Core.Uint256.ofNat, Verity.Core.Int256.modulus]
    have hLt :
        (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val
          < Verity.Core.Int256.signBit := by
      rw [hWordEqZero]; decide
    show Verity.Core.Int256.toInt _ ≤ 0
    have hSigBitPos : 0 < Verity.Core.Int256.signBit := by decide
    simp [Verity.Core.Int256.toInt, hLt, hWordEqZero, hSigBitPos]
  · have hVPos : 0 < v.val := Nat.pos_of_ne_zero hZero
    have hSubLt :
        Verity.Core.Int256.modulus - v.val < Verity.Core.Uint256.modulus := by
      show Verity.Core.Uint256.modulus - v.val < Verity.Core.Uint256.modulus
      omega
    have hWordVal :
        (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val
          = Verity.Core.Int256.modulus - v.val := by
      show (Verity.Core.Uint256.ofNat
              (Verity.Core.Int256.modulus
                - (Verity.Core.Int256.ofUint256 v).word.val)).val
            = Verity.Core.Int256.modulus - v.val
      have hOfUint : (Verity.Core.Int256.ofUint256 v).word = v := rfl
      rw [hOfUint]
      show (Verity.Core.Uint256.ofNat
              (Verity.Core.Int256.modulus - v.val)).val
            = Verity.Core.Int256.modulus - v.val
      simp [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hSubLt]
    have hGe :
        Verity.Core.Int256.signBit
          ≤ (Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val := by
      rw [hWordVal]
      show Verity.Core.Int256.signBit ≤ Verity.Core.Uint256.modulus - v.val
      omega
    show Verity.Core.Int256.toInt _ ≤ 0
    have hNotLt :
        ¬ ((Verity.EVM.Int256.neg (Verity.EVM.Int256.ofUint256 v)).word.val
              < Verity.Core.Int256.signBit) :=
      Nat.not_lt_of_ge hGe
    simp only [Verity.Core.Int256.toInt, hNotLt, if_false]
    rw [hWordVal]
    have hVLe : v.val ≤ Verity.Core.Int256.modulus := by
      show v.val ≤ Verity.Core.Uint256.modulus
      omega
    have hCastEq :
        Int.ofNat (Verity.Core.Int256.modulus - v.val)
          = Int.ofNat Verity.Core.Int256.modulus - Int.ofNat v.val := by
      have := Int.ofNat_sub hVLe
      simpa using this
    rw [hCastEq]
    have hVNonneg : (0 : Int) ≤ Int.ofNat v.val := Int.natCast_nonneg _
    omega

theorem mulDivUp_le_self_of_le
    (a b c : Uint256)
    (hBC : b ≤ c)
    (hCPos : c.val > 0)
    (hNoOverflow : a.val * c.val + c.val - 1 < Verity.Core.Uint256.modulus) :
    mulDivUp a b c ≤ a := by
  show (mulDivUp a b c).val ≤ a.val
  have hC : c ≠ 0 := by
    intro h
    apply Nat.lt_irrefl 0
    have : c.val = 0 := by
      simpa using congrArg (fun x : Uint256 => x.val) h
    omega
  have hBC_nat : b.val ≤ c.val := hBC
  have hAB_le_AC : a.val * b.val ≤ a.val * c.val :=
    Nat.mul_le_mul_left a.val hBC_nat
  have hCPred : c.val - 1 + 1 = c.val := Nat.succ_pred_eq_of_pos hCPos
  have hMaxEq : Verity.Core.Uint256.modulus = MAX_UINT256 + 1 := by
    decide
  have hNumLeMax : a.val * b.val + (c.val - 1) ≤ MAX_UINT256 := by
    have hStep : a.val * b.val + (c.val - 1) ≤ a.val * c.val + (c.val - 1) :=
      Nat.add_le_add_right hAB_le_AC _
    omega
  rw [mulDivUp_nat_eq a b c hC hNumLeMax]
  rw [Nat.div_le_iff_le_mul_add_pred hCPos, Nat.mul_comm c.val a.val]
  exact Nat.add_le_add_right hAB_le_AC _

set_option maxRecDepth 4096

theorem price_upper_bound_spec_holds
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256)
    (hBand :
      mulDivUp sellPrices.low D27 buyPrices.high
        ≤ mulDivUp sellPrices.high D27 buyPrices.low)
    (hSafe : InteriorSafe sellPrices buyPrices auction_startTime auction_endTime block_timestamp) :
    price_upper_bound_spec sellPrices buyPrices auction_startTime auction_endTime block_timestamp := by
  unfold price_upper_bound_spec _price
  by_cases h1 : block_timestamp == auction_startTime
  · simp [h1]
  · by_cases h2 : block_timestamp == auction_endTime
    · simpa [h1, h2] using hBand
    · simp only [h1, h2, Bool.false_eq_true, if_false]
      have hKEFits := hSafe.hKElapsedFitsInt
      have hOverflow := hSafe.hMulNoOverflow
      simp only at hKEFits hOverflow
      split
      · exact hBand
      · have hNegKE_nonpos := neg_ofUint256_toInt_nonpositive _ hKEFits
        have hExpLeD18 := MathLib_exp_nonpositive_le_D18 _ hNegKE_nonpos
        have hD18Pos : D18.val > 0 := by show (1000000000000000000 : Nat) > 0; decide
        exact mulDivUp_le_self_of_le _ _ _ hExpLeD18 hD18Pos hOverflow

end Benchmark.Grindset.Reserve
