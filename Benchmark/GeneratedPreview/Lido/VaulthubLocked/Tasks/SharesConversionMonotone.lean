import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity
open Verity.EVM.Uint256

/-- Private helper (recovered from the deleted case grindset):
ceilDiv(a,b).val = (a.val + b.val - 1) / b.val when b > 0. -/
private theorem ceilDiv_val_eq' (a b : Uint256) (hb : b.val > 0) :
    (ceilDiv a b).val = (a.val + b.val - 1) / b.val := by
  by_cases ha : a.val = 0
  · have haEq : a = 0 := Verity.Core.Uint256.ext (by simp [ha, Verity.Core.Uint256.val_zero])
    rw [haEq]
    simp only [ceilDiv, ↓reduceIte, Verity.Core.Uint256.val_zero, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  · have haPos : a.val > 0 := Nat.pos_of_ne_zero ha
    have haNe : a ≠ 0 := by
      intro h; rw [h] at haPos; simp [Verity.Core.Uint256.val_zero] at haPos
    simp only [ceilDiv, haNe, ↓reduceIte]
    have h1le : (1 : Uint256).val ≤ a.val := by
      simp [Verity.Core.Uint256.val_one]; omega
    have hSubVal : (Verity.EVM.Uint256.sub a 1).val = a.val - 1 := by
      have := Verity.Core.Uint256.sub_eq_of_le h1le
      simp [Verity.Core.Uint256.val_one] at this
      exact this
    have hbne : b.val ≠ 0 := by omega
    have hDivVal : (Verity.EVM.Uint256.div (Verity.EVM.Uint256.sub a 1) b).val = (a.val - 1) / b.val := by
      simp only [HDiv.hDiv, Verity.Core.Uint256.div, hbne, ↓reduceIte, Verity.Core.Uint256.ofNat, hSubVal]
      have hDivLt : (a.val - 1) / b.val < Verity.Core.Uint256.modulus := by
        calc (a.val - 1) / b.val ≤ a.val - 1 := Nat.div_le_self _ _
          _ < a.val := by omega
          _ < Verity.Core.Uint256.modulus := a.isLt
      exact Nat.mod_eq_of_lt hDivLt
    have hAddLt : (a.val - 1) / b.val + 1 < Verity.Core.Uint256.modulus := by
      have hCeil := Benchmark.Grindset.Arith.ceilDiv_nat_le a.val b.val (by omega)
      calc (a.val - 1) / b.val + 1
          ≤ a.val := by
            rw [Benchmark.Grindset.Arith.ceildiv_identity a.val b.val haPos hb]; exact hCeil
        _ < Verity.Core.Uint256.modulus := a.isLt
    simp only [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat, hDivVal,
               Verity.Core.Uint256.val_one]
    rw [Nat.mod_eq_of_lt hAddLt]
    exact Benchmark.Grindset.Arith.ceildiv_identity a.val b.val haPos hb

/--
Supporting arithmetic lemma: getPooledEthBySharesRoundUp is monotone in shares.
If a >= b then getPooledEthBySharesRoundUp(a) >= getPooledEthBySharesRoundUp(b).
Needed to lift the F-01 solvency bound from maxLiabilityShares to liabilityShares.
-/
theorem shares_conversion_monotone
    (a b : Uint256)
    (totalPooledEther totalShares : Uint256)
    (hTS : totalShares > 0)
    (hNoOverflow : a.val * totalPooledEther.val < modulus) :
    shares_conversion_monotone_spec a b totalPooledEther totalShares := by
  have hTSVal : totalShares.val > 0 := by
    simpa [Verity.Core.Uint256.lt_def] using hTS
  unfold shares_conversion_monotone_spec
  intro hab hNoOv
  unfold getPooledEthBySharesRoundUp
  simp [Verity.Core.Uint256.le_def]
  have habVal : b.val ≤ a.val := by
    simp [Verity.Core.Uint256.le_def] at hab; exact hab
  have hBNoOverflow : b.val * totalPooledEther.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ habVal) hNoOverflow
  have hMulA : (Verity.EVM.Uint256.mul a totalPooledEther).val = a.val * totalPooledEther.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow
  have hMulB : (Verity.EVM.Uint256.mul b totalPooledEther).val = b.val * totalPooledEther.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hBNoOverflow
  rw [ceilDiv_val_eq' (Verity.EVM.Uint256.mul a totalPooledEther) totalShares hTSVal,
      ceilDiv_val_eq' (Verity.EVM.Uint256.mul b totalPooledEther) totalShares hTSVal,
      hMulA, hMulB]
  exact Nat.div_le_div_right (by
    have : b.val * totalPooledEther.val ≤ a.val * totalPooledEther.val :=
      Nat.mul_le_mul_right _ habVal
    omega)

end Benchmark.Cases.Lido.VaulthubLocked
