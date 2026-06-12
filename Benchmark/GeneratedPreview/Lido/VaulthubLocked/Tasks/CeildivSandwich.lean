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

/-- Private helper (recovered from the deleted case grindset):
ceilDiv(x,d) * d ≥ x when the product does not overflow. -/
private theorem ceilDiv_mul_ge' (x d : Uint256) (hd : d.val > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < Verity.Core.Uint256.modulus) :
    (Verity.EVM.Uint256.mul (ceilDiv x d) d).val ≥ x.val := by
  have hMulEq : (Verity.EVM.Uint256.mul (ceilDiv x d) d).val = (ceilDiv x d).val * d.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow
  rw [hMulEq, ceilDiv_val_eq' x d hd]
  let q := (x.val + d.val - 1) / d.val
  let r := (x.val + d.val - 1) % d.val
  show x.val ≤ q * d.val
  have hEuclid : d.val * q + r = x.val + d.val - 1 := Nat.div_add_mod ..
  have hRem : r < d.val := Nat.mod_lt _ hd
  have hComm : q * d.val = d.val * q := Nat.mul_comm q d.val
  omega

/--
Supporting arithmetic lemma: ceil(x/d) * d >= x for positive d.
This is a key bound used in the F-01 solvency proof to connect the
ceiling division in the reserve computation back to the original amount.
-/
theorem ceildiv_sandwich
    (x d : Uint256)
    (hd : d > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < modulus) :
    ceildiv_sandwich_spec x d := by
  unfold ceildiv_sandwich_spec
  intro _ _
  simp [Verity.Core.Uint256.le_def]
  exact ceilDiv_mul_ge' x d (by simp [Verity.Core.Uint256.lt_def] at hd; exact hd) hNoOverflow

end Benchmark.Cases.Lido.VaulthubLocked
