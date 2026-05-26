/-
  Benchmark.Grindset.Arith — arithmetic grind pack for Lido VaulthubLocked.

  Mission A4: provide `@[grind]` / `@[simp]` / `@[grind_norm]`-tagged lemmas
  that help `grind` and `omega` close the three supporting arithmetic obligations
  in the `lido/vaulthub_locked` case:

    1. `ceildiv_sandwich_spec`  — ceilDiv(x,d) * d ≥ x
    2. `shares_conversion_monotone_spec` — getPooledEthBySharesRoundUp is monotone
    3. `locked_funds_solvency_spec` — solvency after syncLocked

  Lemma inventory:
    • `mul_val_of_no_overflow` — Uint256 mul → Nat mul under overflow guard
    • `sub_val_of_le` — Uint256 sub → Nat sub when b ≤ a
    • `div_val` — Uint256 div → Nat div when b ≠ 0
    • `add_val_of_no_overflow` — Uint256 add → Nat add under overflow guard
    • `ceilDiv_val_eq` — ceilDiv a b = (a.val + b.val - 1) / b.val (Nat level)
    • `ceilDiv_le_numerator` — ceilDiv a b ≤ a (Nat-val level)
    • `ceilDiv_mul_ge` — ceilDiv(x,d) * d ≥ x (the sandwich, key lemma)
    • `ceilDiv_monotone` — a ≥ b → ceilDiv a d ≥ ceilDiv b d

  All lemmas carry `@[grind_norm, simp]` so that downstream proofs can
  write `simp only [grind_norm, <spec>]; grind` or `omega`.

  Status: zero `sorry`, zero new axioms.
-/

import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Grindset.Attr

namespace Benchmark.Grindset.Arith

open Verity
open Benchmark.Cases.Lido.VaulthubLocked

/-! ## Uint256 → Nat wrapper lemmas -/

/-- Uint256 multiplication reduces to Nat multiplication when no overflow. -/
@[grind_norm, simp]
theorem mul_val_of_no_overflow (a b : Uint256)
    (h : a.val * b.val < Verity.Core.Uint256.modulus) :
    (Verity.EVM.Uint256.mul a b).val = a.val * b.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

/-- Uint256 subtraction reduces to Nat subtraction when b ≤ a. -/
@[grind_norm, simp]
theorem sub_val_of_le (a b : Uint256)
    (h : b.val ≤ a.val) :
    (Verity.EVM.Uint256.sub a b).val = a.val - b.val := by
  have hlt : a.val - b.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  simp [HSub.hSub, Verity.Core.Uint256.sub, h, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Uint256 division reduces to Nat division when divisor is nonzero. -/
@[grind_norm, simp]
theorem div_val (a b : Uint256) (hb : b.val ≠ 0) :
    (Verity.EVM.Uint256.div a b).val = a.val / b.val := by
  have hlt : a.val / b.val < Verity.Core.Uint256.modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
  simp [HDiv.hDiv, Verity.Core.Uint256.div, hb, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Uint256 addition reduces to Nat addition when no overflow. -/
@[grind_norm, simp]
theorem add_val_of_no_overflow (a b : Uint256)
    (h : a.val + b.val < Verity.Core.Uint256.modulus) :
    (Verity.EVM.Uint256.add a b).val = a.val + b.val := by
  simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

/-! ## ceilDiv val-level unfolding -/

/-- Natural-number identity: for a > 0, b > 0, (a-1)/b + 1 = (a+b-1)/b. -/
private theorem ceildiv_identity (a b : Nat) (ha : a > 0) (hb : b > 0) :
    (a - 1) / b + 1 = (a + b - 1) / b := by
  have h : a + b - 1 = (a - 1) + b := by omega
  rw [h, Nat.add_div_right _ hb]

/-- Nat-level: (a+b-1)/b ≤ a when b ≥ 1. -/
private theorem ceilDiv_nat_le (a b : Nat) (hb : b ≥ 1) :
    (a + b - 1) / b ≤ a := by
  by_cases ha : a = 0
  · subst ha; simp
    right; exact Nat.sub_lt (by omega) (by decide)
  · have haPos : a > 0 := Nat.pos_of_ne_zero ha
    have hRw : a + b - 1 = (a - 1) + b := by omega
    rw [hRw, Nat.add_div_right _ (by omega : b > 0)]
    have := Nat.div_le_self (a - 1) b; omega

/-- ceilDiv(a,b).val = (a.val + b.val - 1) / b.val when b > 0. -/
@[grind_norm, simp]
theorem ceilDiv_val_eq (a b : Uint256) (hb : b.val > 0) :
    (ceilDiv a b).val = (a.val + b.val - 1) / b.val := by
  by_cases ha : a.val = 0
  · -- a = 0 case
    have haEq : a = 0 := Verity.Core.Uint256.ext (by simp [ha, Verity.Core.Uint256.val_zero])
    rw [haEq]
    simp only [ceilDiv, ↓reduceIte, Verity.Core.Uint256.val_zero, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  · -- a > 0 case
    have haPos : a.val > 0 := Nat.pos_of_ne_zero ha
    have haNe : a ≠ 0 := by
      intro h; rw [h] at haPos; simp [Verity.Core.Uint256.val_zero] at haPos
    simp only [ceilDiv, haNe, ↓reduceIte]
    -- sub a 1
    have h1le : (1 : Uint256).val ≤ a.val := by
      simp [Verity.Core.Uint256.val_one]; omega
    have hSubVal : (Verity.EVM.Uint256.sub a 1).val = a.val - 1 := by
      have := Verity.Core.Uint256.sub_eq_of_le h1le
      simp [Verity.Core.Uint256.val_one] at this
      exact this
    -- div (sub a 1) b
    have hbne : b.val ≠ 0 := by omega
    have hDivVal : (Verity.EVM.Uint256.div (Verity.EVM.Uint256.sub a 1) b).val = (a.val - 1) / b.val := by
      simp only [HDiv.hDiv, Verity.Core.Uint256.div, hbne, ↓reduceIte, Verity.Core.Uint256.ofNat, hSubVal]
      have hDivLt : (a.val - 1) / b.val < Verity.Core.Uint256.modulus := by
        calc (a.val - 1) / b.val ≤ a.val - 1 := Nat.div_le_self _ _
          _ < a.val := by omega
          _ < Verity.Core.Uint256.modulus := a.isLt
      exact Nat.mod_eq_of_lt hDivLt
    -- add (div ...) 1
    have hAddLt : (a.val - 1) / b.val + 1 < Verity.Core.Uint256.modulus := by
      have hCeil := ceilDiv_nat_le a.val b.val (by omega)
      calc (a.val - 1) / b.val + 1
          ≤ a.val := by rw [ceildiv_identity a.val b.val haPos hb]; exact hCeil
        _ < Verity.Core.Uint256.modulus := a.isLt
    simp only [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat, hDivVal,
               Verity.Core.Uint256.val_one]
    rw [Nat.mod_eq_of_lt hAddLt]
    exact ceildiv_identity a.val b.val haPos hb

/-- ceilDiv(a,b) ≤ a (Nat val level) when b ≥ 1. -/
@[grind_norm, simp]
theorem ceilDiv_le_numerator (a b : Uint256) (hb : b.val ≥ 1) :
    (ceilDiv a b).val ≤ a.val := by
  rw [ceilDiv_val_eq a b (by omega)]
  exact ceilDiv_nat_le a.val b.val hb

/-! ## The sandwich: ceilDiv(x,d) * d ≥ x -/

/-- ceilDiv(x,d) * d ≥ x when the product does not overflow. Core sandwich lemma. -/
@[grind_norm, simp]
theorem ceilDiv_mul_ge (x d : Uint256) (hd : d.val > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < Verity.Core.Uint256.modulus) :
    (Verity.EVM.Uint256.mul (ceilDiv x d) d).val ≥ x.val := by
  have hMulEq : (Verity.EVM.Uint256.mul (ceilDiv x d) d).val = (ceilDiv x d).val * d.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow
  rw [hMulEq, ceilDiv_val_eq x d hd]
  let q := (x.val + d.val - 1) / d.val
  let r := (x.val + d.val - 1) % d.val
  show x.val ≤ q * d.val
  have hEuclid : d.val * q + r = x.val + d.val - 1 := Nat.div_add_mod ..
  have hRem : r < d.val := Nat.mod_lt _ hd
  have hComm : q * d.val = d.val * q := Nat.mul_comm q d.val
  omega

/-! ## Monotonicity of ceilDiv in the numerator -/

/-- ceilDiv is monotone in the numerator: a ≥ b → ceilDiv a d ≥ ceilDiv b d. -/
@[grind_norm, simp]
theorem ceilDiv_monotone (a b d : Uint256) (hd : d.val > 0)
    (hab : a.val ≥ b.val) :
    (ceilDiv a d).val ≥ (ceilDiv b d).val := by
  rw [ceilDiv_val_eq a d hd, ceilDiv_val_eq b d hd]
  exact Nat.div_le_div_right (by omega)

/-! ## Spec-level convenience lemmas -/

/-- ceildiv_sandwich_spec stated directly for grind consumption. -/
@[grind_norm, simp]
theorem ceildiv_sandwich_spec_holds (x d : Uint256)
    (hd : d > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < Verity.Core.Uint256.modulus) :
    ceildiv_sandwich_spec x d := by
  unfold ceildiv_sandwich_spec
  intro _ _
  simp [Verity.Core.Uint256.le_def]
  exact ceilDiv_mul_ge x d (by simp [Verity.Core.Uint256.lt_def] at hd; exact hd) hNoOverflow

/-- shares_conversion_monotone_spec stated directly for grind consumption. -/
@[grind_norm, simp]
theorem shares_conversion_monotone_spec_holds
    (a b totalPooledEther totalShares : Uint256)
    (hTS : totalShares.val > 0)
    (hNoOverflow : a.val * totalPooledEther.val < Verity.Core.Uint256.modulus) :
    shares_conversion_monotone_spec a b totalPooledEther totalShares := by
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
  rw [ceilDiv_val_eq (Verity.EVM.Uint256.mul a totalPooledEther) totalShares hTS,
      ceilDiv_val_eq (Verity.EVM.Uint256.mul b totalPooledEther) totalShares hTS,
      hMulA, hMulB]
  exact Nat.div_le_div_right (by
    have : b.val * totalPooledEther.val ≤ a.val * totalPooledEther.val :=
      Nat.mul_le_mul_right _ habVal
    omega)

/-! ## Demo theorems -/

/-- Demo: ceildiv_sandwich_spec is closable with the grindset. -/
theorem demo_ceildiv_sandwich (x d : Uint256)
    (hd : d > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < Verity.Core.Uint256.modulus) :
    ceildiv_sandwich_spec x d :=
  ceildiv_sandwich_spec_holds x d hd hNoOverflow

/-- Demo: shares_conversion_monotone_spec is closable with the grindset. -/
theorem demo_shares_conversion_monotone
    (a b totalPooledEther totalShares : Uint256)
    (hTS : totalShares.val > 0)
    (hNoOverflow : a.val * totalPooledEther.val < Verity.Core.Uint256.modulus) :
    shares_conversion_monotone_spec a b totalPooledEther totalShares :=
  shares_conversion_monotone_spec_holds a b totalPooledEther totalShares hTS hNoOverflow

/-- Demo: ceilDiv_mul_ge directly yields the sandwich inequality. -/
theorem demo_sandwich_direct (x d : Uint256)
    (hd : d.val > 0)
    (hNoOverflow : (ceilDiv x d).val * d.val < Verity.Core.Uint256.modulus) :
    (Verity.EVM.Uint256.mul (ceilDiv x d) d).val ≥ x.val :=
  ceilDiv_mul_ge x d hd hNoOverflow

end Benchmark.Grindset.Arith
