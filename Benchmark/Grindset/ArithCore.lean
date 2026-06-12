/-
  Benchmark.Grindset.ArithCore — generic EVM arithmetic grind pack.

  Contract-agnostic lemmas shipped to every agent workspace. Nothing in this
  module may reference `Benchmark.Cases.*` (enforced by
  scripts/check_grindset_generic.py).

  Contents:
  * Uint256 → Nat `.val` bridges under the usual side conditions
    (`mul_val_of_no_overflow`, `sub_val_of_le`, `div_val`,
    `add_val_of_no_overflow`).
  * Nat-level ceiling-division helpers (`ceildiv_identity`, `ceilDiv_nat_le`,
    `nat_ceilDiv_mul_ge`, `nat_ge_div_of_mul_ge`, `double_ceilDiv_sandwich`).
  * `grind_norm` tags for the upstream `Verity.Proofs.Stdlib.Math` ceilDiv
    correctness lemmas, so `grind` sees them without an explicit hint.

  Status: zero `sorry`, zero new axioms.
-/

import Verity.Core
import Verity.Stdlib.Math
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset.Attr

namespace Benchmark.Grindset.Arith

open Verity

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

/-! ## Nat-level ceiling-division helpers -/

/-- Natural-number identity: for a > 0, b > 0, (a-1)/b + 1 = (a+b-1)/b. -/
theorem ceildiv_identity (a b : Nat) (ha : a > 0) (hb : b > 0) :
    (a - 1) / b + 1 = (a + b - 1) / b := by
  have h : a + b - 1 = (a - 1) + b := by omega
  rw [h, Nat.add_div_right _ hb]

/-- Nat-level: (a+b-1)/b ≤ a when b ≥ 1. -/
theorem ceilDiv_nat_le (a b : Nat) (hb : b ≥ 1) :
    (a + b - 1) / b ≤ a := by
  by_cases ha : a = 0
  · subst ha; simp
    omega
  · have haPos : a > 0 := Nat.pos_of_ne_zero ha
    have hRw : a + b - 1 = (a - 1) + b := by omega
    rw [hRw, Nat.add_div_right _ (by omega : b > 0)]
    have := Nat.div_le_self (a - 1) b; omega

/-- Nat ceiling division times the divisor dominates the dividend. -/
theorem nat_ceilDiv_mul_ge (a b : Nat) (hb : b > 0) :
    ((a + b - 1) / b) * b ≥ a := by
  have hEuclid := Nat.div_add_mod (a + b - 1) b
  have hRem := Nat.mod_lt (a + b - 1) hb
  have hComm : (a + b - 1) / b * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
  omega

/-- From x * w ≥ y conclude x ≥ y / w (Nat division, w > 0). -/
theorem nat_ge_div_of_mul_ge (x y w : Nat) (hw : w > 0) (h : x * w ≥ y) :
    x ≥ y / w := by
  have := Nat.div_le_div_right (c := w) h
  have hxw : x * w / w = x := Nat.mul_div_cancel x hw
  omega

/-- Composing two Nat ceiling divisions preserves the sandwich bound:
    if n = ceil(A/B) and m = ceil(n*S/W) then m*W*B ≥ A*S is implied at the
    Nat level by `nat_ceilDiv_mul_ge` twice; this packages the common
    double-rounding step. -/
theorem double_ceilDiv_sandwich (A B S W : Nat) (_hB : B > 0) (hW : W > 0) :
    (((((A + B - 1) / B) * S) + W - 1) / W) * W ≥ ((A + B - 1) / B) * S := by
  exact nat_ceilDiv_mul_ge (((A + B - 1) / B) * S) W hW

/-! ## Upstream stdlib ceilDiv lemmas, made grind-visible -/

attribute [grind_norm] Verity.Proofs.Stdlib.Math.ceilDiv_zero_left
attribute [grind_norm] Verity.Proofs.Stdlib.Math.ceilDiv_nat_eq
attribute [grind_norm] Verity.Proofs.Stdlib.Math.ceilDiv_mul_ge

end Benchmark.Grindset.Arith
