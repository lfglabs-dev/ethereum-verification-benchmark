import Benchmark.Cases.Cork.PoolSolvency.Specs
import Verity.Proofs.Stdlib.Automation
import Mathlib.Tactic.Set
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 4000000

namespace Benchmark.Grindset.Cork

open Benchmark.Cases.Cork.PoolSolvency

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-! ## Part 0: Nat-level ceilDiv helpers -/

private theorem nat_ceilDiv_mul_ge (a b : Nat) (hb : b > 0) :
    ((a + b - 1) / b) * b ≥ a := by
  have hEuclid : b * ((a + b - 1) / b) + (a + b - 1) % b = a + b - 1 :=
    Nat.div_add_mod ..
  have hRem : (a + b - 1) % b < b := Nat.mod_lt _ hb
  have hComm : ((a + b - 1) / b) * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
  omega

private theorem nat_ge_div_of_mul_ge (x y w : Nat) (hw : w > 0) (h : x * w ≥ y) :
    x ≥ y / w := by
  have h1 : y / w * w ≤ y := Nat.div_mul_le_self y w
  have h2 : y / w * w ≤ x * w := Nat.le_trans h1 h
  exact Nat.le_of_mul_le_mul_right h2 hw

/-! ## Part 1: Core algebraic lemma -/

theorem double_ceilDiv_sandwich
    (A B S W : Nat)
    (hB : B > 0) (hW : W > 0) :
    (((((A + B - 1) / B) * S + W - 1) / W) * B ≥ (A * S) / W) := by
  set n := (A + B - 1) / B
  set m := (n * S + W - 1) / W
  have h1 : n * B ≥ A := nat_ceilDiv_mul_ge A B hB
  have h2 : m * W ≥ n * S := nat_ceilDiv_mul_ge (n * S) W hW
  have h5 : m * B * W ≥ A * S := by nlinarith
  exact nat_ge_div_of_mul_ge (m * B) (A * S) W hW h5

/-! ## Part 2: Contract execution theorem -/

-- Helper lemmas for Uint256/Nat bridges under no-overflow
private theorem mul_val_no_ovf (a b : Uint256) (h : a.val * b.val < modulus) :
    (mul a b).val = a.val * b.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem div_val (a b : Uint256) (hb : b.val ≠ 0) :
    (div a b).val = a.val / b.val := by
  simp [HDiv.hDiv, Verity.Core.Uint256.div, hb, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)

private theorem sub_val_no_uf (a b : Uint256) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  simp [HSub.hSub, Verity.Core.Uint256.sub, h, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt)

private theorem add_val' (a b : Uint256) :
    (add a b).val = (a.val + b.val) % modulus := by
  simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]

private theorem mul_eq_zero_no_ovf (a b : Uint256) (h : a.val * b.val < modulus) :
    (mul a b = 0) ↔ (a.val * b.val = 0) := by
  have hv : (mul a b).val = a.val * b.val := mul_val_no_ovf a b h
  constructor
  · intro heq
    have h0 : (mul a b).val = 0 := by rw [heq]; exact Verity.Core.Uint256.val_zero
    omega
  · intro heq
    apply Verity.Core.Uint256.ext
    rw [hv, heq]; exact Verity.Core.Uint256.val_zero.symm

theorem unwind_slot_write (s : ContractState) (referenceAssetsOut : Uint256)
    (hNoOvf1 : referenceAssetsOut.val * (s.storage 4).val < modulus)
    (hNoOvf2 : (referenceAssetsOut.val * (s.storage 4).val) * (s.storage 3).val < modulus)
    (hNoOvf3 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               normalizedReferenceAsset * (s.storage 3).val < modulus) :
    let refFixed := referenceAssetsOut.val * (s.storage 4).val
    let cstSharesOut := (refFixed * (s.storage 3).val) / 1000000000000000000
    let normalizedRef := if refFixed = 0 then 0
      else (refFixed - 1) / (s.storage 5).val + 1
    let assetProduct := normalizedRef * (s.storage 3).val
    let assetsIn := if assetProduct = 0 then 0
      else (assetProduct - 1) / 1000000000000000000 + 1
    let requirePasses := cstSharesOut ≤ (s.storage 2).val
    let s' := ((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd
    (requirePasses →
      s'.storage 0 = ⟨((s.storage 0).val + assetsIn) % modulus,
        Nat.mod_lt _ (by decide : 0 < modulus)⟩ ∧
      s'.storage 1 = s.storage 1 ∧
      s'.storage 2 = ⟨((s.storage 2).val - cstSharesOut) % modulus,
        Nat.mod_lt _ (by decide : 0 < modulus)⟩ ∧
      s'.storage 5 = s.storage 5) ∧
    (¬requirePasses →
      s' = s) := by
  -- Uint256/Nat bridges
  have hMul1Val : (mul referenceAssetsOut (s.storage 4)).val = referenceAssetsOut.val * (s.storage 4).val :=
    mul_val_no_ovf _ _ hNoOvf1
  have hMul2Val : (mul (mul referenceAssetsOut (s.storage 4)) (s.storage 3)).val =
      referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val := by
    rw [mul_val_no_ovf _ _ (by rw [hMul1Val]; exact hNoOvf2), hMul1Val]
  have hDiv1e18Ne : (1000000000000000000 : Uint256).val ≠ 0 := by native_decide
  have h1e18val : (1000000000000000000 : Uint256).val = 1000000000000000000 := by native_decide
  have hDivVal : (div (mul (mul referenceAssetsOut (s.storage 4)) (s.storage 3)) 1000000000000000000).val =
      referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val / 1000000000000000000 := by
    rw [div_val _ _ hDiv1e18Ne, hMul2Val, h1e18val]
  have hCondEquiv : (div (mul (mul referenceAssetsOut (s.storage 4)) (s.storage 3)) 1000000000000000000 ≤ s.storage 2) ↔
      (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val / 1000000000000000000 ≤ (s.storage 2).val) := by
    simp [Verity.Core.Uint256.le_def, hDivVal]
  -- normalizedRef bridge
  have hNormVal :
      (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
       else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1).val =
      (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
       else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) := by
    by_cases hrf : referenceAssetsOut.val * (s.storage 4).val = 0
    · have hMulZ : mul referenceAssetsOut (s.storage 4) = 0 := by
        rw [Verity.Core.Uint256.ext_iff, hMul1Val]; simp [hrf, Verity.Core.Uint256.val_zero]
      simp [hMulZ, hrf, Verity.Core.Uint256.val_zero]
    · have hMulNZ : mul referenceAssetsOut (s.storage 4) ≠ 0 := by
        intro h
        have hv : (mul referenceAssetsOut (s.storage 4)).val = 0 := by rw [h]; exact Verity.Core.Uint256.val_zero
        rw [hMul1Val] at hv; exact hrf hv
      simp only [hMulNZ, hrf, ↓reduceIte]
      have hSub1 : (sub (mul referenceAssetsOut (s.storage 4)) 1).val = referenceAssetsOut.val * (s.storage 4).val - 1 := by
        have hle : (1 : Uint256).val ≤ (mul referenceAssetsOut (s.storage 4)).val := by
          rw [hMul1Val]; simp [Verity.Core.Uint256.val_one]; omega
        rw [sub_val_no_uf _ _ hle, hMul1Val]; simp [Verity.Core.Uint256.val_one]
      -- Handle div by (s.storage 5) which may be zero
      have hDivSubVal : (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)).val =
          (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val := by
        by_cases hColNe : (s.storage 5).val ≠ 0
        · have hd := div_val (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5) hColNe
          rw [hd, hSub1]
        · push_neg at hColNe
          -- When col = 0, Uint256.div returns 0 and Nat.div by 0 returns 0
          simp only [HDiv.hDiv, Verity.Core.Uint256.div, hColNe, ↓reduceIte,
                     Verity.Core.Uint256.ofNat, Nat.zero_mod]
          show 0 = (referenceAssetsOut.val * (s.storage 4).val - 1) / 0
          simp [Nat.div_zero]
      rw [add_val']
      simp only [hDivSubVal, Verity.Core.Uint256.val_one]
      exact Nat.mod_eq_of_lt (by have := Nat.div_le_self (referenceAssetsOut.val * (s.storage 4).val - 1) (s.storage 5).val; omega)
  -- assetProduct bridge
  have hAPOvf :
      (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
       else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1).val *
        (s.storage 3).val < modulus := by rw [hNormVal]; exact hNoOvf3
  have hAPVal : (mul
        (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
         else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
        (s.storage 3)).val =
      (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
       else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) *
        (s.storage 3).val := by
    rw [mul_val_no_ovf _ _ hAPOvf, hNormVal]
  -- assetsIn bridge
  have hAIVal :
      (if mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3) = 0 then (0 : Uint256)
       else add (div (sub (mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3)) 1) 1000000000000000000) 1).val =
      (if (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
           else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) *
            (s.storage 3).val = 0 then 0
       else ((if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
              else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) *
               (s.storage 3).val - 1) / 1000000000000000000 + 1) := by
    set normN := (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
       else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1)
    by_cases hap : normN * (s.storage 3).val = 0
    · have hMulZ : mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3) = 0 := by
        rw [Verity.Core.Uint256.ext_iff, hAPVal]; simp [hap, Verity.Core.Uint256.val_zero]
      simp [hMulZ, hap, Verity.Core.Uint256.val_zero]
    · have hMulNZ : mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3) ≠ 0 := by
        intro h
        have hv : (mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3)).val = 0 := by rw [h]; exact Verity.Core.Uint256.val_zero
        rw [hAPVal] at hv; exact hap hv
      simp only [hMulNZ, hap, ↓reduceIte]
      have hSub1 : (sub (mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3)) 1).val = normN * (s.storage 3).val - 1 := by
        have hle : (1 : Uint256).val ≤ (mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3)).val := by
          rw [hAPVal]; simp [Verity.Core.Uint256.val_one]; omega
        rw [sub_val_no_uf _ _ hle, hAPVal]; simp [Verity.Core.Uint256.val_one]
      have hDivSub2 := div_val (sub (mul
            (if mul referenceAssetsOut (s.storage 4) = 0 then (0 : Uint256)
             else add (div (sub (mul referenceAssetsOut (s.storage 4)) 1) (s.storage 5)) 1)
            (s.storage 3)) 1) 1000000000000000000 hDiv1e18Ne
      rw [add_val']
      simp only [hDivSub2, hSub1, h1e18val, Verity.Core.Uint256.val_one]
      apply Nat.mod_eq_of_lt
      have hd := Nat.div_le_self (normN * (s.storage 3).val - 1) 1000000000000000000
      have hOvf3' : normN * (s.storage 3).val < modulus := by
        exact hNoOvf3
      omega
  -- Unfold monadic chain
  dsimp only [
    CorkUnwindExerciseOther.unwindExerciseOther,
    CorkUnwindExerciseOther.collateralAssetLocked,
    CorkUnwindExerciseOther.swapTotalSupply,
    CorkUnwindExerciseOther.swapBalanceOfPool,
    CorkUnwindExerciseOther.swapRate,
    CorkUnwindExerciseOther.refScaleUp,
    CorkUnwindExerciseOther.colScaleUp,
    getStorage, setStorage, Verity.require,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd]
  -- Case split on require condition
  by_cases hCond : div (mul (mul referenceAssetsOut (s.storage 4)) (s.storage 3)) 1000000000000000000 ≤ s.storage 2
  · -- require passes
    have hCondNat := hCondEquiv.mp hCond
    simp [hCond]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    constructor
    · -- Slot 0
      ext
      simp only [add_val']
      rw [hAIVal]
      simp
    · -- Slot 2
      ext
      have hLeNat : (div (mul (mul referenceAssetsOut (s.storage 4)) (s.storage 3)) 1000000000000000000).val ≤ (s.storage 2).val := by
        rw [hDivVal]; exact hCondNat
      rw [sub_val_no_uf _ _ hLeNat, hDivVal]
      exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s.storage 2).isLt)).symm
  · -- require fails
    have hCondNat : ¬(referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val / 1000000000000000000 ≤ (s.storage 2).val) :=
      fun h => hCond (hCondEquiv.mpr h)
    simp [hCond]
    intro h; exact absurd h hCondNat

/-! ## Part 3: Uint256 value helpers -/

private theorem mul_val_eq (a b : Uint256) (h : a.val * b.val < modulus) :
    (mul a b).val = a.val * b.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem sub_val_eq (a b : Uint256) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  have hlt : a.val - b.val < modulus := Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  have : (Verity.Core.Uint256.sub a b).val = a.val - b.val := by
    simp [Verity.Core.Uint256.sub, h, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hlt
  exact this

/-! ## Part 4: Intermediate Nat lemma -/

private theorem solvency_nat_success
    (locked_v supply_v bal_v col_v : Nat)
    (assetsIn cstShares : Nat)
    (hPre : locked_v * col_v ≥ supply_v - bal_v)
    (hCore : assetsIn * col_v ≥ cstShares)
    (hReq : cstShares ≤ bal_v)
    (hSupBal : bal_v ≤ supply_v) :
    (locked_v + assetsIn) * col_v ≥ supply_v - (bal_v - cstShares) := by
  have hExpand : (locked_v + assetsIn) * col_v = locked_v * col_v + assetsIn * col_v := by ring
  rw [hExpand]; omega

/-! ## Part 5: ceilDiv-to-add conversion -/

private theorem evm_ceilDiv_eq_nat (a b : Nat) (ha : a > 0) (hb : b > 0) :
    (a - 1) / b + 1 = (a + b - 1) / b := by
  have h : a + b - 1 = (a - 1) + b := by omega
  rw [h, Nat.add_div_right _ hb]

/-! ## Part 6: Main solvency theorem -/

theorem solvency_preserved_spec_holds
    (s : ContractState)
    (referenceAssetsOut : Uint256)
    (hSolvencyBefore : mul (s.storage 0) (s.storage 5) ≥ sub (s.storage 1) (s.storage 2))
    (hColScale : s.storage 5 > 0)
    (hRefScale : s.storage 4 > 0)
    (hSwapRate : s.storage 3 > 0)
    (hRefOut : referenceAssetsOut > 0)
    (hNoOvf1 : referenceAssetsOut.val * (s.storage 4).val < modulus)
    (hNoOvf2 : (referenceAssetsOut.val * (s.storage 4).val) * (s.storage 3).val < modulus)
    (hNoOvf3 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               normalizedReferenceAsset * (s.storage 3).val < modulus)
    (hNoOvf4 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               let assetProduct := normalizedReferenceAsset * (s.storage 3).val
               let assetsInWithoutFee := if assetProduct = 0 then 0
                 else (assetProduct - 1) / 1000000000000000000 + 1
               (s.storage 0).val + assetsInWithoutFee < modulus)
    (hNoOvf5 : let refFixed := referenceAssetsOut.val * (s.storage 4).val
               let normalizedReferenceAsset := if refFixed = 0 then 0
                 else (refFixed - 1) / (s.storage 5).val + 1
               let assetProduct := normalizedReferenceAsset * (s.storage 3).val
               let assetsInWithoutFee := if assetProduct = 0 then 0
                 else (assetProduct - 1) / 1000000000000000000 + 1
               ((s.storage 0).val + assetsInWithoutFee) * (s.storage 5).val < modulus)
    (hSupplyGeBal : s.storage 1 ≥ s.storage 2) :
    let s' := ((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd
    solvency_preserved_spec s s' := by
  -- Extract Nat-level positivity
  have hColPos : (s.storage 5).val > 0 := by
    simpa [Verity.Core.Uint256.lt_def] using hColScale
  have hSrPos : (s.storage 3).val > 0 := by
    simpa [Verity.Core.Uint256.lt_def] using hSwapRate
  have hRefOutPos : referenceAssetsOut.val > 0 := by
    simpa [Verity.Core.Uint256.lt_def] using hRefOut
  have hRefScalePos : (s.storage 4).val > 0 := by
    simpa [Verity.Core.Uint256.lt_def] using hRefScale
  have hSupBalNat : (s.storage 2).val ≤ (s.storage 1).val := by
    simpa [Verity.Core.Uint256.le_def] using hSupplyGeBal

  have hRfPos : referenceAssetsOut.val * (s.storage 4).val > 0 :=
    Nat.mul_pos hRefOutPos hRefScalePos
  have hRfNe : referenceAssetsOut.val * (s.storage 4).val ≠ 0 := by omega

  have hNrPos : (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1 > 0 :=
    Nat.succ_pos _

  have hApPos :
      ((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val > 0 :=
    Nat.mul_pos hNrPos hSrPos
  have hApNe :
      ((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val ≠ 0 := by omega

  have hNrCeilDiv :
      (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1 =
      (referenceAssetsOut.val * (s.storage 4).val + (s.storage 5).val - 1) / (s.storage 5).val :=
    evm_ceilDiv_eq_nat _ _ hRfPos hColPos

  have hAiCeilDiv :
      (((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1 =
      (((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val + 1000000000000000000 - 1) / 1000000000000000000 :=
    evm_ceilDiv_eq_nat _ _ hApPos (by decide)

  have hCoreIneq :
      ((((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1) * (s.storage 5).val ≥
      (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000 := by
    rw [hAiCeilDiv, hNrCeilDiv]
    exact double_ceilDiv_sandwich
      (referenceAssetsOut.val * (s.storage 4).val)
      (s.storage 5).val (s.storage 3).val 1000000000000000000
      hColPos (by decide)

  have hNoOvf5_unfolded :
      ((s.storage 0).val +
        ((((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1)) *
        (s.storage 5).val < modulus := by
    have h := hNoOvf5
    change ((s.storage 0).val +
      (if (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
           else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val = 0 then 0
       else ((if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
              else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1)) *
      (s.storage 5).val < modulus at h
    simp only [hRfNe, ↓reduceIte, hApNe] at h
    exact h

  have hNoOvf4_unfolded :
      (s.storage 0).val +
        ((((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1) < modulus := by
    have h := hNoOvf4
    change ((s.storage 0).val +
      (if (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
           else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val = 0 then 0
       else ((if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
              else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1)) < modulus at h
    simp only [hRfNe, ↓reduceIte, hApNe] at h
    exact h

  have hLockedColOvf : (s.storage 0).val * (s.storage 5).val < modulus := by
    calc (s.storage 0).val * (s.storage 5).val
        ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ < modulus := hNoOvf5_unfolded

  have hPreNat : (s.storage 0).val * (s.storage 5).val ≥ (s.storage 1).val - (s.storage 2).val := by
    have hMul := mul_val_eq (s.storage 0) (s.storage 5) hLockedColOvf
    have hSub := sub_val_eq (s.storage 1) (s.storage 2) hSupBalNat
    simp [Verity.Core.Uint256.le_def] at hSolvencyBefore
    omega

  -- Use the slot-write theorem
  have hSlots := unwind_slot_write s referenceAssetsOut hNoOvf1 hNoOvf2 hNoOvf3

  -- Unfold the goal
  show solvency_preserved_spec s
    ((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd
  unfold solvency_preserved_spec
  simp only [Verity.Core.Uint256.le_def]

  by_cases hReq : (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000 ≤ (s.storage 2).val
  case pos =>
    -- Success path
    obtain ⟨hSlot0, hSlot1, hSlot2, hSlot5⟩ := hSlots.1 hReq

    have hS0Val :
        (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 0).val =
        (s.storage 0).val +
          ((((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1) := by
      have hv : (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 0).val =
                ((s.storage 0).val +
                  (if (if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
                       else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val = 0 then 0
                   else ((if referenceAssetsOut.val * (s.storage 4).val = 0 then 0
                          else (referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1)) % modulus := by
        rw [hSlot0]
      rw [hv]
      simp only [hRfNe, ↓reduceIte, hApNe]
      exact Nat.mod_eq_of_lt hNoOvf4_unfolded

    have hS2Val :
        (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 2).val =
        (s.storage 2).val - (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000 := by
      rw [hSlot2]
      have hSubLt : (s.storage 2).val - (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000 < modulus :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s.storage 2).isLt
      exact Nat.mod_eq_of_lt hSubLt

    have hLHS : (mul (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 0)
        (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 5)).val =
        ((s.storage 0).val +
          ((((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1)) *
        (s.storage 5).val := by
      rw [hSlot5]
      simp only [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat, hS0Val]
      exact Nat.mod_eq_of_lt hNoOvf5_unfolded

    have hSubLe : (s.storage 2).val - (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000 ≤ (s.storage 1).val := by omega
    have hRHS : (sub (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 1)
        (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 2)).val =
        (s.storage 1).val - ((s.storage 2).val - (referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000) := by
      have hSubEq := sub_val_eq
        (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 1)
        (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 2)
        (by show (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 2).val ≤
                  (((CorkUnwindExerciseOther.unwindExerciseOther referenceAssetsOut).run s).snd.storage 1).val
            rw [hSlot1, hS2Val]; exact hSubLe)
      rw [hSubEq, hSlot1, hS2Val]

    rw [hLHS, hRHS]
    exact solvency_nat_success (s.storage 0).val (s.storage 1).val (s.storage 2).val
      (s.storage 5).val
      ((((referenceAssetsOut.val * (s.storage 4).val - 1) / (s.storage 5).val + 1) * (s.storage 3).val - 1) / 1000000000000000000 + 1)
      ((referenceAssetsOut.val * (s.storage 4).val * (s.storage 3).val) / 1000000000000000000)
      hPreNat hCoreIneq hReq hSupBalNat

  case neg =>
    -- Revert path: state unchanged
    have hFail := hSlots.2 hReq
    rw [hFail]
    have hMul := mul_val_eq (s.storage 0) (s.storage 5) hLockedColOvf
    have hSub := sub_val_eq (s.storage 1) (s.storage 2) hSupBalNat
    simp [Verity.Core.Uint256.le_def] at hSolvencyBefore
    omega

end Benchmark.Grindset.Cork
