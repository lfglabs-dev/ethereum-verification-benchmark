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
    exact Or.inr (by omega : 0 < b)
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

/-! ## Locked funds solvency support -/

/--
  Public pure model for `VaultHubLocked.syncLocked`.
  This mirrors the executable function but keeps the expression small enough for
  downstream candidate proofs to state and reuse.
-/
def lockedPure
    (liabilityShares : Uint256)
    (minimalReserve : Uint256)
    (reserveRatioBP : Uint256)
    (totalPooledEther totalShares : Uint256) : Uint256 :=
  let liability := getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares
  let reserve := ceilDiv (Verity.EVM.Uint256.mul liability reserveRatioBP)
    (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP)
  let effectiveReserve := if reserve ≥ minimalReserve then reserve else minimalReserve
  Verity.EVM.Uint256.add liability effectiveReserve

/-- `syncLocked` writes `lockedPure` to slot 6 and preserves the input slots used by the spec. -/
theorem syncLocked_slot_write (s : ContractState) :
    let s' := ((VaultHubLocked.syncLocked).run s).snd
    s'.storage 6 = lockedPure (s.storage 0) (s.storage 2) (s.storage 3)
      (s.storage 4) (s.storage 5) ∧
    s'.storage 0 = s.storage 0 ∧
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storage 3 = s.storage 3 ∧
    s'.storage 4 = s.storage 4 ∧
    s'.storage 5 = s.storage 5 := by
  repeat' constructor
  all_goals
    simp [VaultHubLocked.syncLocked, lockedPure, TOTAL_BASIS_POINTS,
      getPooledEthBySharesRoundUp, ceilDiv,
      VaultHubLocked.maxLiabilityShares,
      VaultHubLocked.minimalReserve,
      VaultHubLocked.reserveRatioBP, VaultHubLocked.totalPooledEther,
      VaultHubLocked.totalShares, VaultHubLocked.lockedAmount,
      getStorage, setStorage, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.snd]

/-- Core arithmetic fact behind the Lido locked-funds solvency task. -/
theorem locked_funds_solvency_math
    (maxLiabilityShares liabilityShares : Uint256)
    (minimalReserve reserveRatioBP : Uint256)
    (totalPooledEther totalShares : Uint256)
    (hMaxLS : maxLiabilityShares ≥ liabilityShares)
    (hRR_pos : reserveRatioBP > 0)
    (hRR_lt : reserveRatioBP < TOTAL_BASIS_POINTS)
    (hTS : totalShares > 0)
    (_hTPE : totalPooledEther > 0)
    (hNoOverflow1 : maxLiabilityShares.val * totalPooledEther.val < Verity.Core.Uint256.modulus)
    (hNoOverflow2 : (getPooledEthBySharesRoundUp maxLiabilityShares totalPooledEther totalShares).val
                    * reserveRatioBP.val < Verity.Core.Uint256.modulus)
    (hNoOverflow3 : let liab := getPooledEthBySharesRoundUp maxLiabilityShares totalPooledEther totalShares
                    let reserve := ceilDiv (Verity.EVM.Uint256.mul liab reserveRatioBP)
                      (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP)
                    let eff := if reserve ≥ minimalReserve then reserve else minimalReserve
                    liab.val + eff.val < Verity.Core.Uint256.modulus)
    (hNoOverflow4 : (lockedPure maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares).val
                    * (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP).val <
                      Verity.Core.Uint256.modulus)
    (hNoOverflow5 : (getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares).val
                    * TOTAL_BASIS_POINTS.val < Verity.Core.Uint256.modulus) :
    Verity.EVM.Uint256.mul
      (lockedPure maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares)
      (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP)
      ≥
    Verity.EVM.Uint256.mul
      (getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares)
      TOTAL_BASIS_POINTS := by
  simp [Verity.Core.Uint256.le_def]
  set liabilityMax := getPooledEthBySharesRoundUp maxLiabilityShares totalPooledEther totalShares
  set liabilityLS := getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares
  set complement := Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP
  set lockedVal := lockedPure maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares

  have hLHSEq : (Verity.EVM.Uint256.mul lockedVal complement).val =
      lockedVal.val * complement.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow4
  have hRHSEq : (Verity.EVM.Uint256.mul liabilityLS TOTAL_BASIS_POINTS).val =
      liabilityLS.val * TOTAL_BASIS_POINTS.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow5
  rw [hLHSEq, hRHSEq]

  have hMonotone : liabilityMax.val ≥ liabilityLS.val := by
    have hTSVal : totalShares.val > 0 := by
      simpa [Verity.Core.Uint256.lt_def] using hTS
    have hmono := shares_conversion_monotone_spec_holds maxLiabilityShares liabilityShares
      totalPooledEther totalShares hTSVal hNoOverflow1
    unfold shares_conversion_monotone_spec at hmono
    have hM := hmono hMaxLS hNoOverflow1
    simp [Verity.Core.Uint256.le_def] at hM
    exact hM

  suffices h : lockedVal.val * complement.val ≥ liabilityMax.val * TOTAL_BASIS_POINTS.val by
    exact Nat.le_trans (Nat.mul_le_mul_right _ hMonotone) h

  have hRRVal : reserveRatioBP.val > 0 := by
    simp [Verity.Core.Uint256.lt_def] at hRR_pos
    exact hRR_pos
  have hRRLtBP : reserveRatioBP.val < TOTAL_BASIS_POINTS.val := by
    simp [Verity.Core.Uint256.lt_def] at hRR_lt
    exact hRR_lt
  have hComplementVal : complement.val = TOTAL_BASIS_POINTS.val - reserveRatioBP.val := by
    have hle : reserveRatioBP.val ≤ TOTAL_BASIS_POINTS.val := Nat.le_of_lt hRRLtBP
    simp [complement, HSub.hSub, Verity.Core.Uint256.sub, hle, Verity.Core.Uint256.ofNat]
    have : TOTAL_BASIS_POINTS.val - reserveRatioBP.val < Verity.Core.Uint256.modulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) TOTAL_BASIS_POINTS.isLt
    exact Nat.mod_eq_of_lt this
  have hCompPos : complement.val > 0 := by
    rw [hComplementVal]
    omega
  have hBPEq : TOTAL_BASIS_POINTS.val = complement.val + reserveRatioBP.val := by
    rw [hComplementVal]
    omega

  set reserve := ceilDiv (Verity.EVM.Uint256.mul liabilityMax reserveRatioBP) complement
  set effectiveReserve := if reserve ≥ minimalReserve then reserve else minimalReserve

  have hMulLiabRR : (Verity.EVM.Uint256.mul liabilityMax reserveRatioBP).val =
      liabilityMax.val * reserveRatioBP.val := by
    simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoOverflow2

  have hReserveEq :
      reserve.val = (liabilityMax.val * reserveRatioBP.val + complement.val - 1) /
        complement.val := by
    simp only [reserve]
    rw [ceilDiv_val_eq (Verity.EVM.Uint256.mul liabilityMax reserveRatioBP) complement hCompPos,
      hMulLiabRR]

  have hReserveProp : reserve.val * complement.val ≥ liabilityMax.val * reserveRatioBP.val := by
    rw [hReserveEq]
    let n := liabilityMax.val * reserveRatioBP.val + complement.val - 1
    let q := n / complement.val
    let r := n % complement.val
    show liabilityMax.val * reserveRatioBP.val ≤ q * complement.val
    have hEuclid : complement.val * q + r = n := Nat.div_add_mod ..
    have hRem : r < complement.val := Nat.mod_lt _ hCompPos
    have hComm : q * complement.val = complement.val * q := Nat.mul_comm q complement.val
    omega

  have hEffGe : effectiveReserve.val ≥ reserve.val := by
    simp only [effectiveReserve]
    by_cases h : reserve ≥ minimalReserve
    · simp [h]
    · simp [h]
      simp [Verity.Core.Uint256.le_def] at h ⊢
      omega

  have hEffProp :
      effectiveReserve.val * complement.val ≥ liabilityMax.val * reserveRatioBP.val :=
    Nat.le_trans hReserveProp (Nat.mul_le_mul_right _ hEffGe)

  have hNoAddOverflow : liabilityMax.val + effectiveReserve.val < Verity.Core.Uint256.modulus :=
    hNoOverflow3

  have hLockedEq : lockedVal.val = liabilityMax.val + effectiveReserve.val := by
    change (lockedPure maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares).val
      = liabilityMax.val + effectiveReserve.val
    simp only [lockedPure, getPooledEthBySharesRoundUp]
    simp only [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoAddOverflow

  rw [hLockedEq, hBPEq, Nat.mul_add, Nat.add_mul]
  exact Nat.add_le_add_left hEffProp _

/-- Full public helper for `lido/vaulthub_locked/locked_funds_solvency`. -/
theorem locked_funds_solvency_spec_holds
    (s : ContractState)
    (hMaxLS : s.storage 0 ≥ s.storage 1)
    (hRR_pos : s.storage 3 > 0)
    (hRR_lt : s.storage 3 < TOTAL_BASIS_POINTS)
    (hTS : s.storage 5 > 0)
    (hTPE : s.storage 4 > 0)
    (hNoOverflow1 : (s.storage 0).val * (s.storage 4).val < Verity.Core.Uint256.modulus)
    (hNoOverflow2 : (getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)).val
                    * (s.storage 3).val < Verity.Core.Uint256.modulus)
    (hNoOverflow3 : let liab := getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)
                    let reserve := ceilDiv (Verity.EVM.Uint256.mul liab (s.storage 3))
                      (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS (s.storage 3))
                    let eff := if reserve ≥ s.storage 2 then reserve else s.storage 2
                    liab.val + eff.val < Verity.Core.Uint256.modulus)
    (hNoOverflow4 : let liab := getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)
                    let reserve := ceilDiv (Verity.EVM.Uint256.mul liab (s.storage 3))
                      (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS (s.storage 3))
                    let eff := if reserve ≥ s.storage 2 then reserve else s.storage 2
                    (Verity.EVM.Uint256.add liab eff).val *
                      (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS (s.storage 3)).val <
                      Verity.Core.Uint256.modulus)
    (hNoOverflow5 : (getPooledEthBySharesRoundUp (s.storage 1) (s.storage 4) (s.storage 5)).val
                    * TOTAL_BASIS_POINTS.val < Verity.Core.Uint256.modulus) :
    let s' := ((VaultHubLocked.syncLocked).run s).snd
    locked_funds_solvency_spec s s' := by
  rcases syncLocked_slot_write s with ⟨hSlot6, _hSlot0, hSlot1, _hSlot2, hSlot3, hSlot4, hSlot5⟩
  simp only [locked_funds_solvency_spec, hSlot6, hSlot1, hSlot3, hSlot4, hSlot5]
  exact locked_funds_solvency_math (s.storage 0) (s.storage 1) (s.storage 2)
    (s.storage 3) (s.storage 4) (s.storage 5) hMaxLS hRR_pos hRR_lt hTS hTPE
    hNoOverflow1 hNoOverflow2 hNoOverflow3 hNoOverflow4 hNoOverflow5

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
