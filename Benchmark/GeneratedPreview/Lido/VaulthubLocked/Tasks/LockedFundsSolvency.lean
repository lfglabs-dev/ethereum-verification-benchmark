import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Lido.VaulthubLocked

open Verity
open Verity.EVM.Uint256

/-! Private helpers recovered from the deleted case grindset
(`Benchmark.Grindset.Arith` for `lido/vaulthub_locked`). -/

/-- ceilDiv(a,b).val = (a.val + b.val - 1) / b.val when b > 0. -/
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

/-- shares_conversion_monotone_spec stated directly. -/
private theorem shares_conversion_monotone_spec_holds'
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
  rw [ceilDiv_val_eq' (Verity.EVM.Uint256.mul a totalPooledEther) totalShares hTS,
      ceilDiv_val_eq' (Verity.EVM.Uint256.mul b totalPooledEther) totalShares hTS,
      hMulA, hMulB]
  exact Nat.div_le_div_right (by
    have : b.val * totalPooledEther.val ≤ a.val * totalPooledEther.val :=
      Nat.mul_le_mul_right _ habVal
    omega)

/-- Public pure model for `VaultHubLocked.syncLocked`. -/
private def lockedPure'
    (liabilityShares : Uint256)
    (minimalReserve : Uint256)
    (reserveRatioBP : Uint256)
    (totalPooledEther totalShares : Uint256) : Uint256 :=
  let liability := getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares
  let reserve := ceilDiv (Verity.EVM.Uint256.mul liability reserveRatioBP)
    (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP)
  let effectiveReserve := if reserve ≥ minimalReserve then reserve else minimalReserve
  Verity.EVM.Uint256.add liability effectiveReserve

/-- `syncLocked` writes `lockedPure'` to slot 6 and preserves the input slots. -/
private theorem syncLocked_slot_write' (s : ContractState) :
    let s' := ((VaultHubLocked.syncLocked).run s).snd
    s'.storage 6 = lockedPure' (s.storage 0) (s.storage 2) (s.storage 3)
      (s.storage 4) (s.storage 5) ∧
    s'.storage 0 = s.storage 0 ∧
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storage 3 = s.storage 3 ∧
    s'.storage 4 = s.storage 4 ∧
    s'.storage 5 = s.storage 5 := by
  repeat' constructor
  all_goals
    simp [VaultHubLocked.syncLocked, lockedPure', TOTAL_BASIS_POINTS,
      getPooledEthBySharesRoundUp, ceilDiv,
      VaultHubLocked.maxLiabilityShares,
      VaultHubLocked.minimalReserve,
      VaultHubLocked.reserveRatioBP, VaultHubLocked.totalPooledEther,
      VaultHubLocked.totalShares, VaultHubLocked.lockedAmount,
      getStorage, setStorage, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.snd]

/-- Core arithmetic fact behind the locked-funds solvency task. -/
private theorem locked_funds_solvency_math'
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
    (hNoOverflow4 : (lockedPure' maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares).val
                    * (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP).val <
                      Verity.Core.Uint256.modulus)
    (hNoOverflow5 : (getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares).val
                    * TOTAL_BASIS_POINTS.val < Verity.Core.Uint256.modulus) :
    Verity.EVM.Uint256.mul
      (lockedPure' maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares)
      (Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP)
      ≥
    Verity.EVM.Uint256.mul
      (getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares)
      TOTAL_BASIS_POINTS := by
  simp [Verity.Core.Uint256.le_def]
  set liabilityMax := getPooledEthBySharesRoundUp maxLiabilityShares totalPooledEther totalShares
  set liabilityLS := getPooledEthBySharesRoundUp liabilityShares totalPooledEther totalShares
  set complement := Verity.EVM.Uint256.sub TOTAL_BASIS_POINTS reserveRatioBP
  set lockedVal := lockedPure' maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares

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
    have hmono := shares_conversion_monotone_spec_holds' maxLiabilityShares liabilityShares
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

  have hReserveEq : reserve.val =
      (liabilityMax.val * reserveRatioBP.val + complement.val - 1) / complement.val := by
    rw [ceilDiv_val_eq' (Verity.EVM.Uint256.mul liabilityMax reserveRatioBP) complement hCompPos,
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
    change (lockedPure' maxLiabilityShares minimalReserve reserveRatioBP totalPooledEther totalShares).val
      = liabilityMax.val + effectiveReserve.val
    simp only [lockedPure', getPooledEthBySharesRoundUp]
    simp only [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
    exact Nat.mod_eq_of_lt hNoAddOverflow

  rw [hLockedEq, hBPEq, Nat.mul_add, Nat.add_mul]
  exact Nat.add_le_add_left hEffProp _

/--
Certora F-01: Locked funds solvency.
After executing `syncLocked`, the stored locked amount (slot 6) multiplied by
the reserve ratio complement is at least the liability (from liabilityShares
in slot 1) multiplied by total basis points:

  s'.storage 6 * (BP - RR) >= getPooledEthBySharesRoundUp(LS, TPE, TS) * BP

The proof requires a case split on whether the computed reserve or the minimal
reserve dominates, then algebraic manipulation using the ceilDiv sandwich bound
and share conversion monotonicity.
-/
theorem locked_funds_solvency
    (s : ContractState)
    -- Axioms
    (hMaxLS : s.storage 0 ≥ s.storage 1)
    (hRR_pos : s.storage 3 > 0)
    (hRR_lt : s.storage 3 < TOTAL_BASIS_POINTS)
    (hTS : s.storage 5 > 0)
    (hTPE : s.storage 4 > 0)
    -- No overflow: maxLiabilityShares * totalPooledEther fits in Uint256
    (hNoOverflow1 : (s.storage 0).val * (s.storage 4).val < modulus)
    -- No overflow: liability * reserveRatioBP fits in Uint256
    (hNoOverflow2 : (getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)).val
                    * (s.storage 3).val < modulus)
    -- No overflow: the add inside locked (liability + effectiveReserve) fits in Uint256
    (hNoOverflow3 : let liab := getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)
                    let reserve := ceilDiv (mul liab (s.storage 3)) (sub TOTAL_BASIS_POINTS (s.storage 3))
                    let eff := if reserve ≥ s.storage 2 then reserve else s.storage 2
                    liab.val + eff.val < modulus)
    -- No overflow: locked * (BP - RR) fits in Uint256
    (hNoOverflow4 : let liab := getPooledEthBySharesRoundUp (s.storage 0) (s.storage 4) (s.storage 5)
                    let reserve := ceilDiv (mul liab (s.storage 3)) (sub TOTAL_BASIS_POINTS (s.storage 3))
                    let eff := if reserve ≥ s.storage 2 then reserve else s.storage 2
                    (add liab eff).val * (sub TOTAL_BASIS_POINTS (s.storage 3)).val < modulus)
    -- No overflow: liability * BP fits in Uint256
    (hNoOverflow5 : (getPooledEthBySharesRoundUp (s.storage 1) (s.storage 4) (s.storage 5)).val
                    * TOTAL_BASIS_POINTS.val < modulus) :
    let s' := ((VaultHubLocked.syncLocked).run s).snd
    locked_funds_solvency_spec s s' := by
  rcases syncLocked_slot_write' s with ⟨hSlot6, _hSlot0, hSlot1, _hSlot2, hSlot3, hSlot4, hSlot5⟩
  simp only [locked_funds_solvency_spec, hSlot6, hSlot1, hSlot3, hSlot4, hSlot5]
  exact locked_funds_solvency_math' (s.storage 0) (s.storage 1) (s.storage 2)
    (s.storage 3) (s.storage 4) (s.storage 5) hMaxLS hRR_pos hRR_lt hTS hTPE
    hNoOverflow1 hNoOverflow2 hNoOverflow3 hNoOverflow4 hNoOverflow5

end Benchmark.Cases.Lido.VaulthubLocked
