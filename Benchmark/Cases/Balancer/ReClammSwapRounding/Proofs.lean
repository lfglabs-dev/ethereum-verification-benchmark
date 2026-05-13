import Benchmark.Cases.Balancer.ReClammSwapRounding.Specs
import Verity.Proofs.Stdlib.Automation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Benchmark.Cases.Balancer.ReClammSwapRounding

open Verity
open Verity.EVM.Uint256

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem uint256_zero_ne_one : (0 : Uint256) ≠ 1 := by decide

private theorem uint256_one_ne_zero : (1 : Uint256) ≠ 0 := by decide

private theorem add_val_no_ovf (x y : Uint256) (h : x.val + y.val < modulus) :
    (add x y).val = x.val + y.val := by
  simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem mul_val_no_ovf (x y : Uint256) (h : x.val * y.val < modulus) :
    (mul x y).val = x.val * y.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem sub_val_no_uf (x y : Uint256) (h : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  simp [HSub.hSub, Verity.Core.Uint256.sub, h, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt)

private theorem div_val (x y : Uint256) (h : y.val ≠ 0) :
    (div x y).val = x.val / y.val := by
  simp [HDiv.hDiv, Verity.Core.Uint256.div, h, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

private theorem ceil_sub_one_div_mul_ge
    (n d : Uint256) (hD : d.val ≠ 0) :
    n.val ≤ (ite (n == 0) 0 (add (div (sub n 1) d) 1)).val * d.val := by
  by_cases hN : n = 0
  · simp [hN]
  · have hNVal : n.val ≠ 0 := by
      intro h
      apply hN
      exact Verity.Core.Uint256.ext (by simpa using h)
    have hNPos : 0 < n.val := Nat.pos_of_ne_zero hNVal
    have hSub : (sub n 1).val = n.val - 1 := by
      apply sub_val_no_uf
      simpa using hNPos
    have hDiv : (div (sub n 1) d).val = (n.val - 1) / d.val := by
      rw [div_val _ _ hD, hSub]
    have hDivLe : (n.val - 1) / d.val ≤ n.val - 1 := Nat.div_le_self _ _
    have hAddLeN : (n.val - 1) / d.val + (1 : Uint256).val ≤ n.val := by
      norm_num
      omega
    have hAddNoOvf : (div (sub n 1) d).val + (1 : Uint256).val < modulus := by
      rw [hDiv]
      exact Nat.lt_of_le_of_lt hAddLeN n.isLt
    have hAdd : (add (div (sub n 1) d) 1).val = (n.val - 1) / d.val + 1 := by
      rw [add_val_no_ovf _ _ hAddNoOvf, hDiv]
      norm_num
    have hDPos : 0 < d.val := Nat.pos_of_ne_zero hD
    have hLt := Nat.lt_div_mul_add (a := n.val - 1) (b := d.val) hDPos
    have hMain : n.val ≤ (n.val - 1) / d.val * d.val + d.val := by omega
    simp [hN, hAdd]
    simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMain

private theorem exact_in_product_non_decreasing
    (x y dx q : Nat)
    (hQ : q * (x + dx) ≤ y * dx) :
    (x + dx) * (y - q) ≥ x * y := by
  have hQMul : (x + dx) * q ≤ y * dx := by
    rw [Nat.mul_comm]
    exact hQ
  have hExpand : (x + dx) * (y - q) = (x + dx) * y - (x + dx) * q := by
    exact Nat.mul_sub_left_distrib (x + dx) y q
  have hLe : x * y + (x + dx) * q ≤ (x + dx) * y := by
    nlinarith
  have hMain : x * y ≤ (x + dx) * y - (x + dx) * q := Nat.le_sub_of_add_le hLe
  rw [hExpand]
  exact hMain

private theorem exact_out_product_non_decreasing
    (x y dy q : Nat)
    (hDyLeY : dy ≤ y)
    (hCeil : q * (y - dy) ≥ x * dy) :
    (x + q) * (y - dy) ≥ x * y := by
  have hExpand : x * y = x * (y - dy) + x * dy := by
    rw [← Nat.mul_add]
    have : y - dy + dy = y := Nat.sub_add_cancel hDyLeY
    rw [this]
  rw [hExpand]
  nlinarith

theorem onSwap_fixed_virtual_balances_product_non_decreasing
    (exactIn : Bool)
    (balanceA balanceB virtualBalanceA virtualBalanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 : Uint256)
    (s : ContractState)
    (hTokenPair : (indexIn = 0 ∧ indexOut = 1) ∨ (indexIn = 1 ∧ indexOut = 0))
    (hNoOverflow :
      onSwap_no_overflow_assumptions exactIn balanceA balanceB
        virtualBalanceA virtualBalanceB indexIn indexOut amountGivenScaled18)
    (hRun :
      (ReClammPool.onSwap exactIn balanceA balanceB virtualBalanceA virtualBalanceB
        indexIn indexOut amountGivenScaled18).run s =
        ContractResult.success amountCalculatedScaled18 s) :
    onSwap_fixed_virtual_balances_product_non_decreasing_spec
      exactIn balanceA balanceB virtualBalanceA virtualBalanceB
      indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 := by
  rcases hNoOverflow with
    ⟨hBalanceAPlusVirtualNoOverflow, hBalanceBPlusVirtualNoOverflow,
      hExactInDenominatorNoOverflow, hExactInNumeratorNoOverflow,
      hExactOutNumeratorNoOverflow⟩
  rcases hTokenPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_cases hExact : exactIn
    · subst exactIn
      simp [balanceOf, virtualBalanceOf] at hExactInDenominatorNoOverflow hExactInNumeratorNoOverflow
      have hQuoteAndReq :
          amountCalculatedScaled18 =
              div (mul (add balanceB virtualBalanceB) amountGivenScaled18)
                (add (add balanceA virtualBalanceA) amountGivenScaled18) ∧
            (div (mul (add balanceB virtualBalanceB) amountGivenScaled18)
                (add (add balanceA virtualBalanceA) amountGivenScaled18)).val ≤ balanceB.val := by
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRun
        simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require, h10] at hRun
        split_ifs at hRun with hDen hReq
        simp at hRun
        exact ⟨hRun.symm, hReq⟩
      rcases hQuoteAndReq with ⟨hQuote, hReq⟩
      have hAddA : (add balanceA virtualBalanceA).val = balanceA.val + virtualBalanceA.val :=
        add_val_no_ovf _ _ hBalanceAPlusVirtualNoOverflow
      have hAddB : (add balanceB virtualBalanceB).val = balanceB.val + virtualBalanceB.val :=
        add_val_no_ovf _ _ hBalanceBPlusVirtualNoOverflow
      have hDenExact :
          (add (add balanceA virtualBalanceA) amountGivenScaled18).val =
            balanceA.val + virtualBalanceA.val + amountGivenScaled18.val := by
        rw [add_val_no_ovf]
        · rw [hAddA]
        · rw [hAddA]
          simpa [Nat.add_assoc] using hExactInDenominatorNoOverflow
      have hDenValNe :
          (add (add balanceA virtualBalanceA) amountGivenScaled18).val ≠ 0 := by
        have hRunCopy := hRun
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRunCopy
        simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require, h10] at hRunCopy
        split_ifs at hRunCopy with hDen hReq
        simp at hRunCopy
        exact fun h => hDen (Verity.Core.Uint256.ext h)
      have hNumExact :
          (mul (add balanceB virtualBalanceB) amountGivenScaled18).val =
            (balanceB.val + virtualBalanceB.val) * amountGivenScaled18.val := by
        rw [mul_val_no_ovf]
        · rw [hAddB]
        · rw [hAddB]
          simpa using hExactInNumeratorNoOverflow
      have hExactInRoundsDown :
          amountCalculatedScaled18.val *
              (balanceA.val + virtualBalanceA.val + amountGivenScaled18.val)
            ≤
          (balanceB.val + virtualBalanceB.val) * amountGivenScaled18.val := by
        rw [hQuote, div_val _ _ hDenValNe, hDenExact, hNumExact]
        exact Nat.div_mul_le_self _ _
      unfold onSwap_fixed_virtual_balances_product_non_decreasing_spec
      unfold postInvariantNat invariantNat postBalanceA postBalanceB totalNat
      simp [balanceOf, virtualBalanceOf, uint256_zero_ne_one, uint256_one_ne_zero]
      have hOutLeReal : amountCalculatedScaled18.val ≤ balanceB.val := by
        rw [hQuote]
        exact hReq
      have hOutLe : amountCalculatedScaled18.val ≤ balanceB.val + virtualBalanceB.val :=
        Nat.le_trans hOutLeReal (Nat.le_add_right _ _)
      have hCore := exact_in_product_non_decreasing
        (balanceA.val + virtualBalanceA.val)
        (balanceB.val + virtualBalanceB.val)
        amountGivenScaled18.val
        amountCalculatedScaled18.val
        (by simpa [Nat.add_assoc] using hExactInRoundsDown)
      have hOutSub :
          balanceB.val - amountCalculatedScaled18.val + virtualBalanceB.val =
            balanceB.val + virtualBalanceB.val - amountCalculatedScaled18.val := by
        omega
      have hInAdd :
          balanceA.val + amountGivenScaled18.val + virtualBalanceA.val =
            balanceA.val + virtualBalanceA.val + amountGivenScaled18.val := by
        omega
      nlinarith [hCore]
    · have hExactFalse : exactIn = false := by
        cases exactIn <;> simp at hExact ⊢
      simp [hExactFalse, balanceOf, virtualBalanceOf] at hExactOutNumeratorNoOverflow
      have hQuoteAndReq :
          amountCalculatedScaled18 =
              mulDivUp (add balanceA virtualBalanceA) amountGivenScaled18
                (sub (add balanceB virtualBalanceB) amountGivenScaled18) ∧
            amountGivenScaled18.val ≤ balanceB.val := by
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRun
        simp [hExactFalse, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
          Verity.require, h10] at hRun
        split_ifs at hRun with hOut hDen <;> simp at hRun
        all_goals
          constructor
          · exact hRun.symm
          · exact hOut
      rcases hQuoteAndReq with ⟨hQuote, hOutReq⟩
      have hAddA : (add balanceA virtualBalanceA).val = balanceA.val + virtualBalanceA.val :=
        add_val_no_ovf _ _ hBalanceAPlusVirtualNoOverflow
      have hAddB : (add balanceB virtualBalanceB).val = balanceB.val + virtualBalanceB.val :=
        add_val_no_ovf _ _ hBalanceBPlusVirtualNoOverflow
      have hOutLeTotal : amountGivenScaled18.val ≤ (add balanceB virtualBalanceB).val := by
        rw [hAddB]
        exact Nat.le_trans hOutReq (Nat.le_add_right _ _)
      have hDenExact :
          (sub (add balanceB virtualBalanceB) amountGivenScaled18).val =
            balanceB.val + virtualBalanceB.val - amountGivenScaled18.val := by
        rw [sub_val_no_uf _ _ hOutLeTotal, hAddB]
      have hDenValNe :
          (sub (add balanceB virtualBalanceB) amountGivenScaled18).val ≠ 0 := by
        have hRunCopy := hRun
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRunCopy
        simp [hExactFalse, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
          Verity.require, h10] at hRunCopy
        split_ifs at hRunCopy with hOut hDen <;> simp at hRunCopy
        all_goals exact fun h => hOut (Verity.Core.Uint256.ext h)
      have hNumExact :
          (mul (add balanceA virtualBalanceA) amountGivenScaled18).val =
            (balanceA.val + virtualBalanceA.val) * amountGivenScaled18.val := by
        rw [mul_val_no_ovf]
        · rw [hAddA]
        · rw [hAddA]
          simpa using hExactOutNumeratorNoOverflow
      have hExactOutRoundsUp :
          amountCalculatedScaled18.val *
              (balanceB.val + virtualBalanceB.val - amountGivenScaled18.val)
            ≥
          (balanceA.val + virtualBalanceA.val) * amountGivenScaled18.val := by
        rw [hQuote, mulDivUp, ← hDenExact, ← hNumExact]
        exact ceil_sub_one_div_mul_ge _ _ hDenValNe
      unfold onSwap_fixed_virtual_balances_product_non_decreasing_spec
      unfold postInvariantNat invariantNat postBalanceA postBalanceB totalNat
      simp [hExact, balanceOf, virtualBalanceOf, uint256_zero_ne_one, uint256_one_ne_zero]
      have hOutLeReal : amountGivenScaled18.val ≤ balanceB.val := by
        exact hOutReq
      have hOutLe : amountGivenScaled18.val ≤ balanceB.val + virtualBalanceB.val :=
        Nat.le_trans hOutLeReal (Nat.le_add_right _ _)
      have hCore := exact_out_product_non_decreasing
        (balanceA.val + virtualBalanceA.val)
        (balanceB.val + virtualBalanceB.val)
        amountGivenScaled18.val
        amountCalculatedScaled18.val
        hOutLe
        (by simpa [Nat.add_assoc] using hExactOutRoundsUp)
      have hOutSub :
          balanceB.val - amountGivenScaled18.val + virtualBalanceB.val =
            balanceB.val + virtualBalanceB.val - amountGivenScaled18.val := by
        omega
      have hInAdd :
          balanceA.val + amountCalculatedScaled18.val + virtualBalanceA.val =
            balanceA.val + virtualBalanceA.val + amountCalculatedScaled18.val := by
        omega
      nlinarith [hCore]
  · by_cases hExact : exactIn
    · subst exactIn
      simp [balanceOf, virtualBalanceOf] at hExactInDenominatorNoOverflow hExactInNumeratorNoOverflow
      have hQuoteAndReq :
          amountCalculatedScaled18 =
              div (mul (add balanceA virtualBalanceA) amountGivenScaled18)
                (add (add balanceB virtualBalanceB) amountGivenScaled18) ∧
            (div (mul (add balanceA virtualBalanceA) amountGivenScaled18)
                (add (add balanceB virtualBalanceB) amountGivenScaled18)).val ≤ balanceA.val := by
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRun
        simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require, h10] at hRun
        split_ifs at hRun with hDen hReq
        simp at hRun
        exact ⟨hRun.symm, hReq⟩
      rcases hQuoteAndReq with ⟨hQuote, hReq⟩
      have hAddA : (add balanceA virtualBalanceA).val = balanceA.val + virtualBalanceA.val :=
        add_val_no_ovf _ _ hBalanceAPlusVirtualNoOverflow
      have hAddB : (add balanceB virtualBalanceB).val = balanceB.val + virtualBalanceB.val :=
        add_val_no_ovf _ _ hBalanceBPlusVirtualNoOverflow
      have hDenExact :
          (add (add balanceB virtualBalanceB) amountGivenScaled18).val =
            balanceB.val + virtualBalanceB.val + amountGivenScaled18.val := by
        rw [add_val_no_ovf]
        · rw [hAddB]
        · rw [hAddB]
          simpa [Nat.add_assoc] using hExactInDenominatorNoOverflow
      have hDenValNe :
          (add (add balanceB virtualBalanceB) amountGivenScaled18).val ≠ 0 := by
        have hRunCopy := hRun
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRunCopy
        simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require, h10] at hRunCopy
        split_ifs at hRunCopy with hDen hReq
        simp at hRunCopy
        exact fun h => hDen (Verity.Core.Uint256.ext h)
      have hNumExact :
          (mul (add balanceA virtualBalanceA) amountGivenScaled18).val =
            (balanceA.val + virtualBalanceA.val) * amountGivenScaled18.val := by
        rw [mul_val_no_ovf]
        · rw [hAddA]
        · rw [hAddA]
          simpa using hExactInNumeratorNoOverflow
      have hExactInRoundsDown :
          amountCalculatedScaled18.val *
              (balanceB.val + virtualBalanceB.val + amountGivenScaled18.val)
            ≤
          (balanceA.val + virtualBalanceA.val) * amountGivenScaled18.val := by
        rw [hQuote, div_val _ _ hDenValNe, hDenExact, hNumExact]
        exact Nat.div_mul_le_self _ _
      unfold onSwap_fixed_virtual_balances_product_non_decreasing_spec
      unfold postInvariantNat invariantNat postBalanceA postBalanceB totalNat
      simp [balanceOf, virtualBalanceOf, uint256_zero_ne_one, uint256_one_ne_zero]
      have hOutLeReal : amountCalculatedScaled18.val ≤ balanceA.val := by
        rw [hQuote]
        exact hReq
      have hOutLe : amountCalculatedScaled18.val ≤ balanceA.val + virtualBalanceA.val :=
        Nat.le_trans hOutLeReal (Nat.le_add_right _ _)
      have hCore := exact_in_product_non_decreasing
        (balanceB.val + virtualBalanceB.val)
        (balanceA.val + virtualBalanceA.val)
        amountGivenScaled18.val
        amountCalculatedScaled18.val
        (by simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hExactInRoundsDown)
      have hOutSub :
          balanceA.val - amountCalculatedScaled18.val + virtualBalanceA.val =
            balanceA.val + virtualBalanceA.val - amountCalculatedScaled18.val := by
        omega
      have hInAdd :
          balanceB.val + amountGivenScaled18.val + virtualBalanceB.val =
            balanceB.val + virtualBalanceB.val + amountGivenScaled18.val := by
        omega
      nlinarith [hCore]
    · have hExactFalse : exactIn = false := by
        cases exactIn <;> simp at hExact ⊢
      simp [hExactFalse, balanceOf, virtualBalanceOf] at hExactOutNumeratorNoOverflow
      have hQuoteAndReq :
          amountCalculatedScaled18 =
              mulDivUp (add balanceB virtualBalanceB) amountGivenScaled18
                (sub (add balanceA virtualBalanceA) amountGivenScaled18) ∧
            amountGivenScaled18.val ≤ balanceA.val := by
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRun
        simp [hExactFalse, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
          Verity.require, h10] at hRun
        split_ifs at hRun with hOut hDen <;> simp at hRun
        all_goals
          constructor
          · exact hRun.symm
          · exact hOut
      rcases hQuoteAndReq with ⟨hQuote, hOutReq⟩
      have hAddA : (add balanceA virtualBalanceA).val = balanceA.val + virtualBalanceA.val :=
        add_val_no_ovf _ _ hBalanceAPlusVirtualNoOverflow
      have hAddB : (add balanceB virtualBalanceB).val = balanceB.val + virtualBalanceB.val :=
        add_val_no_ovf _ _ hBalanceBPlusVirtualNoOverflow
      have hOutLeTotal : amountGivenScaled18.val ≤ (add balanceA virtualBalanceA).val := by
        rw [hAddA]
        exact Nat.le_trans hOutReq (Nat.le_add_right _ _)
      have hDenExact :
          (sub (add balanceA virtualBalanceA) amountGivenScaled18).val =
            balanceA.val + virtualBalanceA.val - amountGivenScaled18.val := by
        rw [sub_val_no_uf _ _ hOutLeTotal, hAddA]
      have hDenValNe :
          (sub (add balanceA virtualBalanceA) amountGivenScaled18).val ≠ 0 := by
        have hRunCopy := hRun
        have h10 : (1 : Uint256) ≠ 0 := by decide
        unfold ReClammPool.onSwap at hRunCopy
        simp [hExactFalse, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
          Verity.require, h10] at hRunCopy
        split_ifs at hRunCopy with hOut hDen <;> simp at hRunCopy
        all_goals exact fun h => hOut (Verity.Core.Uint256.ext h)
      have hNumExact :
          (mul (add balanceB virtualBalanceB) amountGivenScaled18).val =
            (balanceB.val + virtualBalanceB.val) * amountGivenScaled18.val := by
        rw [mul_val_no_ovf]
        · rw [hAddB]
        · rw [hAddB]
          simpa using hExactOutNumeratorNoOverflow
      have hExactOutRoundsUp :
          amountCalculatedScaled18.val *
              (balanceA.val + virtualBalanceA.val - amountGivenScaled18.val)
            ≥
          (balanceB.val + virtualBalanceB.val) * amountGivenScaled18.val := by
        rw [hQuote, mulDivUp, ← hDenExact, ← hNumExact]
        exact ceil_sub_one_div_mul_ge _ _ hDenValNe
      unfold onSwap_fixed_virtual_balances_product_non_decreasing_spec
      unfold postInvariantNat invariantNat postBalanceA postBalanceB totalNat
      simp [hExact, balanceOf, virtualBalanceOf, uint256_zero_ne_one, uint256_one_ne_zero]
      have hOutLeReal : amountGivenScaled18.val ≤ balanceA.val := by
        exact hOutReq
      have hOutLe : amountGivenScaled18.val ≤ balanceA.val + virtualBalanceA.val :=
        Nat.le_trans hOutLeReal (Nat.le_add_right _ _)
      have hCore := exact_out_product_non_decreasing
        (balanceB.val + virtualBalanceB.val)
        (balanceA.val + virtualBalanceA.val)
        amountGivenScaled18.val
        amountCalculatedScaled18.val
        hOutLe
        (by simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hExactOutRoundsUp)
      have hOutSub :
          balanceA.val - amountGivenScaled18.val + virtualBalanceA.val =
            balanceA.val + virtualBalanceA.val - amountGivenScaled18.val := by
        omega
      have hInAdd :
          balanceB.val + amountCalculatedScaled18.val + virtualBalanceB.val =
            balanceB.val + virtualBalanceB.val + amountCalculatedScaled18.val := by
        omega
      nlinarith [hCore]


end Benchmark.Cases.Balancer.ReClammSwapRounding
