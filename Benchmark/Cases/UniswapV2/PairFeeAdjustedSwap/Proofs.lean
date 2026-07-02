import Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Specs
import Verity.Proofs.Stdlib.Automation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 4000000

namespace Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

open Verity
open Verity.EVM.Uint256

private theorem applySwap_slot_write
    (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState)
    (hInput : amount0In != 0 || amount1In != 0)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000) :
    let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    s'.storage 0 = balance0 ∧
    s'.storage 1 = balance1 := by
  repeat' constructor
  all_goals
    simp [PairFeeAdjustedSwap.applySwap, hInput, hFee0, hFee1, hK,
      PairFeeAdjustedSwap.reserve0, PairFeeAdjustedSwap.reserve1,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      getStorage, setStorage]

theorem applySwap_sets_reserve0
    (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState)
    (hInput : amount0In != 0 || amount1In != 0)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000) :
    let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    applySwap_sets_reserve0_spec balance0 s s' := by
  simpa [applySwap_sets_reserve0_spec] using
    (applySwap_slot_write balance0 balance1 amount0In amount1In s hInput hFee0 hFee1 hK).1

theorem applySwap_sets_reserve1
    (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState)
    (hInput : amount0In != 0 || amount1In != 0)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000) :
    let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    applySwap_sets_reserve1_spec balance1 s s' := by
  simpa [applySwap_sets_reserve1_spec] using
    (applySwap_slot_write balance0 balance1 amount0In amount1In s hInput hFee0 hFee1 hK).2

theorem applySwap_sets_reserve_product
    (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState)
    (hInput : amount0In != 0 || amount1In != 0)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000) :
    let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    applySwap_sets_reserve_product_spec balance0 balance1 s s' := by
  rcases applySwap_slot_write balance0 balance1 amount0In amount1In s hInput hFee0 hFee1 hK with
    ⟨hReserve0, hReserve1⟩
  simp [applySwap_sets_reserve_product_spec, hReserve0, hReserve1]

theorem applySwap_enforces_fee_adjusted_invariant
    (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState)
    (hInput : amount0In != 0 || amount1In != 0)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000) :
    let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    applySwap_enforces_fee_adjusted_invariant_spec balance0 balance1 amount0In amount1In s s' := by
  rcases applySwap_slot_write balance0 balance1 amount0In amount1In s hInput hFee0 hFee1 hK with
    ⟨hReserve0, hReserve1⟩
  simp [applySwap_enforces_fee_adjusted_invariant_spec, hReserve0, hReserve1, hK]

/-! ## Nat-level bridges for the harder tasks -/

private theorem mul_val_no_ovf (a b : Uint256) (h : a.val * b.val < modulus) :
    (mul a b).val = a.val * b.val := by
  simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem sub_val_no_uf (a b : Uint256) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val := by
  simp [HSub.hSub, Verity.Core.Uint256.sub, h, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt)

private theorem add_val_no_ovf (a b : Uint256) (h : a.val + b.val < modulus) :
    (add a b).val = a.val + b.val := by
  simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem mul_val_le (a b : Uint256) : (mul a b).val ≤ a.val * b.val := by
  simp only [Verity.Core.Uint256.mul, Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_le _ _

private theorem val_1000 : (1000 : Uint256).val = 1000 := by decide
private theorem val_1000000 : (1000000 : Uint256).val = 1000000 := by decide

/--
Nat-level consequence of the fee-adjusted `K` guard: whenever the guard
`(1000*balance0 - 3*amount0In) * (1000*balance1 - 3*amount1In) >= r0*r1*1e6`
passes and the old reserve product (scaled by `1e6`) does not overflow, the
raw reserve product cannot decrease across the swap.
-/
private theorem k_growth_of_guards
    (balance0 balance1 amount0In amount1In r0 r1 : Uint256)
    (hFee0 : mul balance0 1000 >= mul amount0In 3)
    (hFee1 : mul balance1 1000 >= mul amount1In 3)
    (hK : mul (sub (mul balance0 1000) (mul amount0In 3))
        (sub (mul balance1 1000) (mul amount1In 3))
        >= mul (mul r0 r1) 1000000)
    (hKOldNoOvf : r0.val * r1.val * 1000000 < modulus) :
    r0.val * r1.val ≤ balance0.val * balance1.val := by
  have hOldLt : r0.val * r1.val < modulus := by omega
  have hr0r1 : (mul r0 r1).val = r0.val * r1.val := mul_val_no_ovf r0 r1 hOldLt
  have hRHS : (mul (mul r0 r1) 1000000).val = r0.val * r1.val * 1000000 := by
    have hlt : (mul r0 r1).val * (1000000 : Uint256).val < modulus := by
      rw [hr0r1, val_1000000]; exact hKOldNoOvf
    rw [mul_val_no_ovf _ _ hlt, hr0r1, val_1000000]
  have hKNat : r0.val * r1.val * 1000000
      ≤ (mul (sub (mul balance0 1000) (mul amount0In 3))
          (sub (mul balance1 1000) (mul amount1In 3))).val := by
    have h := hK
    simp only [ge_iff_le, Verity.Core.Uint256.le_def] at h
    rw [hRHS] at h
    exact h
  have hAdj0 : (sub (mul balance0 1000) (mul amount0In 3)).val ≤ balance0.val * 1000 := by
    have hle : (mul amount0In 3).val ≤ (mul balance0 1000).val := by
      simpa only [ge_iff_le, Verity.Core.Uint256.le_def] using hFee0
    calc (sub (mul balance0 1000) (mul amount0In 3)).val
        = (mul balance0 1000).val - (mul amount0In 3).val := sub_val_no_uf _ _ hle
      _ ≤ (mul balance0 1000).val := Nat.sub_le _ _
      _ ≤ balance0.val * (1000 : Uint256).val := mul_val_le _ _
      _ = balance0.val * 1000 := by rw [val_1000]
  have hAdj1 : (sub (mul balance1 1000) (mul amount1In 3)).val ≤ balance1.val * 1000 := by
    have hle : (mul amount1In 3).val ≤ (mul balance1 1000).val := by
      simpa only [ge_iff_le, Verity.Core.Uint256.le_def] using hFee1
    calc (sub (mul balance1 1000) (mul amount1In 3)).val
        = (mul balance1 1000).val - (mul amount1In 3).val := sub_val_no_uf _ _ hle
      _ ≤ (mul balance1 1000).val := Nat.sub_le _ _
      _ ≤ balance1.val * (1000 : Uint256).val := mul_val_le _ _
      _ = balance1.val * 1000 := by rw [val_1000]
  have hChain : r0.val * r1.val * 1000000 ≤ balance0.val * balance1.val * 1000000 := by
    calc r0.val * r1.val * 1000000
        ≤ (mul (sub (mul balance0 1000) (mul amount0In 3))
            (sub (mul balance1 1000) (mul amount1In 3))).val := hKNat
      _ ≤ (sub (mul balance0 1000) (mul amount0In 3)).val
            * (sub (mul balance1 1000) (mul amount1In 3)).val := mul_val_le _ _
      _ ≤ (balance0.val * 1000) * (balance1.val * 1000) := Nat.mul_le_mul hAdj0 hAdj1
      _ = balance0.val * balance1.val * 1000000 := by ring
  exact Nat.le_of_mul_le_mul_right hChain (by norm_num)

theorem applySwap_two_swap_k_monotone
    (balance0₁ balance1₁ amount0In₁ amount1In₁
      balance0₂ balance1₂ amount0In₂ amount1In₂ : Uint256) (s : ContractState)
    (hInput₁ : amount0In₁ != 0 || amount1In₁ != 0)
    (hFee0₁ : mul balance0₁ 1000 >= mul amount0In₁ 3)
    (hFee1₁ : mul balance1₁ 1000 >= mul amount1In₁ 3)
    (hK₁ : mul (sub (mul balance0₁ 1000) (mul amount0In₁ 3))
        (sub (mul balance1₁ 1000) (mul amount1In₁ 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000)
    (hInput₂ : amount0In₂ != 0 || amount1In₂ != 0)
    (hFee0₂ : mul balance0₂ 1000 >= mul amount0In₂ 3)
    (hFee1₂ : mul balance1₂ 1000 >= mul amount1In₂ 3)
    (hK₂ : mul (sub (mul balance0₂ 1000) (mul amount0In₂ 3))
        (sub (mul balance1₂ 1000) (mul amount1In₂ 3))
        >= mul (mul balance0₁ balance1₁) 1000000)
    (hKOldNoOvf : (s.storage 0).val * (s.storage 1).val * 1000000 < modulus)
    (hKMidNoOvf : balance0₁.val * balance1₁.val * 1000000 < modulus)
    (hKNewNoOvf : balance0₂.val * balance1₂.val < modulus) :
    let sMid := ((PairFeeAdjustedSwap.applySwap
        balance0₁ balance1₁ amount0In₁ amount1In₁).run s).snd
    let s' := ((PairFeeAdjustedSwap.applySwap
        balance0₂ balance1₂ amount0In₂ amount1In₂).run sMid).snd
    applySwap_two_swap_k_monotone_spec s s' := by
  obtain ⟨hMid0, hMid1⟩ :=
    applySwap_slot_write balance0₁ balance1₁ amount0In₁ amount1In₁ s hInput₁ hFee0₁ hFee1₁ hK₁
  have hK₂' : mul (sub (mul balance0₂ 1000) (mul amount0In₂ 3))
      (sub (mul balance1₂ 1000) (mul amount1In₂ 3))
      >= mul (mul
        ((((PairFeeAdjustedSwap.applySwap
            balance0₁ balance1₁ amount0In₁ amount1In₁).run s).snd).storage 0)
        ((((PairFeeAdjustedSwap.applySwap
            balance0₁ balance1₁ amount0In₁ amount1In₁).run s).snd).storage 1)) 1000000 := by
    rw [hMid0, hMid1]; exact hK₂
  obtain ⟨hNew0, hNew1⟩ :=
    applySwap_slot_write balance0₂ balance1₂ amount0In₂ amount1In₂
      (((PairFeeAdjustedSwap.applySwap balance0₁ balance1₁ amount0In₁ amount1In₁).run s).snd)
      hInput₂ hFee0₂ hFee1₂ hK₂'
  have hStep₁ : (s.storage 0).val * (s.storage 1).val ≤ balance0₁.val * balance1₁.val :=
    k_growth_of_guards balance0₁ balance1₁ amount0In₁ amount1In₁
      (s.storage 0) (s.storage 1) hFee0₁ hFee1₁ hK₁ hKOldNoOvf
  have hStep₂ : balance0₁.val * balance1₁.val ≤ balance0₂.val * balance1₂.val :=
    k_growth_of_guards balance0₂ balance1₂ amount0In₂ amount1In₂
      balance0₁ balance1₁ hFee0₂ hFee1₂ hK₂ hKMidNoOvf
  have hOldLt : (s.storage 0).val * (s.storage 1).val < modulus := by omega
  simp only [applySwap_two_swap_k_monotone_spec, ge_iff_le, Verity.Core.Uint256.le_def,
    hNew0, hNew1]
  rw [mul_val_no_ovf _ _ hOldLt, mul_val_no_ovf _ _ hKNewNoOvf]
  exact Nat.le_trans hStep₁ hStep₂

private theorem fee0_trivial (b : Uint256) : mul b 1000 >= mul (0 : Uint256) 3 := by
  simp only [ge_iff_le, Verity.Core.Uint256.le_def]
  have h0 : (mul (0 : Uint256) 3).val = 0 := by decide
  omega

/--
Pure Nat core of the sandwich bound. `A` is the victim's post-swap reserve0,
`o` the victim's realized token0 output, `F1` reserve1 after the front-run,
`R0`/`R1` the original reserves, and `i` the victim's token1 input.
-/
private theorem sandwich_nat_bound
    (A o F1 R0 R1 i : Nat)
    (hK : (A + o) * F1 * 1000 ≤ A * (1000 * F1 + 997 * i))
    (hR1 : R1 ≤ F1)
    (hR0 : A + o ≤ R0) :
    o * (1000 * R1 + 997 * i) ≤ 997 * (i * R0) := by
  nlinarith [Nat.mul_le_mul_left o hR1, Nat.mul_le_mul_left (997 * i) hR0]

theorem applySwap_swap_sandwich_output_bound
    (frontBalance0 frontBalance1 frontAmount1In amount0Out amountIn : Uint256)
    (s : ContractState)
    (hInputF : frontAmount1In != 0)
    (hFeeF : mul frontBalance1 1000 >= mul frontAmount1In 3)
    (hKF : mul (sub (mul frontBalance0 1000) (mul 0 3))
        (sub (mul frontBalance1 1000) (mul frontAmount1In 3))
        >= mul (mul (s.storage 0) (s.storage 1)) 1000000)
    (hFront0 : frontBalance0.val ≤ (s.storage 0).val)
    (hFront1 : (s.storage 1).val ≤ frontBalance1.val)
    (hInputV : amountIn != 0)
    (hFeeV : mul (add frontBalance1 amountIn) 1000 >= mul amountIn 3)
    (hKV : mul (sub (mul (sub frontBalance0 amount0Out) 1000) (mul 0 3))
        (sub (mul (add frontBalance1 amountIn) 1000) (mul amountIn 3))
        >= mul (mul frontBalance0 frontBalance1) 1000000)
    (hOutLe : amount0Out.val ≤ frontBalance0.val)
    (hInNoWrap : frontBalance1.val + amountIn.val < modulus)
    (hBal0NoWrap : frontBalance0.val * 1000 < modulus)
    (hBal1NoWrap : (frontBalance1.val + amountIn.val) * 1000 < modulus)
    (hAdjNoWrap : (frontBalance0.val * 1000)
        * ((frontBalance1.val + amountIn.val) * 1000) < modulus)
    (hKMidNoOvf : frontBalance0.val * frontBalance1.val * 1000000 < modulus) :
    let sMid := ((PairFeeAdjustedSwap.applySwap
        frontBalance0 frontBalance1 0 frontAmount1In).run s).snd
    let s' := ((PairFeeAdjustedSwap.applySwap
        (sub frontBalance0 amount0Out) (add frontBalance1 amountIn) 0 amountIn).run sMid).snd
    applySwap_swap_sandwich_output_bound_spec frontBalance0 amountIn s s' := by
  have hInputF' : ((0 : Uint256) != 0 || frontAmount1In != 0) = true := by
    simp only [hInputF, Bool.or_true]
  have hInputV' : ((0 : Uint256) != 0 || amountIn != 0) = true := by
    simp only [hInputV, Bool.or_true]
  obtain ⟨hMid0, hMid1⟩ :=
    applySwap_slot_write frontBalance0 frontBalance1 0 frontAmount1In s
      hInputF' (fee0_trivial frontBalance0) hFeeF hKF
  have hKV' : mul (sub (mul (sub frontBalance0 amount0Out) 1000) (mul 0 3))
      (sub (mul (add frontBalance1 amountIn) 1000) (mul amountIn 3))
      >= mul (mul
        ((((PairFeeAdjustedSwap.applySwap
            frontBalance0 frontBalance1 0 frontAmount1In).run s).snd).storage 0)
        ((((PairFeeAdjustedSwap.applySwap
            frontBalance0 frontBalance1 0 frontAmount1In).run s).snd).storage 1)) 1000000 := by
    rw [hMid0, hMid1]; exact hKV
  obtain ⟨hNew0, _⟩ :=
    applySwap_slot_write (sub frontBalance0 amount0Out) (add frontBalance1 amountIn) 0 amountIn
      (((PairFeeAdjustedSwap.applySwap frontBalance0 frontBalance1 0 frontAmount1In).run s).snd)
      hInputV' (fee0_trivial (sub frontBalance0 amount0Out)) hFeeV hKV'
  -- Nat values of the victim-swap balances
  have hB0V : (sub frontBalance0 amount0Out).val = frontBalance0.val - amount0Out.val :=
    sub_val_no_uf _ _ hOutLe
  have hB1V : (add frontBalance1 amountIn).val = frontBalance1.val + amountIn.val :=
    add_val_no_ovf _ _ hInNoWrap
  have hM0 : (mul (sub frontBalance0 amount0Out) 1000).val
      = (frontBalance0.val - amount0Out.val) * 1000 := by
    have hlt : (sub frontBalance0 amount0Out).val * (1000 : Uint256).val < modulus := by
      rw [hB0V, val_1000]
      exact Nat.lt_of_le_of_lt
        (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_refl _)) hBal0NoWrap
    rw [mul_val_no_ovf _ _ hlt, hB0V, val_1000]
  have hM1 : (mul (add frontBalance1 amountIn) 1000).val
      = (frontBalance1.val + amountIn.val) * 1000 := by
    have hlt : (add frontBalance1 amountIn).val * (1000 : Uint256).val < modulus := by
      rw [hB1V, val_1000]; exact hBal1NoWrap
    rw [mul_val_no_ovf _ _ hlt, hB1V, val_1000]
  have h03 : (mul (0 : Uint256) 3).val = 0 := by decide
  have h3i : (mul amountIn 3).val = amountIn.val * 3 := by
    have h3 : (3 : Uint256).val = 3 := by decide
    have hlt : amountIn.val * (3 : Uint256).val < modulus := by
      rw [h3]
      exact Nat.lt_of_le_of_lt
        (Nat.mul_le_mul (Nat.le_add_left _ _) (by norm_num)) hBal1NoWrap
    rw [mul_val_no_ovf _ _ hlt, h3]
  -- Nat values of the fee-adjusted balances of the victim swap
  have hAdj0V : (sub (mul (sub frontBalance0 amount0Out) 1000) (mul 0 3)).val
      = (frontBalance0.val - amount0Out.val) * 1000 := by
    rw [sub_val_no_uf _ _ (by rw [h03]; exact Nat.zero_le _), hM0, h03]
    omega
  have hAdj1V : (sub (mul (add frontBalance1 amountIn) 1000) (mul amountIn 3)).val
      = (frontBalance1.val + amountIn.val) * 1000 - amountIn.val * 3 := by
    have hle : (mul amountIn 3).val ≤ (mul (add frontBalance1 amountIn) 1000).val := by
      simpa only [ge_iff_le, Verity.Core.Uint256.le_def] using hFeeV
    rw [sub_val_no_uf _ _ hle, hM1, h3i]
  -- de-wrap both sides of the victim K guard
  have hLHS : (mul (sub (mul (sub frontBalance0 amount0Out) 1000) (mul 0 3))
      (sub (mul (add frontBalance1 amountIn) 1000) (mul amountIn 3))).val
      = ((frontBalance0.val - amount0Out.val) * 1000)
        * ((frontBalance1.val + amountIn.val) * 1000 - amountIn.val * 3) := by
    have hlt : (sub (mul (sub frontBalance0 amount0Out) 1000) (mul 0 3)).val
        * (sub (mul (add frontBalance1 amountIn) 1000) (mul amountIn 3)).val < modulus := by
      rw [hAdj0V, hAdj1V]
      exact Nat.lt_of_le_of_lt
        (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.le_refl _))
          (Nat.sub_le _ _))
        hAdjNoWrap
    rw [mul_val_no_ovf _ _ hlt, hAdj0V, hAdj1V]
  have hMidLt : frontBalance0.val * frontBalance1.val < modulus := by omega
  have hF0F1 : (mul frontBalance0 frontBalance1).val
      = frontBalance0.val * frontBalance1.val := mul_val_no_ovf _ _ hMidLt
  have hRHSV : (mul (mul frontBalance0 frontBalance1) 1000000).val
      = frontBalance0.val * frontBalance1.val * 1000000 := by
    have hlt : (mul frontBalance0 frontBalance1).val * (1000000 : Uint256).val < modulus := by
      rw [hF0F1, val_1000000]; exact hKMidNoOvf
    rw [mul_val_no_ovf _ _ hlt, hF0F1, val_1000000]
  have hKNat : frontBalance0.val * frontBalance1.val * 1000000
      ≤ ((frontBalance0.val - amount0Out.val) * 1000)
        * ((frontBalance1.val + amountIn.val) * 1000 - amountIn.val * 3) := by
    have h := hKV
    simp only [ge_iff_le, Verity.Core.Uint256.le_def] at h
    rw [hRHSV, hLHS] at h
    exact h
  -- cancel the common factor 1000 and normalize the adjusted balance1
  have hcancel : frontBalance0.val * frontBalance1.val * 1000
      ≤ (frontBalance0.val - amount0Out.val)
        * (1000 * frontBalance1.val + 997 * amountIn.val) := by
    have hrw : (frontBalance1.val + amountIn.val) * 1000 - amountIn.val * 3
        = 1000 * frontBalance1.val + 997 * amountIn.val := by omega
    rw [hrw] at hKNat
    have hml : 1000 * (frontBalance0.val * frontBalance1.val * 1000)
        ≤ 1000 * ((frontBalance0.val - amount0Out.val)
            * (1000 * frontBalance1.val + 997 * amountIn.val)) := by
      calc 1000 * (frontBalance0.val * frontBalance1.val * 1000)
          = frontBalance0.val * frontBalance1.val * 1000000 := by ring
        _ ≤ ((frontBalance0.val - amount0Out.val) * 1000)
            * (1000 * frontBalance1.val + 997 * amountIn.val) := hKNat
        _ = 1000 * ((frontBalance0.val - amount0Out.val)
            * (1000 * frontBalance1.val + 997 * amountIn.val)) := by ring
    exact Nat.le_of_mul_le_mul_left hml (by norm_num)
  have hbound := sandwich_nat_bound
      (frontBalance0.val - amount0Out.val) amount0Out.val frontBalance1.val
      (s.storage 0).val (s.storage 1).val amountIn.val
      (by
        have hAo : frontBalance0.val - amount0Out.val + amount0Out.val
            = frontBalance0.val := by omega
        rw [hAo]; exact hcancel)
      hFront1
      (by omega)
  simp only [applySwap_swap_sandwich_output_bound_spec, hNew0]
  rw [hB0V]
  have hOo : frontBalance0.val - (frontBalance0.val - amount0Out.val)
      = amount0Out.val := by omega
  rw [hOo]
  exact hbound

end Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap
