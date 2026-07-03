import Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

open Verity
open Verity.EVM.Uint256

/--
Across two sequential fee-adjusted swaps whose guards all pass and whose
reserve products do not overflow, the constant-product invariant is
monotone: the final reserve product is at least the initial one.
-/
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
  exact ?_

end Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap
