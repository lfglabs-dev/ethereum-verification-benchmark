import Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap

open Verity
open Verity.EVM.Uint256

/--
Sandwich output bound: after an adversarial front-run swap moves the
reserves from `(s.storage 0, s.storage 1)` to
`(frontBalance0, frontBalance1)`, the token0 output realized by the victim
swap is still bounded by the fee-adjusted no-front-run output bound
computed from the original reserves.
-/
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
  exact ?_

end Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap
