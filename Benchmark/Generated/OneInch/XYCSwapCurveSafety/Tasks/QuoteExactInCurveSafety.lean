import Benchmark.Cases.OneInch.XYCSwapCurveSafety.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneInch.XYCSwapCurveSafety

open Verity
open Verity.EVM.Uint256

/--
Curve safety: the output of _quoteExactIn satisfies the fee-adjusted
constant-product constraint. The output amount times the denominator is at
most the fee-adjusted input times the output balance.
-/
theorem quoteExactIn_curve_safety
    (balanceIn balanceOut amountIn feeBps : Uint256)
    (hFeeRange : feeBps.val ≤ 10000)
    (hFeeMulNoOvf : amountIn.val * (10000 - feeBps.val) < modulus)
    (hDenomNoOvf : balanceIn.val
      + (amountIn.val * (10000 - feeBps.val) / 10000) < modulus)
    (hProductNoOvf :
      (amountIn.val * (10000 - feeBps.val) / 10000) * balanceOut.val < modulus) :
    quoteExactIn_curve_safety_spec balanceIn balanceOut amountIn feeBps := by
  exact ?_

end Benchmark.Cases.OneInch.XYCSwapCurveSafety
