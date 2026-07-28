import Benchmark.Cases.OneInch.XYCSwapCurveSafety.Contract

namespace Benchmark.Cases.OneInch.XYCSwapCurveSafety

open Verity
open Verity.EVM.Uint256

/-- Fee-adjusted input amount matching Solidity: amountIn * (10000 - feeBps) / 10000 -/
def amountInWithFee (amountIn feeBps : Uint256) : Uint256 :=
  div (mul amountIn (sub 10000 feeBps)) 10000

/-- Denominator matching Solidity: balanceIn + amountInWithFee -/
def curveDenominator (balanceIn amountIn feeBps : Uint256) : Uint256 :=
  add balanceIn (amountInWithFee amountIn feeBps)

/-- Output amount matching Solidity _quoteExactIn -/
def quoteExactInOutput (balanceIn balanceOut amountIn feeBps : Uint256) : Uint256 :=
  let amountInWithFeeVal := amountInWithFee amountIn feeBps
  div (mul amountInWithFeeVal balanceOut) (curveDenominator balanceIn amountIn feeBps)

/--
Curve safety invariant: the output amount computed by `_quoteExactIn` satisfies
the constant-product constraint. The output times the denominator is at most the
fee-adjusted input times the output balance.
-/
def quoteExactIn_curve_safety_spec
    (balanceIn balanceOut amountIn feeBps : Uint256) : Prop :=
  let fee := amountInWithFee amountIn feeBps
  let denom := curveDenominator balanceIn amountIn feeBps
  let output := quoteExactInOutput balanceIn balanceOut amountIn feeBps
  mul output denom <= mul fee balanceOut

end Benchmark.Cases.OneInch.XYCSwapCurveSafety
