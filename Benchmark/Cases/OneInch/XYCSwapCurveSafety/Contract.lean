import Contracts.Common

namespace Benchmark.Cases.OneInch.XYCSwapCurveSafety

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity slice of 1inch Aqua XYCSwap._quoteExactIn.

  XYCSwap is a constant-product AMM built on the Aqua shared liquidity layer.
  The benchmark isolates the pure arithmetic of _quoteExactIn, which computes
  the output amount for a given input using the fee-adjusted x*y=k formula:

    amountInWithFee = amountIn * (10000 - feeBps) / 10000
    amountOut = (amountInWithFee * balanceOut) / (balanceIn + amountInWithFee)

  This is the exact fee-adjusted constant-product output formula, analogous to
  Uniswap V2's swap math but with configurable fee in basis points.

  Simplifications:
  - AQUA.pull, xycSwapCallback, and _safeCheckAquaPush are elided because the
    output amount is a pure function of the formula inputs. This matches the
    existing Uniswap V2 benchmark, which starts after transfers and callbacks.
  - The Strategy struct is flattened: feeBps is a direct parameter. Other
    fields (maker, token0, token1, salt) are not relevant to the output formula.
  - The zeroForOne direction selector is abstracted: balanceIn and balanceOut
    are taken as direct parameters.
  - _quoteExactOut is not modeled (one invariant only).

  Upstream: 1inch/aqua (commit 81c26e4619ce21556ab02b3284ee2685de21fb18)
  File: examples/apps/XYCSwap.sol
-/

verity_contract XYCSwapCurveSafety where
  storage
    -- Output: computed amount out
    amountOut : Uint256 := slot 0

  function quoteExactIn
      (balanceIn : Uint256, balanceOut : Uint256,
       amountIn : Uint256, feeBps : Uint256) : Uint256 := do
    let amountInWithFee := div (mul amountIn (sub 10000 feeBps)) 10000
    let output := div (mul amountInWithFee balanceOut) (add balanceIn amountInWithFee)

    setStorage amountOut output
    return output

end Benchmark.Cases.OneInch.XYCSwapCurveSafety
