import Benchmark.Cases.Usual.DaoCollateral.Specs

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

/--
If the oracle quote equals the explicit price-times-collateral formula, the
direct swap transition satisfies the value-conservation spec.
-/
theorem swap_value_conservation
    (rwaToken : Address) (amount wadQuoteInUSD minAmountOut price tokenUnit : Uint256)
    (s : ContractState)
    (hAmount : amount != 0)
    (hMin : wadQuoteInUSD >= minAmountOut)
    (hArithmetic : successfulSwapArithmetic rwaToken amount wadQuoteInUSD price tokenUnit s) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount wadQuoteInUSD minAmountOut).run s).snd
    swap_value_conservation_spec rwaToken amount wadQuoteInUSD price tokenUnit s s' := by
  exact ?_

end Benchmark.Cases.Usual.DaoCollateral
