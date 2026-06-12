import Benchmark.Cases.Usual.DaoCollateral.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

/--
Direct swap computes the oracle USD quote from explicit price and supported
token-unit inputs, then mints exactly that quote and credits exactly the RWA
collateral amount in the modeled treasury ledger.
-/
theorem swap_conservation
    (rwaToken : Address) (amount minAmountOut price tokenUnit : Uint256) (s : ContractState)
    (hAmount : amount != 0)
    (hMin : expectedSwapUsdQuote amount price tokenUnit >= minAmountOut)
    (hArithmetic : successfulSwapArithmetic rwaToken amount price tokenUnit s) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount minAmountOut price tokenUnit).run s).snd
    swap_conservation_spec rwaToken amount price tokenUnit s s' := by
  exact ?_

end Benchmark.Cases.Usual.DaoCollateral
