import Benchmark.Cases.Usual.DaoCollateral.Specs

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

/--
Direct swap mints exactly the oracle USD quote and credits exactly the RWA
collateral amount received by the treasury.
-/
theorem swap_conservation
    (rwaToken : Address) (amount wadQuoteInUSD minAmountOut : Uint256) (s : ContractState)
    (hAmount : amount != 0)
    (hAmountMax : amount <= 340282366920938463463374607431768211455)
    (hQuoteNonzero : wadQuoteInUSD != 0)
    (hMin : wadQuoteInUSD >= minAmountOut)
    (hArithmetic :
      addDoesNotWrap (usd0SupplyOf s) wadQuoteInUSD ∧
      addDoesNotWrap (treasuryCollateralOf s rwaToken) amount) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount wadQuoteInUSD minAmountOut).run s).snd
    swap_conservation_spec rwaToken amount wadQuoteInUSD s s' := by
  exact ?_

end Benchmark.Cases.Usual.DaoCollateral
