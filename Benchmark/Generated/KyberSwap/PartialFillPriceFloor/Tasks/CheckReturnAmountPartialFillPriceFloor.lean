import Benchmark.Cases.KyberSwap.PartialFillPriceFloor.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.KyberSwap.PartialFillPriceFloor

open Verity
open Verity.EVM.Uint256

/--
KyberSwap helper-level partial-fill price-floor invariant.

For a successful modeled `_checkReturnAmount` execution in the partial-fill
branch, the checked scaled floor holds:

  `returnAmount * amount >= minReturnAmount * spentAmount`.
-/
theorem checkReturnAmount_partial_fill_price_floor
    (spentAmount returnAmount amount minReturnAmount flags : Uint256)
    (s : ContractState)
    (hPartial :
      isPartialFill
        { amount := amount, minReturnAmount := minReturnAmount, flags := flags } = true)
    (hRun :
      (MetaAggregationRouterV2._checkReturnAmount
        spentAmount returnAmount amount minReturnAmount flags).run s =
        ContractResult.success () s) :
    partial_fill_price_floor_spec spentAmount returnAmount
      { amount := amount, minReturnAmount := minReturnAmount, flags := flags } := by
  exact ?_

end Benchmark.Cases.KyberSwap.PartialFillPriceFloor
