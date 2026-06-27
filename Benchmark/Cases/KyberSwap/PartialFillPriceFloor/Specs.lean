import Verity.Specs.Common
import Benchmark.Cases.KyberSwap.PartialFillPriceFloor.Contract

namespace Benchmark.Cases.KyberSwap.PartialFillPriceFloor

open Verity
open Verity.EVM.Uint256

/--
  Helper-level partial-fill price-floor predicate.

  This matches the Solidity `_checkReturnAmount` partial-fill branch:

    `returnAmount * desc.amount >= desc.minReturnAmount * spentAmount`

  The predicate is false if either checked multiplication would overflow, which
  mirrors Solidity 0.8 successful-execution semantics.
-/
def partial_fill_price_floor_spec
    (spentAmount returnAmount : Uint256)
    (desc : SwapDescriptionV2) : Prop :=
  isPartialFill desc = true →
    checkedScaledPriceFloorHolds spentAmount returnAmount desc

end Benchmark.Cases.KyberSwap.PartialFillPriceFloor
