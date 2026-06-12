import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256

/--
At `block_timestamp = auction_endTime` and `auction_startTime ≠ auction_endTime`,
`_price` returns `endPrice`.
-/
theorem price_at_end_time
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256)
    (hStartNeEnd : auction_startTime ≠ auction_endTime) :
    price_at_end_time_spec sellPrices buyPrices auction_startTime auction_endTime := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
