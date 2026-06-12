import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256

/--
At `block_timestamp = auction_startTime`, `_price` returns `startPrice`.
-/
theorem price_at_start_time
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime : Uint256) :
    price_at_start_time_spec sellPrices buyPrices auction_startTime auction_endTime := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
