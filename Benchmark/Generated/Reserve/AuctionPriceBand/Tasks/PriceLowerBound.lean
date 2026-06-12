import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
Band invariant lower bound: `endPrice ≤ p` for any timestamp,
given a well-formed band `endPrice ≤ startPrice`.
-/
theorem price_lower_bound
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256)
    (hBand :
      mulDivUp sellPrices.low D27 buyPrices.high
        ≤ mulDivUp sellPrices.high D27 buyPrices.low) :
    price_lower_bound_spec sellPrices buyPrices auction_startTime auction_endTime block_timestamp := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
