import Benchmark.Cases.Reserve.AuctionPriceBand.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Reserve.AuctionPriceBand

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/--
Band invariant upper bound: `p ≤ startPrice` for any timestamp,
given a well-formed band and the interior-branch overflow / fixed-point
safety bounds bundled in `InteriorSafe`.
-/
theorem price_upper_bound
    (sellPrices buyPrices : PriceRange)
    (auction_startTime auction_endTime block_timestamp : Uint256)
    (hBand :
      mulDivUp sellPrices.low D27 buyPrices.high
        ≤ mulDivUp sellPrices.high D27 buyPrices.low)
    (hSafe : InteriorSafe sellPrices buyPrices auction_startTime auction_endTime block_timestamp) :
    price_upper_bound_spec sellPrices buyPrices auction_startTime auction_endTime block_timestamp := by
  exact ?_

end Benchmark.Cases.Reserve.AuctionPriceBand
