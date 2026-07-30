import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _inner_reinvestment_coverage_neutral
    (before : ReinvestmentState)
    (requestedShares minLPTAssetsOut lptAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool)
    (_hDomain : successfulReinvestmentDomain before requestedShares
      minLPTAssetsOut lptAssetsMinted minCoverageWAD venueCallSucceeded) :
    InnerReinvestmentCoverageNeutralSpec before requestedShares
      minLPTAssetsOut lptAssetsMinted minCoverageWAD venueCallSucceeded := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
