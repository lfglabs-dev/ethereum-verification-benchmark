import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _inner_reinvestment_coverage_neutral
    (before : ReinvestmentState)
    (requestedShares minLTAssetsOut ltAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool)
    (hDomain : successfulReinvestmentDomain
      before requestedShares minLTAssetsOut ltAssetsMinted
      minCoverageWAD venueCallSucceeded) :
    InnerReinvestmentCoverageNeutralSpec
      before requestedShares minLTAssetsOut ltAssetsMinted
      minCoverageWAD venueCallSucceeded := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
