import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem fee_claim_preserves_unclaimed_le_supply
    (s : FeeState)
    (requestedSharesToClaim : Nat) :
    fee_claim_preserves_unclaimed_le_supply_spec s requestedSharesToClaim := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
