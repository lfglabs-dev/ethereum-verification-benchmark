import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem settleMarketForwards_preserves_accounting
    (s : RehypeAccounting) (forwardedX forwardedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hx : forwardedX ≤ s.carry.toX.x)
    (hy : forwardedY ≤ s.carry.toY.y) :
    rehypeFeeAccountingInvariant (_settleMarketForwards s forwardedX forwardedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
