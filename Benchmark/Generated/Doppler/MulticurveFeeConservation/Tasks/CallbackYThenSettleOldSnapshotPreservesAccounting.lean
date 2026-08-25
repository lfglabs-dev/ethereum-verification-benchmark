import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem callbackYThenSettleOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp forwardedX forwardedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hForwardedX : forwardedX ≤ s.carry.toX.x)
    (hForwardedY : forwardedY ≤ s.carry.toY.y) :
    rehypeFeeAccountingInvariant
      (_settleMarketForwards
        (_onSwapFeeReceivedY s fee stay convert lp) forwardedX forwardedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
