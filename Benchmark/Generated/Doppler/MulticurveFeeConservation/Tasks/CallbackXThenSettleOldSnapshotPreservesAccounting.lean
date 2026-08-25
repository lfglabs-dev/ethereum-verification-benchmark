import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem callbackXThenSettleOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp forwardedX forwardedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hForwardedX : forwardedX ≤ s.carry.toX.x)
    (hForwardedY : forwardedY ≤ s.carry.toY.y) :
    rehypeFeeAccountingInvariant
      (_settleMarketForwards
        (_onSwapFeeReceivedX s fee stay convert lp) forwardedX forwardedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
