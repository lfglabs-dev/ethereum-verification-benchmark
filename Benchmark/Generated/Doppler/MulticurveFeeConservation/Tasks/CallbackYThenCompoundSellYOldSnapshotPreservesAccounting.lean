import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem callbackYThenCompoundSellYOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.lp.y)
    (hProvideY : providedY ≤ s.carry.lp.y - spent)
    (hProvideX : providedX ≤ s.carry.lp.x + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellY
        (_onSwapFeeReceivedY s fee stay convert lp) spent received providedX providedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
