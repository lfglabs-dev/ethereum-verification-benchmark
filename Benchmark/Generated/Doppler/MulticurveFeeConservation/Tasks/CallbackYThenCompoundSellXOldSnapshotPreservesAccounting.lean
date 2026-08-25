import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem callbackYThenCompoundSellXOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.lp.x)
    (hProvideX : providedX ≤ s.carry.lp.x - spent)
    (hProvideY : providedY ≤ s.carry.lp.y + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellX
        (_onSwapFeeReceivedY s fee stay convert lp) spent received providedX providedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
