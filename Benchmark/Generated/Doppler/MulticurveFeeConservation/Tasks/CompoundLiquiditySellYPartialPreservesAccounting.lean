import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem compoundLiquiditySellY_partial_preserves_accounting
    (s : RehypeAccounting) (spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.lp.y)
    (hProvideX : providedX ≤ s.carry.lp.x + received)
    (hProvideY : providedY ≤ s.carry.lp.y - spent) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellY s spent received providedX providedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
