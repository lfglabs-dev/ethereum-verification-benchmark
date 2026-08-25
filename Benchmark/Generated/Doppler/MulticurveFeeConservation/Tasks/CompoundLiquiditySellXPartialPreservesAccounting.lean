import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem compoundLiquiditySellX_partial_preserves_accounting
    (s : RehypeAccounting) (spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.lp.x)
    (hProvideX : providedX ≤ s.carry.lp.x - spent)
    (hProvideY : providedY ≤ s.carry.lp.y + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellX s spent received providedX providedY) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
