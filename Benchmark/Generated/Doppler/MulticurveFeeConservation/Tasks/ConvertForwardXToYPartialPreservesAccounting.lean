import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem convertForwardXToY_partial_preserves_accounting
    (s : RehypeAccounting) (spent received : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.toY.x) :
    rehypeFeeAccountingInvariant (convertForwardXToYAndSettle s spent received) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
