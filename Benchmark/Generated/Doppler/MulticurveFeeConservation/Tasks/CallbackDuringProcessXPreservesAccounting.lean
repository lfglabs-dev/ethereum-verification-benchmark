import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem callbackDuringProcessX_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.toY.x) :
    rehypeFeeAccountingInvariant
      (convertForwardXToYAndSettle
        (_onSwapFeeReceivedX s fee stay convert lp) spent received) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
