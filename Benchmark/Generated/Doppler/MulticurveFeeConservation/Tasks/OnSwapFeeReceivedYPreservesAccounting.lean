import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem onSwapFeeReceivedY_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee) :
    rehypeFeeAccountingInvariant (_onSwapFeeReceivedY s fee stay convert lp) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
