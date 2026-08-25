import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem releaseClosedMarketCredit_preserves_accounting
    (s : RehypeAccounting) (hInv : rehypeFeeAccountingInvariant s) :
    rehypeFeeAccountingInvariant (releaseClosedMarketCredit s) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
