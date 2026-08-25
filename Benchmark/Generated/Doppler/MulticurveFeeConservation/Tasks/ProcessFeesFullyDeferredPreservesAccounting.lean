import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem processFees_fullyDeferred_preserves_accounting
    (s : RehypeAccounting) (hInv : rehypeFeeAccountingInvariant s) :
    rehypeFeeAccountingInvariant (processFeesDeferred s) := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
