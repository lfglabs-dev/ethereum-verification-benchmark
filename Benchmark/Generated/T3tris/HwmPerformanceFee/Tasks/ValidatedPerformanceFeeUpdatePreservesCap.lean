import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem validated_performance_fee_update_preserves_cap
    (s : FeeState)
    (nextPerformanceFeeWad : Nat) :
    validated_performance_fee_update_preserves_cap_spec s nextPerformanceFeeWad := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
