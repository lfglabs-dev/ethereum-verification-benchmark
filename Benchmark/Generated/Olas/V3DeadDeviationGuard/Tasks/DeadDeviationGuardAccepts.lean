import Benchmark.Grindset
import Benchmark.Cases.Olas.V3DeadDeviationGuard.Specs
namespace Benchmark.Cases.Olas.V3DeadDeviationGuard
theorem dead_deviation_guard_accepts (spotSqrt twapSqrt maxAllowedDeviation : Nat) :
    dead_guard_accepts_spec spotSqrt twapSqrt maxAllowedDeviation := by
  exact ?_
end Benchmark.Cases.Olas.V3DeadDeviationGuard
