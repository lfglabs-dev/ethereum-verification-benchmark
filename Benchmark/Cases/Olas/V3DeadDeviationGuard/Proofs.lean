import Benchmark.Cases.Olas.V3DeadDeviationGuard.Specs

namespace Benchmark.Cases.Olas.V3DeadDeviationGuard

theorem normal_path_deviation_is_zero (spotSqrt twapSqrt : Nat) :
    normal_path_zero_deviation_spec spotSqrt twapSqrt := by
  simp [normal_path_zero_deviation_spec, sourceNormalPath, priceDeviation]

theorem normal_path_returns_twap_center (spotSqrt twapSqrt : Nat) :
    normal_path_returns_twap_center_spec spotSqrt twapSqrt := by
  rfl

theorem normal_path_ignores_spot (spotA spotB twapSqrt : Nat) :
    normal_path_ignores_spot_spec spotA spotB twapSqrt := by
  rfl

theorem dead_deviation_guard_accepts
    (spotSqrt twapSqrt maxAllowedDeviation : Nat) :
    dead_guard_accepts_spec spotSqrt twapSqrt maxAllowedDeviation := by
  simp [dead_guard_accepts_spec, sourceNormalPath, priceDeviation]

end Benchmark.Cases.Olas.V3DeadDeviationGuard
