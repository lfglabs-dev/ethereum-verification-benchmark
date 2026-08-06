import Benchmark.Cases.Olas.V3DeadDeviationGuard.Contract

namespace Benchmark.Cases.Olas.V3DeadDeviationGuard

/-- On every successful-oracle path, the overwrite makes the deviation exactly zero. -/
def normal_path_zero_deviation_spec (spotSqrt twapSqrt : Nat) : Prop :=
  (sourceNormalPath spotSqrt twapSqrt).deviation = 0

/-- The returned center is the TWAP sqrt value, not the original spot value. -/
def normal_path_returns_twap_center_spec (spotSqrt twapSqrt : Nat) : Prop :=
  (sourceNormalPath spotSqrt twapSqrt).returnedCenterSqrtPriceX96 = twapSqrt

/-- The entire normal-path result is independent of the source spot price. -/
def normal_path_ignores_spot_spec (spotA spotB twapSqrt : Nat) : Prop :=
  sourceNormalPath spotA twapSqrt = sourceNormalPath spotB twapSqrt

/-- Consequently, any nonnegative configured deviation limit accepts this path. -/
def dead_guard_accepts_spec (spotSqrt twapSqrt maxAllowedDeviation : Nat) : Prop :=
  (sourceNormalPath spotSqrt twapSqrt).deviation ≤ maxAllowedDeviation

end Benchmark.Cases.Olas.V3DeadDeviationGuard
