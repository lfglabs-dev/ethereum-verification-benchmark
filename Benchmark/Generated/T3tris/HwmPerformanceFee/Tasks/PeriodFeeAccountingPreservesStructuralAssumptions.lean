import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem period_fee_accounting_preserves_structural_assumptions
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel := noManagementFee) :
    period_fee_accounting_preserves_structural_assumptions_spec s totalAssets managementFee := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
