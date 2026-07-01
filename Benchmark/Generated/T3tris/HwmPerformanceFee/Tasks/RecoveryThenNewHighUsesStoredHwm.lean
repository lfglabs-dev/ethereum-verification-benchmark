import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem recovery_then_new_high_uses_stored_hwm
    (s0 : FeeState)
    (gainAssets lossAssets recoveryAssets newHighAssets : Nat)
    (gainManagementFee : ManagementFeeModel := noManagementFee)
    (lossManagementFee : ManagementFeeModel := noManagementFee)
    (recoveryManagementFee : ManagementFeeModel := noManagementFee)
    (newHighManagementFee : ManagementFeeModel := noManagementFee) :
    recovery_then_new_high_uses_stored_hwm_spec
      s0 gainAssets lossAssets recoveryAssets newHighAssets
      gainManagementFee lossManagementFee recoveryManagementFee newHighManagementFee := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
