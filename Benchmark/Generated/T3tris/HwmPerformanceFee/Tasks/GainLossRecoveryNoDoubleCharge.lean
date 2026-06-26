import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem gain_loss_recovery_no_double_charge
    (s0 : FeeState)
    (gainAssets lossAssets recoveryAssets : Nat)
    (gainManagementFee : ManagementFeeModel := noManagementFee)
    (lossManagementFee : ManagementFeeModel := noManagementFee)
    (recoveryManagementFee : ManagementFeeModel := noManagementFee) :
    gain_loss_recovery_no_double_charge_spec
      s0 gainAssets lossAssets recoveryAssets
      gainManagementFee lossManagementFee recoveryManagementFee := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
