import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem no_performance_fee_when_pre_pps_le_hwm
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) :
    no_performance_fee_when_pre_pps_le_hwm_spec gross params managementFee := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
