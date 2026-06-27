import Benchmark.Cases.T3tris.HwmPerformanceFee.Specs

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

theorem profit_pnl_uses_cached_hwm
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) :
    profit_pnl_uses_cached_hwm_spec gross params managementFee := by
  exact ?_

end Benchmark.Cases.T3tris.HwmPerformanceFee
