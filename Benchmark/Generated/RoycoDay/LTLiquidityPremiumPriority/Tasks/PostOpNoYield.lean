import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _post_op_no_yield
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat)
    (hDomain : successfulPostOpSourceDomain
      before op amounts minCoverageWAD minLiquidityWAD) :
    PostOpNoYieldSpec
      before op amounts minCoverageWAD minLiquidityWAD := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
