import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _post_op_conserves_nav
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat)
    (hDomain : successfulPostOpSourceDomain
      before op amounts minCoverageWAD minLiquidityWAD) :
    PostOpConservationSpec
      before op amounts minCoverageWAD minLiquidityWAD := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
