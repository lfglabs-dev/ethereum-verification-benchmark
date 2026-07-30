import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _post_op_conserves_nav
    (before : AccountingState)
    (op : Operation)
    (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat)
    (hDomain : successfulPostOpSourceDomain before op input
      minCoverageWAD minLiquidityWAD) :
    PostOpConservationSpec before op input minCoverageWAD minLiquidityWAD := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
