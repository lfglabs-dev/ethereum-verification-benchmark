import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _post_op_no_yield
    (before : AccountingState)
    (op : Operation)
    (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat)
    (_hDomain : successfulPostOpSourceDomain before op input
      minCoverageWAD minLiquidityWAD) :
    PostOpNoYieldSpec before op input minCoverageWAD minLiquidityWAD := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
