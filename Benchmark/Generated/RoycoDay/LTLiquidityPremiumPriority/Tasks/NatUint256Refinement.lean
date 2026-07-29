import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

/-- Exact Uint256/Int256 encoding and checked-arithmetic refinement for a source sync. -/
theorem _nat_uint256_refinement
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last current deltaJT deltaST syncCfg yieldCfg) :
    NatUint256RefinementSpec
      last current deltaJT deltaST syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
