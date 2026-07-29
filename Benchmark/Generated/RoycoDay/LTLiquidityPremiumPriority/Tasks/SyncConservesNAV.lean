import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _sync_conserves_nav
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last current deltaJT deltaST syncCfg yieldCfg) :
    SyncConservationSpec
      last current deltaJT deltaST syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
