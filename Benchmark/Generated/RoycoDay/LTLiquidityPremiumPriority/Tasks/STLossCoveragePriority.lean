import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _st_loss_coverage_priority
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT : SignedDelta)
    (stLoss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last current deltaJT (.loss stLoss) syncCfg yieldCfg) :
    STLossCoveragePrioritySpec
      last current deltaJT stLoss syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
