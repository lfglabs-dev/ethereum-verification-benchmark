import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _st_loss_coverage_priority
    (last : AccountingState)
    (loss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hLossBound : loss ≤ last.collateralNAV)
    (_hDomain : sourceSyncDomain last (last.collateralNAV - loss)
      syncCfg yieldCfg) :
    STLossCoveragePrioritySpec last loss syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
