import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _recovery_before_yield
    (last : AccountingState)
    (gain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (_hDomain : sourceSyncDomain last (last.collateralNAV + gain)
      syncCfg yieldCfg) :
    RecoveryBeforeYieldSpec last gain syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
