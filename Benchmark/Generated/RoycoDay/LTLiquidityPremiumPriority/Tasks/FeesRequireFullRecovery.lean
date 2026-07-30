import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _fees_require_full_recovery
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (_hDomain : sourceSyncDomain
      last currentCollateralNAV syncCfg yieldCfg) :
    FeesRequireFullRecoverySpec last currentCollateralNAV
      syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
