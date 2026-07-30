import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _sync_conserves_nav
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last currentCollateralNAV syncCfg yieldCfg) :
    SyncConservationSpec last currentCollateralNAV
      syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
