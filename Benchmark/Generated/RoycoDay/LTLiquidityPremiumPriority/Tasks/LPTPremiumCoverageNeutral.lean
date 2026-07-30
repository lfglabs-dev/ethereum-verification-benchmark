import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _lpt_premium_coverage_neutral
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (cfg : YieldConfig)
    (lptAccruedA lptAccruedB : Nat)
    (_hCfgA : ({ cfg with twLPTYieldShareAccruedWAD := lptAccruedA }).valid)
    (_hCfgB : ({ cfg with twLPTYieldShareAccruedWAD := lptAccruedB }).valid)
    (_hDomainA : sourceSyncDomain last currentCollateralNAV syncCfg
      { cfg with twLPTYieldShareAccruedWAD := lptAccruedA })
    (_hDomainB : sourceSyncDomain last currentCollateralNAV syncCfg
      { cfg with twLPTYieldShareAccruedWAD := lptAccruedB }) :
    LPTPremiumCoverageNeutralSpec last currentCollateralNAV
      syncCfg cfg lptAccruedA lptAccruedB := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
