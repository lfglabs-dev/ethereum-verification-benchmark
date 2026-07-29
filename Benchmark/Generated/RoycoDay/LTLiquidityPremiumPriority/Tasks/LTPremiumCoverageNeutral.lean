import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _lt_premium_coverage_neutral
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (cfg : YieldConfig)
    (ltAccruedA ltAccruedB : Nat)
    (hCfgA : ({ cfg with twLTYieldShareAccruedWAD := ltAccruedA }).valid)
    (hCfgB : ({ cfg with twLTYieldShareAccruedWAD := ltAccruedB }).valid)
    (hDomainA : sourceSyncDomain
      last current deltaJT deltaST syncCfg
      { cfg with twLTYieldShareAccruedWAD := ltAccruedA })
    (hDomainB : sourceSyncDomain
      last current deltaJT deltaST syncCfg
      { cfg with twLTYieldShareAccruedWAD := ltAccruedB }) :
    LTPremiumCoverageNeutralSpec
      last current deltaJT deltaST syncCfg cfg ltAccruedA ltAccruedB := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
