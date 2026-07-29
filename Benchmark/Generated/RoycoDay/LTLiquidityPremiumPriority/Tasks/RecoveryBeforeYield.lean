import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _recovery_before_yield
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT : SignedDelta)
    (stGain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig)
    (hDomain : sourceSyncDomain
      last current deltaJT (.gain stGain) syncCfg yieldCfg) :
    RecoveryBeforeYieldSpec
      last current deltaJT stGain syncCfg yieldCfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
