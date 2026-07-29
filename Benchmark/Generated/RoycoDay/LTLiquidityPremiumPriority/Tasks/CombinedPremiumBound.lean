import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _combined_premium_bound
    (stGain coverageIL : Nat)
    (cfg : YieldConfig)
    (hCfg : cfg.valid)
    (hUint256 :
      stGain ≤ UINT256_MAX ∧ coverageIL ≤ UINT256_MAX ∧
      cfg.uint256Bounded) :
    CombinedPremiumBoundSpec stGain coverageIL cfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
