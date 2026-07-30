import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

theorem _combined_premium_bound
    (stGain : Nat)
    (cfg : YieldConfig)
    (hCfg : cfg.valid)
    (_hUint256 : stGain ≤ UINT256_MAX ∧ cfg.uintBounded) :
    CombinedPremiumBoundSpec stGain cfg := by
  exact ?_

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
