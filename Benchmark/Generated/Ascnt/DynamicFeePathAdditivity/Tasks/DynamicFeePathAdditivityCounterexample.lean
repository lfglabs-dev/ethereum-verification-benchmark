import Benchmark.Cases.Ascnt.DynamicFeePathAdditivity.Specs

namespace Benchmark.Cases.Ascnt.DynamicFeePathAdditivity

/-!
Find and prove the source-admissible normal-path counterexample certificate. The reference result uses:

- `cum = -1`
- `zeroForOne = true`
- `p1 = p2 = 1`
- `effectiveMinFee = 0`, `maxFee = 100`
- `kPips = cPips = 1_000_000`
- source-valid configuration witnesses `minMinFee = maxMinFee = 0`,
  `timeDecayLength = 1`, and `jitLockBlocks = 0`

The certificate must establish configuration admissibility, the normal same-block
unclamped scope, a strict split advantage, and failure of the requested conjunction.
-/

theorem dynamicFeePathAdditivity_counterexample_certificate :
    configurePoolAdmissible 0 0 100 1 0 1000000 1000000 ∧
    normalSameBlockUnclampedScope (-1) true 1 1 0 100 1000000 1000000 ∧
    splitFeeAmount (-1) true 1 1 0 100 1000000 1000000 <
      oneShotFeeAmount (-1) true 1 1 0 100 1000000 1000000 ∧
    ¬ dynamicFeePathAdditivitySpec (-1) true 1 1 0 100 1000000 1000000 := by
  exact ?_

end Benchmark.Cases.Ascnt.DynamicFeePathAdditivity
