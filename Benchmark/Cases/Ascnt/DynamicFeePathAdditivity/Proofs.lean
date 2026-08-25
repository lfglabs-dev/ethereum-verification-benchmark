import Benchmark.Cases.Ascnt.DynamicFeePathAdditivity.Specs
import Mathlib.Tactic.NormNum

namespace Benchmark.Cases.Ascnt.DynamicFeePathAdditivity

/-!
# Terminal result: concrete counterexample

All values below are accepted by `configurePool`:

- `minMinFee = maxMinFee = effectiveMinFee = 0`
- `maxFee = 100`
- `timeDecayLength = 1`, `jitLockBlocks = 0`
- `kPips = 1000000`, `cPips = 1000000`

Start from `cumPriceImpact = -1` and execute two same-block `zeroForOne`
imbalance-increasing legs of impact 1 each. The combined impact is 2 pips.
Every raw rate lies strictly between the effective minimum and maximum clamps.

Source-equivalent rates and amounts:

- first leg: `floor((1 + 2) * 1000000 / 2000000) = 1`; amount `1 * 1 = 1`
- second leg from cum = -2:
  `floor((2 + 3) * 1000000 / 2000000) = 2`; amount `1 * 2 = 2`
- one shot: `floor((1 + 3) * 1000000 / 2000000) = 2`; amount `2 * 2 = 4`

Thus the split costs 3 while the one-shot costs 4. Exact equality is false and
splitting toxic flow is concretely cheaper by one fee-pip × impact-pip unit. This
does not weaken the source branch conditions or appeal to either clamp.
-/

/-- The concrete values satisfy source configuration bounds and the requested
    normal same-block, same-direction, unclamped scope. -/
theorem counterexample_is_source_admissible :
    configurePoolAdmissible 0 0 100 1 0 1000000 1000000 ∧
    normalSameBlockUnclampedScope (-1) true 1 1 0 100 1000000 1000000 := by
  have hAdvanceOne : advanceCum (-1) 1 true = -2 := by native_decide
  have hAdvanceTotal : advanceCum (-1) 2 true = -3 := by native_decide
  have hAdvanceSecond : advanceCum (-2) 1 true = -3 := by native_decide
  have hRawFirst : dynamicImpactFee 1 (-1) true 1000000 1000000 = 1 := by
    native_decide
  have hRawSecond : dynamicImpactFee 1 (-2) true 1000000 1000000 = 2 := by
    native_decide
  have hRawOneShot : dynamicImpactFee 2 (-1) true 1000000 1000000 = 2 := by
    native_decide
  constructor
  · norm_num [configurePoolAdmissible, MAX_LP_FEE, MAX_TIME_DECAY_LENGTH,
      MAX_JIT_LOCK_BLOCKS, MAX_WEIGHT_PIPS, PIPS_SCALE]
  · norm_num [normalSameBlockUnclampedScope, hAdvanceOne, hAdvanceTotal,
      hAdvanceSecond, hRawFirst, hRawSecond, hRawOneShot, PIPS_SCALE,
      MAX_MIDPOINT_SUM, INT256_MIN_ABS_SAFE, INT256_MAX,
      directionalPriceImpact, toInt256Capped]

/-- Machine-checked source-equivalent rates for the counterexample. -/
theorem counterexample_rates :
    calculateDynamicFee 1 (-1) true 0 100 1000000 1000000 = 1 ∧
    calculateDynamicFee 1 (advanceCum (-1) 1 true) true 0 100 1000000 1000000 = 2 ∧
    calculateDynamicFee 2 (-1) true 0 100 1000000 1000000 = 2 := by
  native_decide

/-- Machine-checked fee amounts: split = 3 and one-shot = 4. -/
theorem counterexample_amounts :
    splitFeeAmount (-1) true 1 1 0 100 1000000 1000000 = 3 ∧
    oneShotFeeAmount (-1) true 1 1 0 100 1000000 1000000 = 4 := by
  native_decide

/-- Terminal COUNTEREXAMPLE to the unweakened exact-equality/no-cheaper claim. -/
theorem dynamicFeePathAdditivity_counterexample :
    ¬ dynamicFeePathAdditivitySpec (-1) true 1 1 0 100 1000000 1000000 := by
  intro h
  have hEq := h.1
  unfold exactPathAdditivitySpec at hEq
  rw [counterexample_amounts.1, counterexample_amounts.2] at hEq
  norm_num at hEq

/-- The economically directional failure: this imbalance-increasing k-branch split is strictly cheaper. -/
theorem split_is_strictly_cheaper_counterexample :
    splitFeeAmount (-1) true 1 1 0 100 1000000 1000000 <
      oneShotFeeAmount (-1) true 1 1 0 100 1000000 1000000 := by
  native_decide

/-- Joint terminal certificate: source configuration, normal unclamped scope,
    strict split advantage, and negation of the requested conjunction. -/
theorem dynamicFeePathAdditivity_counterexample_certificate :
    configurePoolAdmissible 0 0 100 1 0 1000000 1000000 ∧
    normalSameBlockUnclampedScope (-1) true 1 1 0 100 1000000 1000000 ∧
    splitFeeAmount (-1) true 1 1 0 100 1000000 1000000 <
      oneShotFeeAmount (-1) true 1 1 0 100 1000000 1000000 ∧
    ¬ dynamicFeePathAdditivitySpec (-1) true 1 1 0 100 1000000 1000000 := by
  exact ⟨counterexample_is_source_admissible.1,
    counterexample_is_source_admissible.2,
    split_is_strictly_cheaper_counterexample,
    dynamicFeePathAdditivity_counterexample⟩

end Benchmark.Cases.Ascnt.DynamicFeePathAdditivity
