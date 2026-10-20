import Verity.Specs.Common
import Benchmark.Cases.Ascnt.DynamicFeePathAdditivity.Contract

namespace Benchmark.Cases.Ascnt.DynamicFeePathAdditivity

/-- All fee-related bounds enforced by `SimHook.configurePool`. The unrelated
    initialized-pool and authority checks do not alter this pure fee result. -/
def configurePoolAdmissible
    (minMinFee maxMinFee maxFee timeDecayLength jitLockBlocks kPips cPips : Nat) : Prop :=
  minMinFee ≤ maxMinFee ∧
  maxMinFee ≤ maxFee ∧
  maxFee ≤ MAX_LP_FEE ∧
  0 < timeDecayLength ∧ timeDecayLength ≤ MAX_TIME_DECAY_LENGTH ∧
  jitLockBlocks ≤ MAX_JIT_LOCK_BLOCKS ∧
  0 < kPips ∧ kPips ≤ MAX_WEIGHT_PIPS ∧
  0 < cPips ∧ cPips ≤ MAX_WEIGHT_PIPS

/-- Fee amount in the source tests' pips-squared accounting: rate times impact
    length. Common scaling factors do not affect equality or ordering. -/
def feeAmount (impact rate : Nat) : Nat := impact * rate

/-- One-shot fee amount for a path of total impact `p1 + p2`. -/
def oneShotFeeAmount (cum : Int) (zeroForOne : Bool)
    (p1 p2 effectiveMinFee maxFee kPips cPips : Nat) : Nat :=
  feeAmount (p1 + p2)
    (calculateDynamicFee (p1 + p2) cum zeroForOne
      effectiveMinFee maxFee kPips cPips)

/-- Two same-block same-direction legs. The second quote sees exactly the first
    leg's realized accumulator transition, with no inter-leg decay. -/
def splitFeeAmount (cum : Int) (zeroForOne : Bool)
    (p1 p2 effectiveMinFee maxFee kPips cPips : Nat) : Nat :=
  feeAmount p1
      (calculateDynamicFee p1 cum zeroForOne
        effectiveMinFee maxFee kPips cPips) +
    feeAmount p2
      (calculateDynamicFee p2 (advanceCum cum p1 zeroForOne) zeroForOne
        effectiveMinFee maxFee kPips cPips)

/-- The requested normal path: positive same-direction parts, production impact
    bound, no signed saturation, no midpoint cap, and none of the three rates is
    changed by the effective-minimum or maximum clamps. -/
def normalSameBlockUnclampedScope (cum : Int) (zeroForOne : Bool)
    (p1 p2 effectiveMinFee maxFee kPips cPips : Nat) : Prop :=
  0 < p1 ∧ 0 < p2 ∧
  p1 + p2 ≤ PIPS_SCALE ∧
  INT256_MIN_ABS_SAFE ≤ cum ∧ cum ≤ INT256_MAX ∧
  advanceCum cum p1 zeroForOne =
    cum + directionalPriceImpact p1 zeroForOne ∧
  advanceCum (advanceCum cum p1 zeroForOne) p2 zeroForOne =
    advanceCum cum p1 zeroForOne + directionalPriceImpact p2 zeroForOne ∧
  advanceCum cum (p1 + p2) zeroForOne =
    cum + directionalPriceImpact (p1 + p2) zeroForOne ∧
  advanceCum cum (p1 + p2) zeroForOne =
    advanceCum (advanceCum cum p1 zeroForOne) p2 zeroForOne ∧
  cum.natAbs + (advanceCum cum p1 zeroForOne).natAbs ≤ MAX_MIDPOINT_SUM ∧
  (advanceCum cum p1 zeroForOne).natAbs +
      (advanceCum (advanceCum cum p1 zeroForOne) p2 zeroForOne).natAbs ≤
    MAX_MIDPOINT_SUM ∧
  cum.natAbs + (advanceCum cum (p1 + p2) zeroForOne).natAbs ≤ MAX_MIDPOINT_SUM ∧
  effectiveMinFee < dynamicImpactFee p1 cum zeroForOne kPips cPips ∧
  dynamicImpactFee p1 cum zeroForOne kPips cPips < maxFee ∧
  effectiveMinFee < dynamicImpactFee p2 (advanceCum cum p1 zeroForOne)
    zeroForOne kPips cPips ∧
  dynamicImpactFee p2 (advanceCum cum p1 zeroForOne)
    zeroForOne kPips cPips < maxFee ∧
  effectiveMinFee < dynamicImpactFee (p1 + p2) cum zeroForOne kPips cPips ∧
  dynamicImpactFee (p1 + p2) cum zeroForOne kPips cPips < maxFee

/-- Exact path additivity requested by the benchmark scope. -/
def exactPathAdditivitySpec (cum : Int) (zeroForOne : Bool)
    (p1 p2 effectiveMinFee maxFee kPips cPips : Nat) : Prop :=
  splitFeeAmount cum zeroForOne p1 p2 effectiveMinFee maxFee kPips cPips =
    oneShotFeeAmount cum zeroForOne p1 p2 effectiveMinFee maxFee kPips cPips

/-- No-cheaper split property: splitting may not reduce the fee amount. -/
def splitNoCheaperSpec (cum : Int) (zeroForOne : Bool)
    (p1 p2 effectiveMinFee maxFee kPips cPips : Nat) : Prop :=
  oneShotFeeAmount cum zeroForOne p1 p2 effectiveMinFee maxFee kPips cPips ≤
    splitFeeAmount cum zeroForOne p1 p2 effectiveMinFee maxFee kPips cPips

/-- Combined exact-equality/no-cheaper claim, without rounding slack. -/
def dynamicFeePathAdditivitySpec (cum : Int) (zeroForOne : Bool)
    (p1 p2 effectiveMinFee maxFee kPips cPips : Nat) : Prop :=
  exactPathAdditivitySpec cum zeroForOne p1 p2 effectiveMinFee maxFee kPips cPips ∧
  splitNoCheaperSpec cum zeroForOne p1 p2 effectiveMinFee maxFee kPips cPips

end Benchmark.Cases.Ascnt.DynamicFeePathAdditivity
