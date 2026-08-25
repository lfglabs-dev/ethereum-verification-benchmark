import Contracts.Common

namespace Benchmark.Cases.Ascnt.DynamicFeePathAdditivity

/-!
Verity model of Ascnt `SimHook.calculateDynamicFee`.

Upstream: ascntlabs/v1-core-audit
Commit: 87ddf6ba464f00548c449681755050343df89322
Files: src/SimHook.sol:447-516; src/lib/HookMath.sol:62-78

Simplifications:
- Solidity's `uint256`, `uint24`, and `uint32` inputs are represented as `Nat`,
  and `int256` as `Int`. `configurePoolAdmissible` and the normal-path scope in
  `Specs.lean` state the source bounds used by the target property. This avoids
  obscuring the fee formula with word coercions while preserving every branch.
- `FullMath.mulDiv` is represented by exact unbounded multiplication followed by
  floor division. All source-admissible inputs to `calculateDynamicFee` stay
  within the overflow arguments documented in `SimHook.sol`; therefore this is
  semantically exact, not a rounding idealization.
- The stateful callback plumbing is reduced to `advanceCum`: same-block means no
  time decay, and the requested normal-path hypothesis says realized impact is
  the quoted impact. This is the exact accumulator transition used between split
  legs. Pool simulation and price-impact derivation are outside this arithmetic
  invariant.

Preserved behavior:
- direction signing and abs-safe saturating signed addition;
- increasing, non-crossing decreasing, and zero-crossing fee branches;
- `MAX_MIDPOINT_SUM`, floor division, effective-minimum clamp, maximum clamp;
- arbitrary one-shot pool weights admitted by `configurePool`.
-/

/-- `HookMath.PIPS_SCALE`. -/
def PIPS_SCALE : Nat := 1000000

/-- `SimHook.MAX_MIDPOINT_SUM`. -/
def MAX_MIDPOINT_SUM : Nat := 4000000000000

/-- `SimHook.MAX_K_PIPS` and `MAX_C_PIPS`. -/
def MAX_WEIGHT_PIPS : Nat := 20 * PIPS_SCALE

/-- `LPFeeLibrary.MAX_LP_FEE`. -/
def MAX_LP_FEE : Nat := PIPS_SCALE

/-- `SimHook.MAX_TIME_DECAY_LENGTH`. -/
def MAX_TIME_DECAY_LENGTH : Nat := 86400

/-- `SimHook.MAX_JIT_LOCK_BLOCKS`. -/
def MAX_JIT_LOCK_BLOCKS : Nat := 50400

def INT256_MAX : Int := (2 : Int) ^ 255 - 1
def INT256_MIN_ABS_SAFE : Int := -((2 : Int) ^ 255) + 1

/-- `SafeCast.toInt256Capped` on a `uint256`. -/
def toInt256Capped (n : Nat) : Int :=
  min (Int.ofNat n) INT256_MAX

/-- `HookMath.addSaturating`, including its abs-safe `int256.min + 1` floor. -/
def addSaturating (a b : Int) : Int :=
  max INT256_MIN_ABS_SAFE (min (a + b) INT256_MAX)

/-- Saturating unsigned addition. The Nat model cannot overflow; the explicit
    cap retains the Solidity helper's result for its full source domain. -/
def addSaturatingUint (a b : Nat) : Nat :=
  min (a + b) ((2 : Nat) ^ 256 - 1)

/-- Signed impact selected by `zeroForOne`. -/
def directionalPriceImpact (estimatedPriceImpact : Nat) (zeroForOne : Bool) : Int :=
  if zeroForOne then -toInt256Capped estimatedPriceImpact
  else toInt256Capped estimatedPriceImpact

/-- Accumulator after one quoted/realized same-direction leg. -/
def advanceCum (cumPriceImpact : Int) (estimatedPriceImpact : Nat)
    (zeroForOne : Bool) : Int :=
  addSaturating cumPriceImpact
    (directionalPriceImpact estimatedPriceImpact zeroForOne)

/-- Source branch predicate at `SimHook.sol:464`. -/
def increasingImbalance (cumPriceImpact : Int) (zeroForOne : Bool) : Bool :=
  decide (cumPriceImpact = 0 ∨ (zeroForOne = decide (cumPriceImpact < 0)))

/-- Source branch predicate at `SimHook.sol:467`. -/
def crossingZero (estimatedPriceImpact : Nat) (cumPriceImpact : Int)
    (zeroForOne : Bool) : Bool :=
  !increasingImbalance cumPriceImpact zeroForOne &&
    decide (estimatedPriceImpact > cumPriceImpact.natAbs)

/-- Unclamped `dynamicImpactFee`, preserving all three source branches. -/
def dynamicImpactFee (estimatedPriceImpact : Nat) (cumPriceImpact : Int)
    (zeroForOne : Bool) (kPips cPips : Nat) : Nat :=
  let estimatedCumPriceImpact :=
    advanceCum cumPriceImpact estimatedPriceImpact zeroForOne
  let absCum := cumPriceImpact.natAbs
  let absEstCum := estimatedCumPriceImpact.natAbs
  let midpointSum := min (addSaturatingUint absCum absEstCum) MAX_MIDPOINT_SUM
  if increasingImbalance cumPriceImpact zeroForOne then
    midpointSum * kPips / (2 * PIPS_SCALE)
  else if !crossingZero estimatedPriceImpact cumPriceImpact zeroForOne then
    midpointSum * cPips / (2 * PIPS_SCALE)
  else
    let twoPScaled := 2 * estimatedPriceImpact * PIPS_SCALE
    addSaturatingUint
      (absCum * absCum * cPips / twoPScaled)
      (absEstCum * absEstCum * kPips / twoPScaled)

/-- `SimHook.calculateDynamicFee`, including both final clamps. -/
def calculateDynamicFee (estimatedPriceImpact : Nat) (cumPriceImpact : Int)
    (zeroForOne : Bool) (effectiveMinFee maxFee kPips cPips : Nat) : Nat :=
  let impactFee := dynamicImpactFee estimatedPriceImpact cumPriceImpact
    zeroForOne kPips cPips
  if impactFee < effectiveMinFee then effectiveMinFee
  else if impactFee > maxFee then maxFee
  else impactFee

end Benchmark.Cases.Ascnt.DynamicFeePathAdditivity
