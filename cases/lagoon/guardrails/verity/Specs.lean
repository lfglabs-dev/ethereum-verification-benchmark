import Benchmark.Cases.Lagoon.Guardrails.Contract

namespace Benchmark.Cases.Lagoon.Guardrails

open Verity
open Verity.EVM

/--
  Scope predicate for the production Solidity path.
  `isCompliant` is specified for successful Solidity executions: nonzero divisors,
  no checked-arithmetic overflow/underflow, and no negation of `type(int256).min`.
  The Nat helpers below encode the successful arithmetic result; `lowerRateNotMin`
  records the signed-negation side condition enforced by `updateGuardrails`.
-/
def successfulSolidityArithmeticScope
    (currentPps nextPps timePast _upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  lowerRateNotMin lowerRate ∧
  uint256Nat currentPps ≠ 0 ∧
  uint256Nat timePast ≠ 0 ∧
  if uint256Nat nextPps ≥ uint256Nat currentPps then
    increaseVariationArithmeticSafe currentPps nextPps timePast
  else
    decreaseVariationArithmeticSafe currentPps nextPps timePast

instance
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    Decidable (successfulSolidityArithmeticScope currentPps nextPps timePast upperRate lowerRate) := by
  unfold successfulSolidityArithmeticScope
  infer_instance

/-- Signed annualized PPS movement. Positive values are increases. -/
def annualizedPpsVariation
    (currentPps nextPps timePast : Uint256) : Int :=
  if uint256Nat nextPps >= uint256Nat currentPps then
    Int.ofNat (ppsIncreaseVariationNat currentPps nextPps timePast)
  else
    -Int.ofNat (ppsDecreaseVariationNat currentPps nextPps timePast)

/--
  Reader-facing interval predicate:
  the signed annualized PPS movement must lie between signed `lowerRate`
  and unsigned `upperRate`.
-/
def annualizedVariationInsideGuardrails
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  if uint256Nat nextPps ≥ uint256Nat currentPps then
    let variation := ppsIncreaseVariationNat currentPps nextPps timePast
    if (lowerRate : Int) < 0 then
      variation ≤ uint256Nat upperRate
    else
      int256Nat lowerRate ≤ variation ∧ variation ≤ uint256Nat upperRate
  else
    let variation := ppsDecreaseVariationNat currentPps nextPps timePast
    (lowerRate : Int) < 0 ∧ variation ≤ int256NegativeMagnitude lowerRate

def positiveVariationUpperOnlySpec
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  if (lowerRate : Int) < 0 ∧ uint256Nat nextPps ≥ uint256Nat currentPps then
    isCompliant currentPps nextPps timePast upperRate lowerRate = true ↔
      ppsIncreaseVariationNat currentPps nextPps timePast ≤ uint256Nat upperRate
  else
    True

def positiveVariationBoundedSpec
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  if 0 ≤ (lowerRate : Int) ∧ uint256Nat nextPps ≥ uint256Nat currentPps then
    isCompliant currentPps nextPps timePast upperRate lowerRate = true ↔
      int256Nat lowerRate ≤ ppsIncreaseVariationNat currentPps nextPps timePast ∧
      ppsIncreaseVariationNat currentPps nextPps timePast ≤ uint256Nat upperRate
  else
    True

def nonnegativeLowerRejectsDecreaseSpec
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  if 0 ≤ (lowerRate : Int) ∧ uint256Nat nextPps < uint256Nat currentPps then
    isCompliant currentPps nextPps timePast upperRate lowerRate = false
  else
    True

def negativeVariationBoundedSpec
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  if lowerRateNotMin lowerRate ∧ (lowerRate : Int) < 0 ∧ uint256Nat nextPps < uint256Nat currentPps then
    isCompliant currentPps nextPps timePast upperRate lowerRate = true ↔
      ppsDecreaseVariationNat currentPps nextPps timePast ≤ int256NegativeMagnitude lowerRate
  else
    True

def exactComplianceSpec
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Prop :=
  if successfulSolidityArithmeticScope currentPps nextPps timePast upperRate lowerRate then
    isCompliant currentPps nextPps timePast upperRate lowerRate = true ↔
      annualizedVariationInsideGuardrails currentPps nextPps timePast upperRate lowerRate
  else
    True

end Benchmark.Cases.Lagoon.Guardrails
