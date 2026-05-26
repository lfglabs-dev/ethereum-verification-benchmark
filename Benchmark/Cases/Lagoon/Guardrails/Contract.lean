import Verity.EVM.Uint256
import Verity.EVM.Int256
import Verity.Core

namespace Benchmark.Cases.Lagoon.Guardrails

open Verity
open Verity.EVM
open Verity.EVM.Uint256

/--
  Focused Verity model of Lagoon `GuardrailsLib.isCompliant`.

  Simplifications:
  - This is a pure function slice. ERC-7201 storage, events, access control, and
    `GuardrailsManager.activated` are omitted because they do not affect the
    arithmetic compliance decision in `GuardrailsLib.isCompliant`.
  - Solidity 0.8 checked arithmetic reverts on overflow, underflow, and division
    by zero. The model exposes successful-execution arithmetic as Nat helpers
    over `Uint256.val`, so benchmark tasks focus on signed guardrail boundaries
    rather than proving EVM wrapping is unreachable.
  - `lowerRate != type(int256).min` is represented by `lowerRateNotMin`. The
    production `updateGuardrails` function enforces this before a policy can be
    stored. Without it, Solidity negation of `int256.min` is not a successful
    execution.
-/

def ONE_YEAR : Nat := 31556952

def SCALE : Nat := 1000000000000000000

def INT256_MIN : Int := Verity.EVM.Int256.minValue

def int256Nat (rate : Verity.Core.Int256) : Nat :=
  Int.toNat (rate : Int)

def int256NegativeMagnitude (rate : Verity.Core.Int256) : Nat :=
  Int.natAbs (rate : Int)

def lowerRateNotMin (lowerRate : Verity.Core.Int256) : Prop :=
  (lowerRate : Int) ≠ INT256_MIN

instance (lowerRate : Verity.Core.Int256) : Decidable (lowerRateNotMin lowerRate) := by
  unfold lowerRateNotMin
  infer_instance

def uint256Nat (value : Uint256) : Nat :=
  Verity.Core.Uint256.val value

def scaleToOneYearNat (timePast : Uint256) : Nat :=
  ONE_YEAR / uint256Nat timePast

def ppsIncreaseVariationNat (currentPps nextPps timePast : Uint256) : Nat :=
  (uint256Nat nextPps - uint256Nat currentPps) * scaleToOneYearNat timePast * SCALE / uint256Nat currentPps

def ppsDecreaseVariationNat (currentPps nextPps timePast : Uint256) : Nat :=
  (uint256Nat currentPps - uint256Nat nextPps) * scaleToOneYearNat timePast * SCALE / uint256Nat currentPps

def increaseVariationArithmeticSafe (currentPps nextPps timePast : Uint256) : Prop :=
  let delta := uint256Nat nextPps - uint256Nat currentPps
  let scaled := delta * scaleToOneYearNat timePast
  scaled < Verity.Core.Uint256.modulus ∧ scaled * SCALE < Verity.Core.Uint256.modulus

instance (currentPps nextPps timePast : Uint256) :
    Decidable (increaseVariationArithmeticSafe currentPps nextPps timePast) := by
  unfold increaseVariationArithmeticSafe
  infer_instance

def decreaseVariationArithmeticSafe (currentPps nextPps timePast : Uint256) : Prop :=
  let delta := uint256Nat currentPps - uint256Nat nextPps
  let scaled := delta * scaleToOneYearNat timePast
  scaled < Verity.Core.Uint256.modulus ∧ scaled * SCALE < Verity.Core.Uint256.modulus

instance (currentPps nextPps timePast : Uint256) :
    Decidable (decreaseVariationArithmeticSafe currentPps nextPps timePast) := by
  unfold decreaseVariationArithmeticSafe
  infer_instance

def positiveBranchCompliant
    (variation upperRate : Nat) (lowerRate : Verity.Core.Int256) : Bool :=
  if (lowerRate : Int) < 0 then
    upperRate >= variation
  else
    upperRate >= variation && variation >= int256Nat lowerRate

def negativeBranchCompliant
    (variation : Nat) (lowerRate : Verity.Core.Int256) : Bool :=
  if 0 <= (lowerRate : Int) then
    false
  else
    variation <= int256NegativeMagnitude lowerRate

def isCompliant
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) : Bool :=
  if uint256Nat nextPps >= uint256Nat currentPps then
    let variation := ppsIncreaseVariationNat currentPps nextPps timePast
    positiveBranchCompliant variation (uint256Nat upperRate) lowerRate
  else
    let variation := ppsDecreaseVariationNat currentPps nextPps timePast
    negativeBranchCompliant variation lowerRate

end Benchmark.Cases.Lagoon.Guardrails
