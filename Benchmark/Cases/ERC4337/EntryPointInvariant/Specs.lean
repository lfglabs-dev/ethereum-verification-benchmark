import Verity.Specs.Common
import Benchmark.Cases.ERC4337.EntryPointInvariant.Contract

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/-!
# ERC-4337 EntryPoint Invariant Specifications

The core security property of the ERC-4337 EntryPoint, as stated in the EIP:

> "The EntryPoint only calls the sender with userOp.callData if and only if
>  validateUserOp on that specific sender has passed."

This decomposes into two claims:

- **Claim 1 (Safety / "only if")**: If execution was attempted at index i,
  then validation must have passed at index i.

- **Claim 2 (Liveness / "if")**: If validation passed at index i (and the
  transaction didn't revert), then execution was attempted at index i.

- **Combined (Biconditional)**: In a non-reverting handleOps call, for every
  index i: execution was attempted at i ↔ validation passed at i.
-/

/--
**Claim 1 — Safety**: Execution implies validation.

"The EntryPoint only calls the sender with userOp.callData
 if validateUserOp to that specific sender has passed."

For all indices in the batch: if execution was attempted,
then validation must have succeeded.
-/
def execution_implies_validation_spec
    (validationResults : List ValidationResult)
    (executionResults : Option (List ExecutionAttempted))
    (i : Nat) : Prop :=
  wasExecuted executionResults i = true →
  wasValidated validationResults i = true

/--
**Claim 2 — Liveness**: Validation implies execution (in non-reverting case).

"If the EntryPoint calls validateUserOp and passes, it also must make
 the generic call with calldata equal to userOp.calldata."

If handleOps does not revert (i.e., returns some result), and validation
passed for index i (which it must have, since handleOps only succeeds if
ALL validations pass), then execution was attempted at index i.
-/
def validation_implies_execution_spec
    (validationResults : List ValidationResult)
    (executionResults : Option (List ExecutionAttempted))
    (i : Nat) : Prop :=
  executionResults.isSome →
  wasValidated validationResults i = true →
  i < validationResults.length →
  wasExecuted executionResults i = true

/--
**Combined invariant — Biconditional**: In a non-reverting handleOps,
execution at index i ↔ validation at index i.

This is the full invariant that Certora could not prove.
-/
def execution_iff_validation_spec
    (validationResults : List ValidationResult)
    (executionResults : Option (List ExecutionAttempted))
    (i : Nat) : Prop :=
  executionResults.isSome →
  i < validationResults.length →
  (wasExecuted executionResults i = true ↔ wasValidated validationResults i = true)

/--
**All-validations-pass invariant**: If handleOps succeeds (doesn't revert),
then every UserOp in the batch was validated.

This captures the critical property of the validation loop: it's all-or-nothing.
-/
def all_validated_on_success_spec
    (validationResults : List ValidationResult)
    (executionResults : Option (List ExecutionAttempted)) : Prop :=
  executionResults.isSome →
  ∀ i, i < validationResults.length → wasValidated validationResults i = true

/--
**All-executed-on-success invariant**: If handleOps succeeds, then every
UserOp in the batch had its execution attempted.
-/
def all_executed_on_success_spec
    (validationResults : List ValidationResult)
    (executionResults : Option (List ExecutionAttempted)) : Prop :=
  executionResults.isSome →
  ∀ i, i < validationResults.length → wasExecuted executionResults i = true

/--
**No-execution-on-revert invariant**: If handleOps reverts (returns none),
then no execution was attempted for any index.
-/
def no_execution_on_revert_spec
    (executionResults : Option (List ExecutionAttempted))
    (i : Nat) : Prop :=
  executionResults.isNone → wasExecuted executionResults i = false

/--
**Verity contract spec**: For the on-chain model with a single operation,
if `processSingleOp` succeeds (doesn't revert), then `batchExecuted` is set to 1.
-/
def single_op_execution_on_validation_spec (_s s' : ContractState) : Prop :=
  s'.storage 1 = 1

/--
**Verity contract spec**: The collected fees are incremented by 1 for each
successfully processed operation.
-/
def single_op_fee_collected_spec (s s' : ContractState) : Prop :=
  s'.storage 2 = add (s.storage 2) 1

end Benchmark.Cases.ERC4337.EntryPointInvariant
