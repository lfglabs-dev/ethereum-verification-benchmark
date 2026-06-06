import Verity.Specs.Common
import Benchmark.Cases.ERC4337.EntryPointInvariant.Contract

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/-!
# ERC-4337 EntryPoint Invariant Specifications

The selected control-flow property of the ERC-4337 EntryPoint:

> EntryPoint reaches the operation execution path if and only if validation for
> that same operation has passed.

This decomposes into two claims:

- **Claim 1 (Safety / "only if")**: If execution was attempted at index i,
  then validation must have passed at index i.

- **Claim 2 (Liveness / "if")**: If validation passed at index i (and the
  transaction didn't revert), then execution was attempted at index i.

- **Combined (Biconditional)**: In a non-reverting handleOps call, for every
  index i: execution was attempted at i ↔ validation passed at i.
-/

/--
**Claim 1 — Safety**: Execution attempt implies validation.

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
**Claim 2 — Liveness**: Validation implies an execution-path attempt in the
non-reverting case.

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
**Combined invariant — Biconditional**: In a non-reverting handleOps control-flow
model, execution attempt at index i ↔ validation at index i.
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

/-! ## Deeper specs over the pure model

These specs sharpen the control-flow claim into properties that
correspond more directly to the EntryPoint Solidity source. -/

/-- **Determinism**: `handleOps` is a pure function of the validation list. -/
def handleOps_deterministic_spec (vr1 vr2 : List ValidationResult) : Prop :=
  vr1 = vr2 → handleOps vr1 = handleOps vr2

/-- **Empty batch**: an empty UserOp batch is a successful no-op. -/
def handleOps_empty_spec : Prop :=
  handleOps [] = some []

/-- **Length invariant**: when the batch succeeds, the execution-attempt list
    has exactly one entry per UserOp. -/
def execution_length_eq_validation_length_spec
    (validationResults : List ValidationResult) : Prop :=
  ∀ results, handleOps validationResults = some results →
    results.length = validationResults.length

/-- **Bounded executions**: any execution attempt records an index strictly less
    than the batch size. -/
def executed_index_in_bounds_spec
    (validationResults : List ValidationResult) (i : Nat) : Prop :=
  wasExecuted (handleOps validationResults) i = true → i < validationResults.length

/-- **Single failure suffices**: if any validation fails the whole batch reverts. -/
def single_failure_reverts_spec
    (validationResults : List ValidationResult) : Prop :=
  (∃ i, i < validationResults.length ∧ wasValidated validationResults i = false) →
  handleOps validationResults = none

/-- **Count conservation**: the number of execution attempts equals the number
    of validated ops on a successful batch. -/
def count_executed_eq_validated_spec
    (validationResults : List ValidationResult) : Prop :=
  ∀ results, handleOps validationResults = some results →
    (results.filter id).length = (validationResults.filter id).length

/-! ## Refined specs (sender call vs. execution attempt, fee conservation) -/

/-- **Sender-call iff (validated ∧ hasCallData)**: the inner sender-call branch
    of `innerHandleOp` is entered exactly when validation passed AND callData is
    non-empty. -/
def sender_call_iff_validated_and_calldata_spec
    (ops : List OpInfo) (i : Nat) : Prop :=
  i < ops.length →
  handleOpsR ops ≠ none →
  (senderCallAttempted ops i = true ↔
    (ops[i]?.map (·.validated) = some true ∧
     ops[i]?.map (·.hasCallData) = some true))

/-- **Inner-revert independence**: an inner sender-call revert does NOT affect
    whether the execution path was entered (the try/catch absorbs the revert). -/
def execution_independent_of_inner_revert_spec
    (ops1 ops2 : List OpInfo) (i : Nat) : Prop :=
  ops1.length = ops2.length →
  (∀ j, j < ops1.length →
    (ops1[j]?.map (·.validated) = ops2[j]?.map (·.validated) ∧
     ops1[j]?.map (·.hasCallData) = ops2[j]?.map (·.hasCallData))) →
  executionAttemptedR ops1 i = executionAttemptedR ops2 i

/-- **Fee conservation**: on a successful batch, the collected fee equals the
    number of UserOps (one unit per executed op). -/
def fees_collected_eq_ops_length_spec (ops : List OpInfo) : Prop :=
  handleOpsR ops ≠ none → feesCollectedR ops = some ops.length

/-- **All-or-nothing fees**: on a failed batch, no fee is collected. -/
def no_fees_on_revert_spec (ops : List OpInfo) : Prop :=
  handleOpsR ops = none → feesCollectedR ops = none

end Benchmark.Cases.ERC4337.EntryPointInvariant
