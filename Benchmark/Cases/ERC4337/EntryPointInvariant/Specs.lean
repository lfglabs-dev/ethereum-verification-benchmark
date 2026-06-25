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

/-- **Refined biconditional**: in a non-reverting batch, the execution path is
    entered at index i iff i is in bounds. (The refined model captures the
    fact that a successful batch executes ALL ops in range, regardless of the
    per-op `hasCallData` / `innerCallReverted` flags.) -/
def executionR_iff_in_bounds_spec (ops : List OpInfo) (i : Nat) : Prop :=
  handleOpsR ops ≠ none →
  (executionAttemptedR ops i = true ↔ i < ops.length)

/-- **Concat-success**: if both halves succeed, the concatenation succeeds. -/
def validation_concat_spec (ops1 ops2 : List OpInfo) : Prop :=
  validationPhaseSucceedsR ops1 = true →
  validationPhaseSucceedsR ops2 = true →
  validationPhaseSucceedsR (ops1 ++ ops2) = true

/-- **Concat-failure propagation (left)**: a failure in the left half taints
    the concatenation. -/
def validation_concat_fail_left_spec (ops1 ops2 : List OpInfo) : Prop :=
  validationPhaseSucceedsR ops1 = false →
  validationPhaseSucceedsR (ops1 ++ ops2) = false

/-- **Concat-failure propagation (right)**: a failure in the right half taints
    the concatenation. -/
def validation_concat_fail_right_spec (ops1 ops2 : List OpInfo) : Prop :=
  validationPhaseSucceedsR ops2 = false →
  validationPhaseSucceedsR (ops1 ++ ops2) = false

/-- **Concat fee additivity**: when both halves succeed, the concatenated fee
    equals the sum of the halves. -/
def fees_concat_additive_spec (ops1 ops2 : List OpInfo) : Prop :=
  validationPhaseSucceedsR ops1 = true →
  validationPhaseSucceedsR ops2 = true →
  feesCollectedR (ops1 ++ ops2) = some (ops1.length + ops2.length)

/-! ## Full-scope specs: nonce, paymaster, gas, beneficiary -/

/-- **Nonce monotonicity**: on a successful batch the final nonce equals
    `startNonce + ops.length`. Captures `account.nonce++` per validated op. -/
def nonce_advances_by_batch_size_spec
    (ops : List FullOpInfo) (startNonce : Nat) : Prop :=
  handleOpsFull ops startNonce ≠ none →
  handleOpsFull ops startNonce = some (startNonce + ops.length)

/-- **Strict nonce monotonicity**: validation strictly increases the account
    nonce — a stale nonce can never replay. -/
def nonce_strictly_increases_spec
    (ops : List FullOpInfo) (startNonce finalNonce : Nat) : Prop :=
  ops ≠ [] →
  handleOpsFull ops startNonce = some finalNonce →
  startNonce < finalNonce

/-- **Account-required**: validation fails if the account rejects any op,
    regardless of paymaster decisions. -/
def account_rejection_reverts_spec
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) : Prop :=
  op.accountApproves = false →
  handleOpsFull (op :: rest) startNonce = none

/-- **Paymaster-required-when-present**: when an op has a paymaster, paymaster
    rejection fails validation even if the account approves. -/
def paymaster_rejection_reverts_when_present_spec
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) : Prop :=
  op.paymaster = some () →
  op.paymasterApproves = false →
  handleOpsFull (op :: rest) startNonce = none

/-- **Paymaster-irrelevant-when-absent**: if no paymaster is attached, paymaster
    approval flag has no effect on validation. -/
def paymaster_irrelevant_when_absent_spec
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) : Prop :=
  op.paymaster = none →
  handleOpsFull (op :: rest) startNonce =
    handleOpsFull ({ op with paymasterApproves := !op.paymasterApproves } :: rest)
      startNonce

/-- **Nonce-mismatch reverts**: a wrong declared nonce always reverts. -/
def nonce_mismatch_reverts_spec
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) : Prop :=
  op.declaredNonce ≠ startNonce →
  handleOpsFull (op :: rest) startNonce = none

/-- **Beneficiary conservation**: the amount sent to the beneficiary equals
    the sum of per-op prefunds when the batch succeeds. -/
def beneficiary_eq_total_prefund_spec
    (ops : List FullOpInfo) (startNonce : Nat) : Prop :=
  handleOpsFull ops startNonce ≠ none →
  beneficiaryReceives ops startNonce = some (totalPrefund ops)

/-- **No beneficiary payout on revert**: a reverted batch transfers nothing. -/
def no_beneficiary_payout_on_revert_spec
    (ops : List FullOpInfo) (startNonce : Nat) : Prop :=
  handleOpsFull ops startNonce = none →
  beneficiaryReceives ops startNonce = none

/-- **Total prefund is additive**: `totalPrefund` distributes over concatenation. -/
def total_prefund_concat_spec (ops1 ops2 : List FullOpInfo) : Prop :=
  totalPrefund (ops1 ++ ops2) = totalPrefund ops1 + totalPrefund ops2

/-- **Full-scope safety**: success implies every op's account approved. -/
def full_success_implies_all_account_approved_spec
    (ops : List FullOpInfo) (startNonce : Nat) : Prop :=
  handleOpsFull ops startNonce ≠ none →
  ∀ op ∈ ops, op.accountApproves = true

end Benchmark.Cases.ERC4337.EntryPointInvariant
