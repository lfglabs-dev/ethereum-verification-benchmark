import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Contracts

/-!
# ERC-4337 EntryPoint — Control-Flow Invariant Model

This is an abstract model of the ERC-4337 EntryPoint v0.9 `handleOps` function,
capturing the two-loop validation-before-execution control flow that is the heart
of this benchmark case.

## What this models

The real EntryPoint processes a batch of UserOperations in two phases:

1. **Validation loop**: For each UserOp[i], call the account's `validateUserOp`.
   If validation fails, the entire transaction reverts (the UserOp is rejected).
   If validation passes, record the result in `opInfos[i]`.

2. **Execution loop**: For each UserOp[i] that passed validation, enter
   `_executeUserOp(i, ops[i], opInfos[i])`. That path builds the `innerHandleOp`
   call and, when the effective call data is non-empty, `innerHandleOp` calls the
   account. Even if the account call reverts, the operation execution path was
   attempted and fees are accounted.

## The invariant slice

> EntryPoint reaches the execution path for UserOp[i] if and only if validation
> for that same UserOp[i] passed.

This decomposes into:
- **Claim 1 (safety)**: An execution attempt at index i implies validation at
  index i passed.
- **Claim 2 (liveness)**: If validation at index i passed (and the function doesn't
  revert), then the execution path for index i is attempted.

## Abstraction choices

- UserOperations are abstracted to indices (0..N-1) with validation outcomes
  modeled as a function `validateResult : Fin N → Bool`.
- The account and paymaster are modeled as **universally quantified parameters**:
  the proof holds for all possible validation outcomes in this control-flow model.
- The model records `_executeUserOp` attempts, not account-call success. It also
  elides the `callData.length > 0` branch inside `innerHandleOp`, so an
  "execution" event here means "EntryPoint attempted the operation execution
  path", not necessarily that a non-empty `Exec.call(sender, ...)` happened.
- Gas accounting is abstracted away (it does not affect the execution-iff-validation
  control-flow claim).
- The two-loop structure is modeled via two storage arrays tracking which ops
  were validated and which were executed.

## Correspondence to Solidity

```solidity
// EntryPoint.sol lines 78-96
function handleOps(PackedUserOperation[] calldata ops, address payable beneficiary)
    external nonReentrant {
    uint256 opslen = ops.length;
    UserOpInfo[] memory opInfos = new UserOpInfo[](opslen);
    unchecked {
        _iterateValidationPhase(ops, opInfos, address(0), 0);  // ← LOOP 1
        uint256 collected = 0;
        emit BeforeExecution();
        for (uint256 i = 0; i < opslen; i++) {                 // ← LOOP 2
            collected += _executeUserOp(i, ops[i], opInfos[i]);
        }
        _compensate(beneficiary, collected);
    }
}
```

In the real contract, if ANY validation in loop 1 fails, the entire `handleOps`
reverts. So when loop 2 runs, ALL ops in the batch have passed validation.
Loop 2 always runs for every index, calling `_executeUserOp` which calls
`this.innerHandleOp`. This benchmark records that execution-path attempt; it
does not model the full payload, gas accounting, or account call result.
-/

/-!
## Pure model — no Verity contract needed

We model the two-loop structure as pure Lean functions operating on lists.
This keeps the model clean and makes the proof entirely about the control
flow invariant, not about storage encoding.
-/

/-- Result of validating a single UserOp. In the real contract this is the
    return value of `_validatePrepayment` which calls `account.validateUserOp`.
    We abstract it to a Bool: true = validation passed, false = reverted. -/
abbrev ValidationResult := Bool

/-- Result of entering the execution path for a single UserOp. In the real
    contract `_executeUserOp` performs an inner self-call and handles the result;
    even if the inner account call reverts, this benchmark records that the
    operation execution path was attempted. -/
abbrev ExecutionAttempted := Bool

/--
The validation phase (Loop 1 of handleOps).

In the real contract (`_iterateValidationPhase`), each UserOp is validated
sequentially. If ANY validation fails, the entire handleOps reverts.
This means: either ALL validations pass and we proceed, or we revert entirely.

We model this as: given a list of validation results (one per UserOp),
the validation phase succeeds iff ALL results are true.
-/
def validationPhaseSucceeds (results : List ValidationResult) : Bool :=
  results.all (· == true)

/--
The execution phase (Loop 2 of handleOps).

In the real contract, this loop runs for EVERY index from 0 to opslen-1,
calling `_executeUserOp(i, ops[i], opInfos[i])` for each.
The key insight: this loop runs IF AND ONLY IF the validation phase succeeded
(because handleOps is a single transaction — if validation reverts, execution
never happens).

Each individual execution may succeed or revert internally (inside
`innerHandleOp`), but the attempt is always made. We return a list of `true`
for each index where execution was attempted.
-/
def executionPhase (opslen : Nat) : List ExecutionAttempted :=
  List.replicate opslen true

/--
Abstract model of `handleOps`.

Returns `none` if the transaction reverts (validation failure),
or `some executionList` if it succeeds, where `executionList[i] = true`
means UserOp[i]'s execution was attempted.

This captures the selected Solidity control-flow slice:
- If any validation fails → entire transaction reverts → no executions
- If all validations pass → `_executeUserOp` is attempted once per index
-/
def handleOps (validationResults : List ValidationResult)
    : Option (List ExecutionAttempted) :=
  if validationPhaseSucceeds validationResults then
    some (executionPhase validationResults.length)
  else
    none

/--
For a single UserOp at index `i`:
Was validation successful? (Did `validateUserOp` return success for this op?)
-/
def wasValidated (validationResults : List ValidationResult) (i : Nat) : Bool :=
  match validationResults[i]? with
  | some result => result
  | none => false

/--
For a single UserOp at index `i`:
Was execution attempted? (Did EntryPoint enter the execution path for i?)
-/
def wasExecuted (executionResults : Option (List ExecutionAttempted)) (i : Nat) : Bool :=
  match executionResults with
  | some results =>
    match results[i]? with
    | some attempted => attempted
    | none => false
  | none => false

/-!
## Verity contract for on-chain modeling

We also provide a Verity contract that implements the same logic using
storage arrays, native bounded loops, and environment-backed call oracles.
-/

verity_contract EntryPointModel where
  storage
    -- Number of operations in the current batch
    opsCount : Uint256 := slot 0
    -- 1 if the current batch completed execution, 0 otherwise
    batchExecuted : Uint256 := slot 1
    -- Total fees collected
    collected : Uint256 := slot 2
    -- Per-operation deposit tracking (simplified StakeManager)
    deposits : Address → Uint256 := slot 3
    -- Per-operation validation status recorded by the validation loop
    validationStatus : Uint256 → Uint256 := slot 4
    -- Per-operation execution status recorded by the execution loop
    executionStatus : Uint256 → Uint256 := slot 5

  constants
    STATUS_NOT_VALIDATED : Uint256 := 0
    STATUS_VALIDATED : Uint256 := 1
    STATUS_EXECUTED : Uint256 := 2

  -- Batch lifecycle model using the executable ERC-4337 primitives in Verity:
  -- `forEach` runs once per index and binds `i`, `externalCall` reads from the
  -- environment oracle, and `tryCatch` treats account execution failure as a
  -- caught inner revert while still recording that execution was attempted.
  function handleOpsNative (opslen : Uint256) : Unit := do
    setStorage opsCount opslen

    -- Phase 1: validate every operation. A zero oracle word models validation
    -- failure and reverts the whole batch.
    forEach "i" opslen (do
      let validationWord := externalCall "validateUserOp" [i]
      require (validationWord != STATUS_NOT_VALIDATED) "AA validation failed"
      setMappingUint validationStatus i STATUS_VALIDATED)

    -- Phase 2: attempt execution for every validated operation. The inner call
    -- can fail independently; `tryCatch` catches that failure and the attempt is
    -- still recorded.
    forEach "i" opslen (do
      tryCatch (call 0 i 0 0 0 0 0) (do
        pure ())
      setMappingUint executionStatus i STATUS_EXECUTED
      let currentCollected ← getStorage collected
      setStorage collected (add currentCollected 1))

    setStorage batchExecuted 1

  -- Simplified: process a single operation's full lifecycle
  -- This models the case of a single-op batch (N=1) which is the common case
  -- and keeps the proof-only tasks compact.
  function processSingleOp (validationPassed : Bool, _sender : Address) : Unit := do
    -- Phase 1: Validation
    require validationPassed "AA validation failed"
    -- If we reach here, validation passed.

    -- Phase 2: Execution (always attempted after validation passes)
    -- In the real contract, _executeUserOp uses try/catch so even
    -- if innerHandleOp reverts, execution was still "attempted"
    setStorage batchExecuted 1

    -- Fee collection (simplified)
    let currentCollected ← getStorage collected
    setStorage collected (add currentCollected 1)

end Benchmark.Cases.ERC4337.EntryPointInvariant
