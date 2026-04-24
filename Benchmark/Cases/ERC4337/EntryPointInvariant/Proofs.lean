import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/-!
# ERC-4337 EntryPoint Invariant Proofs

These proofs establish the selected ERC-4337 EntryPoint control-flow property:

> EntryPoint reaches the operation execution path if and only if validation for
> that same operation has passed.

The proofs work on the abstract pure-Lean model of the two-loop `handleOps`
structure. Because the model uses universally quantified validation results
(a `List Bool`), these proofs hold for all possible validation outcomes in this
model. The proof does not model full arbitrary EVM account/paymaster behavior or
the `callData.length > 0` sender-call branch in `innerHandleOp`.

## Proof strategy

The key insight is that `handleOps` has only two outcomes:
1. All validations pass → `some (List.replicate n true)` → all execution paths attempted
2. Some validation fails → `none` → nothing executed

In case 1, `List.replicate n true` at any in-bounds index gives `true`,
and `List.all` being true means every element is `true`.
In case 2, `wasExecuted none i` is always `false` by definition.
-/

/-! ## Helper lemmas -/

/-- When `handleOps` returns `some`, all validations passed. -/
private theorem handleOps_some_means_valid (vr : List ValidationResult)
    (h : (handleOps vr).isSome = true) :
    validationPhaseSucceeds vr = true := by
  unfold handleOps at h
  split at h <;> simp_all

/-- When `handleOps` returns `some`, the execution list is `List.replicate n true`. -/
private theorem handleOps_some_eq (vr : List ValidationResult)
    (h : (handleOps vr).isSome = true) :
    handleOps vr = some (List.replicate vr.length true) := by
  unfold handleOps executionPhase
  have hv := handleOps_some_means_valid vr h
  simp [hv]

/-- `wasExecuted` on a replicate-true list at an in-bounds index is `true`. -/
private theorem wasExecuted_replicate_true (n i : Nat) (hi : i < n) :
    wasExecuted (some (List.replicate n true)) i = true := by
  simp [wasExecuted, hi]

/-- When `List.all (· == true)` is true and index is in bounds, the element is true. -/
private theorem all_true_getElem {l : List Bool} (h : l.all (· == true) = true)
    (i : Nat) (hi : i < l.length) : l[i] = true := by
  have hAll := List.all_eq_true.mp h
  exact beq_iff_eq.mp (hAll _ (List.getElem_mem hi))

/-- `wasValidated` at an in-bounds index in an all-true list returns true. -/
private theorem wasValidated_of_all_valid (vr : List ValidationResult)
    (hAll : validationPhaseSucceeds vr = true) (i : Nat) (hi : i < vr.length) :
    wasValidated vr i = true := by
  unfold wasValidated
  rw [List.getElem?_eq_getElem hi]
  exact all_true_getElem hAll i hi

/-! ## Pure-model theorems -/

/--
**Claim 1 — Safety**: Execution implies validation.

For any list of validation results: if `handleOps` produced execution results
and execution was attempted at index i, then validation passed at index i.

The proof proceeds by cases on the output of `handleOps`:
- If `none` (revert): `wasExecuted none i = false`, so the premise is vacuously false.
- If `some results`: `handleOps` only returns `some` when ALL validations pass,
  so `wasValidated` at any valid index returns `true`.
-/
theorem execution_implies_validation
    (validationResults : List ValidationResult)
    (i : Nat) :
    let executionResults := handleOps validationResults
    execution_implies_validation_spec validationResults executionResults i := by
  unfold execution_implies_validation_spec
  simp only
  intro hExec
  -- Case split on whether handleOps returned some or none
  cases hOps : handleOps validationResults with
  | none => simp [hOps, wasExecuted] at hExec
  | some results =>
    -- handleOps returned some, so all validations passed
    have hSome : (handleOps validationResults).isSome = true := by simp [hOps]
    have hValid := handleOps_some_means_valid validationResults hSome
    -- The execution results are List.replicate n true
    have hEq := handleOps_some_eq validationResults hSome
    rw [hOps] at hEq
    have hRes : results = List.replicate validationResults.length true :=
      Option.some.inj hEq
    -- Since wasExecuted is true, i must be in bounds
    rw [hOps] at hExec
    simp [wasExecuted] at hExec
    split at hExec
    · rename_i val heq
      -- i is in bounds in results, which means in bounds in validationResults
      rw [hRes] at heq
      have hi : i < validationResults.length := by
        rw [List.getElem?_replicate] at heq
        split at heq
        · rename_i hi; exact hi
        · simp at heq
      exact wasValidated_of_all_valid validationResults hValid i hi
    · simp at hExec

/--
**Claim 2 — Liveness**: Validation implies execution (in non-reverting case).

If `handleOps` does not revert (returns `some`), and validation passed at
index i, and i is within the batch size, then execution was attempted at i.

The proof uses the fact that when `handleOps` returns `some`, it returns
`List.replicate n true`, so `wasExecuted` at any in-bounds index is `true`.
-/
theorem validation_implies_execution
    (validationResults : List ValidationResult)
    (i : Nat) :
    let executionResults := handleOps validationResults
    validation_implies_execution_spec validationResults executionResults i := by
  unfold validation_implies_execution_spec
  simp only
  intro hSome _hValid hi
  have hEq := handleOps_some_eq validationResults hSome
  rw [hEq]
  exact wasExecuted_replicate_true validationResults.length i hi

/--
**Combined invariant — Biconditional**: execution attempt at index i ↔ validation
at i in the selected control-flow model.
-/
theorem execution_iff_validation
    (validationResults : List ValidationResult)
    (i : Nat) :
    let executionResults := handleOps validationResults
    execution_iff_validation_spec validationResults executionResults i := by
  unfold execution_iff_validation_spec
  simp only
  intro hSome hi
  constructor
  · intro hExec
    exact execution_implies_validation validationResults i hExec
  · intro hValid
    exact (validation_implies_execution validationResults i) hSome hValid hi

/--
**All-validations-pass**: If handleOps succeeds, every UserOp was validated.

This captures the all-or-nothing property of the validation loop.
-/
theorem all_validated_on_success
    (validationResults : List ValidationResult) :
    let executionResults := handleOps validationResults
    all_validated_on_success_spec validationResults executionResults := by
  unfold all_validated_on_success_spec
  simp only
  intro hSome i hi
  exact wasValidated_of_all_valid validationResults
    (handleOps_some_means_valid validationResults hSome) i hi

/--
**All-executed-on-success**: If handleOps succeeds, every UserOp's execution
was attempted.
-/
theorem all_executed_on_success
    (validationResults : List ValidationResult) :
    let executionResults := handleOps validationResults
    all_executed_on_success_spec validationResults executionResults := by
  unfold all_executed_on_success_spec
  simp only
  intro hSome i hi
  have hEq := handleOps_some_eq validationResults hSome
  rw [hEq]
  exact wasExecuted_replicate_true validationResults.length i hi

/--
**No-execution-on-revert**: If handleOps reverts, no execution was attempted.
-/
theorem no_execution_on_revert
    (validationResults : List ValidationResult)
    (i : Nat) :
    let executionResults := handleOps validationResults
    no_execution_on_revert_spec executionResults i := by
  unfold no_execution_on_revert_spec
  simp only
  intro hNone
  cases hOps : handleOps validationResults with
  | none => rfl
  | some _ => simp [hOps] at hNone

/-! ## Verity contract proofs (on-chain model) -/

/--
**Verity contract proof**: When `processSingleOp` succeeds (validation passes),
`batchExecuted` is set to 1.
-/
theorem single_op_execution_on_validation
    (sender : Address) (s : ContractState) :
    let s' := ((EntryPointModel.processSingleOp true sender).run s).snd
    single_op_execution_on_validation_spec s s' := by
  unfold single_op_execution_on_validation_spec
  simp [EntryPointModel.processSingleOp,
    EntryPointModel.batchExecuted, EntryPointModel.collected,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

/--
**Verity contract proof**: Processing a single op increments collected fees.
-/
theorem single_op_fee_collected
    (sender : Address) (s : ContractState) :
    let s' := ((EntryPointModel.processSingleOp true sender).run s).snd
    single_op_fee_collected_spec s s' := by
  unfold single_op_fee_collected_spec
  simp [EntryPointModel.processSingleOp,
    EntryPointModel.batchExecuted, EntryPointModel.collected,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

end Benchmark.Cases.ERC4337.EntryPointInvariant
