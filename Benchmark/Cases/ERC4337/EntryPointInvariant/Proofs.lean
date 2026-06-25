import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/-!
# ERC-4337 EntryPoint Invariant Proofs — historical record

> **Status: archival.** The 33 theorems below were the original abstract
> control-flow proof set, before the case grew to include the bytecode-level
> frame conditions, the indexed counting form, and the aggregator path.
>
> The current critical path is in `IndexedCounting.lean` (headline biconditional
> without pairwise distinctness), `Aggregator.lean` (aggregator-path reuse),
> and `Bytecode.lean` (bytecode-level composition). See `CRITICAL_PATH.md` for
> the load-bearing map.
>
> The theorems in this file are now **corollaries of the indexed-counting
> biconditional** specialised to the safety/liveness/all-or-nothing forms.
> They are preserved here because they document the original Yoav-grade
> claim shape and because they are independently informative; downstream
> consumers (the `CRITICAL_PATH.md` headline theorem in particular) do not
> depend on them.

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

/-! ## Deeper theorems over the pure model -/

/-- **Determinism**: `handleOps` is a pure Lean function — trivial reflexive
    consequence, but it certifies the model has no hidden state. -/
theorem handleOps_deterministic (vr1 vr2 : List ValidationResult) :
    handleOps_deterministic_spec vr1 vr2 := by
  unfold handleOps_deterministic_spec
  intro h; rw [h]

/-- **Empty batch**: `handleOps []` succeeds with an empty execution list. -/
theorem handleOps_empty : handleOps_empty_spec := by
  unfold handleOps_empty_spec handleOps validationPhaseSucceeds executionPhase
  simp

/-- **Length invariant**: success returns one execution slot per UserOp. -/
theorem execution_length_eq_validation_length
    (validationResults : List ValidationResult) :
    execution_length_eq_validation_length_spec validationResults := by
  unfold execution_length_eq_validation_length_spec
  intro results hEq
  unfold handleOps executionPhase at hEq
  split at hEq
  · simp at hEq; rw [← hEq]; exact List.length_replicate
  · cases hEq

/-- **Bounded executions**: any recorded execution index is within batch bounds. -/
theorem executed_index_in_bounds
    (validationResults : List ValidationResult) (i : Nat) :
    executed_index_in_bounds_spec validationResults i := by
  unfold executed_index_in_bounds_spec
  intro hExec
  cases hOps : handleOps validationResults with
  | none => simp [hOps, wasExecuted] at hExec
  | some results =>
    have hSome : (handleOps validationResults).isSome = true := by simp [hOps]
    have hEq := handleOps_some_eq validationResults hSome
    rw [hOps] at hEq
    have hRes : results = List.replicate validationResults.length true :=
      Option.some.inj hEq
    rw [hOps] at hExec
    simp [wasExecuted] at hExec
    split at hExec
    · rename_i val heq
      rw [hRes] at heq
      rw [List.getElem?_replicate] at heq
      split at heq
      · assumption
      · simp at heq
    · simp at hExec

/-- **Single failure suffices**: any failed validation reverts the whole batch. -/
theorem single_failure_reverts
    (validationResults : List ValidationResult) :
    single_failure_reverts_spec validationResults := by
  unfold single_failure_reverts_spec
  rintro ⟨i, hi, hValFalse⟩
  unfold handleOps
  have : validationPhaseSucceeds validationResults = false := by
    unfold validationPhaseSucceeds
    rw [List.all_eq_false]
    refine ⟨validationResults[i], ?_, ?_⟩
    · exact List.getElem_mem hi
    · unfold wasValidated at hValFalse
      rw [List.getElem?_eq_getElem hi] at hValFalse
      simp at hValFalse
      simp [hValFalse]
  rw [this]; rfl

/-- **Count conservation**: number of executed ops equals number of validated ops
    on a successful batch. -/
theorem count_executed_eq_validated
    (validationResults : List ValidationResult) :
    count_executed_eq_validated_spec validationResults := by
  unfold count_executed_eq_validated_spec
  intro results hEq
  unfold handleOps executionPhase at hEq
  split at hEq
  · simp at hEq
    rename_i hValid
    rw [← hEq]
    -- Result list is replicate n true; filter id keeps all of it -> length n
    rw [show (List.replicate validationResults.length true).filter id =
            List.replicate validationResults.length true by
          rw [List.filter_eq_self.mpr]; intro x hx
          have := List.eq_of_mem_replicate hx; simp [this]]
    rw [List.length_replicate]
    -- validationResults is all true (validationPhaseSucceeds = true)
    -- so filter id keeps everything -> length = validationResults.length
    have hAll : ∀ x ∈ validationResults, id x = true := by
      intro x hx
      have hAll := List.all_eq_true.mp hValid
      have := hAll x hx
      simpa using this
    rw [List.filter_eq_self.mpr hAll]
  · cases hEq

/-! ## Refined-model theorems (calldata, inner revert, fees) -/

/-- Helper: when `handleOpsR ops ≠ none`, validation succeeded. -/
private theorem handleOpsR_some_means_valid (ops : List OpInfo)
    (h : handleOpsR ops ≠ none) :
    validationPhaseSucceedsR ops = true := by
  by_contra hne
  have hFalse : validationPhaseSucceedsR ops = false := by
    cases hv : validationPhaseSucceedsR ops
    · rfl
    · exact (hne hv).elim
  unfold handleOpsR at h
  rw [hFalse] at h
  simp at h

/-- **Sender-call iff (validated ∧ hasCallData)**: tight characterization of when
    the inner sender-call branch is entered. -/
theorem sender_call_iff_validated_and_calldata
    (ops : List OpInfo) (i : Nat) :
    sender_call_iff_validated_and_calldata_spec ops i := by
  unfold sender_call_iff_validated_and_calldata_spec
  intro hi _hOk
  unfold senderCallAttempted
  rw [List.getElem?_eq_getElem hi]
  simp [Option.map, Bool.and_eq_true]

/-- **Inner-revert independence**: whether execution was attempted does NOT
    depend on whether the inner sender-call reverted. -/
theorem execution_independent_of_inner_revert
    (ops1 ops2 : List OpInfo) (i : Nat) :
    execution_independent_of_inner_revert_spec ops1 ops2 i := by
  unfold execution_independent_of_inner_revert_spec
  intro hLen hAgree
  unfold executionAttemptedR
  have hVal : validationPhaseSucceedsR ops1 = validationPhaseSucceedsR ops2 := by
    unfold validationPhaseSucceedsR
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [List.all_eq_true] at h ⊢
      intro x hx
      obtain ⟨j, hj2, hjEq⟩ := List.getElem_of_mem hx
      have hj1 : j < ops1.length := by rw [hLen]; exact hj2
      have hv1 := h ops1[j] (List.getElem_mem hj1)
      have ⟨hValEq, _⟩ := hAgree j hj1
      rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2] at hValEq
      simp at hValEq
      rw [← hjEq, ← hValEq]; exact hv1
    · intro h
      rw [List.all_eq_true] at h ⊢
      intro x hx
      obtain ⟨j, hj1, hjEq⟩ := List.getElem_of_mem hx
      have hj2 : j < ops2.length := by rw [← hLen]; exact hj1
      have hv2 := h ops2[j] (List.getElem_mem hj2)
      have ⟨hValEq, _⟩ := hAgree j hj1
      rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2] at hValEq
      simp at hValEq
      rw [← hjEq, hValEq]; exact hv2
  rw [hVal, hLen]

/-- **Fee conservation**: on success, fees collected = number of UserOps. -/
theorem fees_collected_eq_ops_length (ops : List OpInfo) :
    fees_collected_eq_ops_length_spec ops := by
  unfold fees_collected_eq_ops_length_spec
  intro h
  have hValid := handleOpsR_some_means_valid ops h
  unfold feesCollectedR handleOpsR
  rw [if_pos hValid]

/-- **No fees on revert**: a failed batch collects no fee. -/
theorem no_fees_on_revert (ops : List OpInfo) :
    no_fees_on_revert_spec ops := by
  unfold no_fees_on_revert_spec feesCollectedR
  intro h
  rw [h]

/-- **Refined biconditional**: in the non-reverting case, execution is attempted
    at index i iff i is in bounds — the sharpest possible characterization. -/
theorem executionR_iff_in_bounds (ops : List OpInfo) (i : Nat) :
    executionR_iff_in_bounds_spec ops i := by
  unfold executionR_iff_in_bounds_spec
  intro hOk
  have hValid := handleOpsR_some_means_valid ops hOk
  unfold executionAttemptedR
  simp [hValid]

/-- **Concat validation success**: validation succeeds on the concatenation iff
    it succeeds on both halves. -/
theorem validation_concat (ops1 ops2 : List OpInfo) :
    validation_concat_spec ops1 ops2 := by
  unfold validation_concat_spec validationPhaseSucceedsR
  intro h1 h2
  rw [List.all_append, h1, h2]; rfl

/-- **Concat failure propagation (left)**. -/
theorem validation_concat_fail_left (ops1 ops2 : List OpInfo) :
    validation_concat_fail_left_spec ops1 ops2 := by
  unfold validation_concat_fail_left_spec validationPhaseSucceedsR
  intro h1
  rw [List.all_append, h1]; rfl

/-- **Concat failure propagation (right)**. -/
theorem validation_concat_fail_right (ops1 ops2 : List OpInfo) :
    validation_concat_fail_right_spec ops1 ops2 := by
  unfold validation_concat_fail_right_spec validationPhaseSucceedsR
  intro h2
  rw [List.all_append, h2, Bool.and_false]

/-- **Fee additivity over batch concatenation**: when both halves succeed,
    fees collected on the concatenation equal the sum of the halves' sizes. -/
theorem fees_concat_additive (ops1 ops2 : List OpInfo) :
    fees_concat_additive_spec ops1 ops2 := by
  unfold fees_concat_additive_spec feesCollectedR handleOpsR
  intro h1 h2
  have hConcat : validationPhaseSucceedsR (ops1 ++ ops2) = true :=
    validation_concat ops1 ops2 h1 h2
  rw [if_pos hConcat]
  simp [List.length_append]

/-! ## Full-scope theorems (nonce, paymaster, gas, beneficiary) -/

/-- Helper: `validateSequence` advances by exactly the list length on success. -/
private theorem validateSequence_length (ops : List FullOpInfo) (n : Nat) :
    ∀ m, validateSequence ops n = some m → m = n + ops.length := by
  induction ops generalizing n with
  | nil =>
    intro m h
    unfold validateSequence at h
    have : n = m := Option.some.inj h
    simp [← this]
  | cons op rest ih =>
    intro m h
    unfold validateSequence at h
    split at h
    · have := ih (n + 1) m h
      simp [List.length_cons]; omega
    · cases h

/-- **Nonce monotonicity (precise)**: a successful batch advances the nonce by
    exactly the batch size. -/
theorem nonce_advances_by_batch_size
    (ops : List FullOpInfo) (startNonce : Nat) :
    handleOpsFull ops startNonce ≠ none →
    handleOpsFull ops startNonce = some (startNonce + ops.length) := by
  intro hne
  cases h : handleOpsFull ops startNonce with
  | none => exact (hne h).elim
  | some m =>
    have := validateSequence_length ops startNonce m h
    rw [this]

/-- **Strict nonce monotonicity**: a non-empty successful batch strictly raises
    the nonce — replay protection at the model level. -/
theorem nonce_strictly_increases
    (ops : List FullOpInfo) (startNonce finalNonce : Nat) :
    nonce_strictly_increases_spec ops startNonce finalNonce := by
  unfold nonce_strictly_increases_spec
  intro hne h
  have := validateSequence_length ops startNonce finalNonce h
  rw [this]
  have hlen : 0 < ops.length := List.length_pos_iff.mpr hne
  omega

/-- **Account-rejection reverts**: the account is required for validation. -/
theorem account_rejection_reverts
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    account_rejection_reverts_spec op rest startNonce := by
  unfold account_rejection_reverts_spec
  intro hAcc
  simp [handleOpsFull, validateSequence, fullOpValidated, hAcc]

/-- **Paymaster-rejection reverts when paymaster is present**. -/
theorem paymaster_rejection_reverts_when_present
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    paymaster_rejection_reverts_when_present_spec op rest startNonce := by
  unfold paymaster_rejection_reverts_when_present_spec
  intro hPM hRej
  simp [handleOpsFull, validateSequence, fullOpValidated, hPM, hRej]

/-- **Paymaster flag is irrelevant when no paymaster is attached**. -/
theorem paymaster_irrelevant_when_absent
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    paymaster_irrelevant_when_absent_spec op rest startNonce := by
  unfold paymaster_irrelevant_when_absent_spec
  intro hPM
  simp [handleOpsFull, validateSequence, fullOpValidated, hPM]

/-- **Nonce-mismatch reverts**: replay-prevention is by construction. -/
theorem nonce_mismatch_reverts
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    nonce_mismatch_reverts_spec op rest startNonce := by
  unfold nonce_mismatch_reverts_spec
  intro hMis
  simp [handleOpsFull, validateSequence, fullOpValidated, hMis]

/-- **Beneficiary conservation**: collected ≡ Σ prefunds on success. -/
theorem beneficiary_eq_total_prefund
    (ops : List FullOpInfo) (startNonce : Nat) :
    beneficiary_eq_total_prefund_spec ops startNonce := by
  unfold beneficiary_eq_total_prefund_spec beneficiaryReceives
  intro hne
  cases h : handleOpsFull ops startNonce with
  | none => exact (hne h).elim
  | some _ => rfl

/-- **No beneficiary payout on revert**. -/
theorem no_beneficiary_payout_on_revert
    (ops : List FullOpInfo) (startNonce : Nat) :
    no_beneficiary_payout_on_revert_spec ops startNonce := by
  unfold no_beneficiary_payout_on_revert_spec beneficiaryReceives
  intro h
  rw [h]

/-- **Total prefund additivity over batch concatenation**. -/
theorem total_prefund_concat (ops1 ops2 : List FullOpInfo) :
    total_prefund_concat_spec ops1 ops2 := by
  unfold total_prefund_concat_spec
  induction ops1 with
  | nil => simp [totalPrefund]
  | cons op rest ih =>
    simp [totalPrefund, ih]; omega

/-- **Full success implies every op's account approved**: account-required is
    a global invariant across the whole batch. -/
theorem full_success_implies_all_account_approved
    (ops : List FullOpInfo) (startNonce : Nat) :
    full_success_implies_all_account_approved_spec ops startNonce := by
  unfold full_success_implies_all_account_approved_spec
  intro hne op hMem
  induction ops generalizing startNonce with
  | nil => cases hMem
  | cons hd tl ih =>
    unfold handleOpsFull validateSequence at hne
    split at hne
    · rename_i hValid
      rcases List.mem_cons.mp hMem with hEq | hTail
      · rw [hEq]
        unfold fullOpValidated at hValid
        simp at hValid
        exact hValid.1.2
      · have hneTl : handleOpsFull tl (startNonce + 1) ≠ none := hne
        exact ih (startNonce + 1) hneTl hTail
    · exact (hne rfl).elim

end Benchmark.Cases.ERC4337.EntryPointInvariant
