import Benchmark.Cases.ERC4337.EntryPointInvariant.Trace
import Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame
import Benchmark.Cases.ERC4337.EntryPointInvariant.Layout

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
# `Yoav.lean` — critical path to the headline theorem

This file restates the Yoav-grade theorem in its literal counting form
and proves it from a minimal critical-path set of lemmas.

The English statement (Yoav Weis, paraphrased):

> "Execution will happen exactly once, if and only if validation was
> successful for that UserOp."

The formal counting statement decomposes into three corollaries:

  C1. `validation succeeds ∧ op has callData → countExecCalls = 1`
  C2. `validation succeeds ∧ op has no callData → countExecCalls = 0`
  C3. `validation fails → countExecCalls = 0`

Together they say `countExecCalls = (if validated ∧ executable then 1 else 0)`,
which is the Yoav biconditional in counting form. All three are proved
directly from `Trace.lean`'s `executionLoop_count_*` lemmas.
-/

/-- The execution trace produced by `handleOpsMulti`. -/
def handleOpsTrace
    (ops : List PackedUserOperation) (table : Nonce2DTable)
    (approvals : List Bool) : Trace :=
  match handleOpsMulti ops table approvals with
  | some (_, t) => t
  | none        => []

/-- The validation phase succeeded. -/
def batchValidated
    (ops : List PackedUserOperation) (table : Nonce2DTable)
    (approvals : List Bool) : Bool :=
  (validationLoop ops table approvals).isSome

/-- The op at index `i` has non-empty callData. -/
def opExecutable (ops : List PackedUserOperation) (i : Nat) (hi : i < ops.length)
    : Bool :=
  hasCallData ops[i]

/-! ## C1 — validation succeeded ∧ op has callData ⇒ count = 1 -/

/-- **CRITICAL_PATH L9** — bridging lemma: when validation succeeded and
    op `i` has non-empty callData, `countExecCalls = 1` exactly. The
    composition of L6 (upper bound) and L7 (lower bound). -/
theorem yoav_count_eq_one_when_validated_and_executable
    (ops : List PackedUserOperation)
    (hDistinct : List.Pairwise
      (fun a b => ¬ (a.sender = b.sender ∧ a.callData = b.callData)) ops)
    (table : Nonce2DTable) (approvals : List Bool) (i : Nat) (hi : i < ops.length)
    (hVal : batchValidated ops table approvals = true)
    (hExec : opExecutable ops i hi = true) :
    countExecCalls (handleOpsTrace ops table approvals)
      ops[i].sender ops[i].callData = 1 := by
  unfold handleOpsTrace handleOpsMulti
  unfold batchValidated at hVal
  cases hVL : validationLoop ops table approvals with
  | some finalTable =>
    simp only
    have hLower : countExecCalls (executionLoop ops) ops[i].sender ops[i].callData ≥ 1 :=
      executionLoop_count_ge_one ops ops[i] (List.getElem_mem hi) hExec
        ops[i].sender ops[i].callData ⟨rfl, rfl⟩
    have hUpper : countExecCalls (executionLoop ops) ops[i].sender ops[i].callData ≤ 1 :=
      executionLoop_count_le_one ops hDistinct ops[i].sender ops[i].callData
    omega
  | none =>
    rw [hVL] at hVal; simp at hVal

/-! ## C2 — validation succeeded ∧ op has no callData ⇒ count = 0 -/

theorem yoav_count_eq_zero_when_validated_and_not_executable
    (ops : List PackedUserOperation)
    (table : Nonce2DTable) (approvals : List Bool) (i : Nat) (hi : i < ops.length)
    (hExec : opExecutable ops i hi = false) :
    countExecCalls (handleOpsTrace ops table approvals)
      ops[i].sender ops[i].callData = 0 := by
  unfold handleOpsTrace handleOpsMulti
  cases hVL : validationLoop ops table approvals with
  | some finalTable =>
    simp only
    unfold countExecCalls
    have hFilter :
        (executionLoop ops).filter (matchesCallEvent ops[i].sender ops[i].callData) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he hMatch
      obtain ⟨op', _hMem', hHas', _hET, hED⟩ :=
        executionLoop_event_origin ops e he
      unfold matchesCallEvent at hMatch
      simp at hMatch
      have hCD : op'.callData = ops[i].callData := by rw [← hED, hMatch.2]
      unfold hasCallData at hHas'
      rw [hCD] at hHas'
      unfold opExecutable hasCallData at hExec
      rw [hHas'] at hExec
      cases hExec
    rw [hFilter]; simp
  | none =>
    simp [countExecCalls]

/-! ## C3 — validation failed ⇒ count = 0 -/

/-- **CRITICAL_PATH L10** — failure side: when validation fails, no
    execution events are emitted regardless of any other state. -/
theorem yoav_count_eq_zero_when_validation_fails
    (ops : List PackedUserOperation) (table : Nonce2DTable)
    (approvals : List Bool) (s : Address) (c : List Uint256)
    (hFail : batchValidated ops table approvals = false) :
    countExecCalls (handleOpsTrace ops table approvals) s c = 0 := by
  unfold handleOpsTrace handleOpsMulti
  unfold batchValidated at hFail
  cases hVL : validationLoop ops table approvals with
  | some finalTable =>
    rw [hVL] at hFail; simp at hFail
  | none =>
    simp [countExecCalls]

/-! ## The combined Yoav biconditional -/

/-- **The Yoav-grade theorem in counting form**:

    `countExecCalls trace ops[i].sender ops[i].callData = 1`
    iff
    `batchValidated ∧ opExecutable i`.

    Otherwise the count is `0`. This is the literal formal counterpart of
    Yoav's English claim:

    > "Execution will happen exactly once, if and only if validation was
    > successful for that UserOp."
-/
theorem yoav_counting_biconditional
    (ops : List PackedUserOperation)
    (hDistinct : List.Pairwise
      (fun a b => ¬ (a.sender = b.sender ∧ a.callData = b.callData)) ops)
    (table : Nonce2DTable) (approvals : List Bool) (i : Nat) (hi : i < ops.length) :
    countExecCalls (handleOpsTrace ops table approvals)
      ops[i].sender ops[i].callData = 1 ↔
    batchValidated ops table approvals = true ∧
    opExecutable ops i hi = true := by
  constructor
  · -- Count = 1 ⇒ both flags true.
    intro hCount
    by_contra h
    push_neg at h
    -- Case on which flag fails.
    by_cases hVal : batchValidated ops table approvals = true
    · -- Validation passed; then op cannot be executable.
      have hNotExec : opExecutable ops i hi = false := by
        cases hE : opExecutable ops i hi with
        | true => exact absurd (h hVal) (by simp [hE])
        | false => rfl
      have := yoav_count_eq_zero_when_validated_and_not_executable
        ops table approvals i hi hNotExec
      rw [this] at hCount; cases hCount
    · -- Validation failed.
      have hFail : batchValidated ops table approvals = false := by
        cases hV : batchValidated ops table approvals with
        | true => exact absurd hV hVal
        | false => rfl
      have := yoav_count_eq_zero_when_validation_fails
        ops table approvals ops[i].sender ops[i].callData hFail
      rw [this] at hCount; cases hCount
  · -- Both flags true ⇒ count = 1.
    rintro ⟨hVal, hExec⟩
    exact yoav_count_eq_one_when_validated_and_executable
      ops hDistinct table approvals i hi hVal hExec

/-! ## Composition with the bytecode-level frame -/

open EvmYulFrame
open Layout

/-- **CRITICAL_PATH T** — the headline theorem. Top-level (bytecode-level
    form): the Yoav counting biconditional holds for any sequence of
    arbitrary EVM callee invocations. Composes L1–L10 with the upstream
    frame, layout, and EntryPointV09 EOA-guard lemmas (`Verity.EVM.Frame`,
    `Verity.EVM.Layout`, `EntryPointV09.handleOp` guard checks)
    into the literal counting form of Yoav Weis's English claim. -/
theorem yoav_counting_biconditional_under_arbitrary_callees
    (ops : List PackedUserOperation)
    (hDistinct : List.Pairwise
      (fun a b => ¬ (a.sender = b.sender ∧ a.callData = b.callData)) ops)
    (table : Nonce2DTable) (approvals : List Bool) (i : Nat) (hi : i < ops.length)
    (caller : CallerFrame) (L : SolcLayout) (S : EntryPointCallSites L)
    (callees : List CalleeResult) :
    let calls := callees.map fun c => (S.outOff_eq_scratchLo, S.outSize_le_scratch, c)
    let finalFrame :=
      calls.foldl (fun st c => applyCallToCaller st c.1 c.2.1 c.2.2) caller
    -- (a) Yoav's counting biconditional holds.
    (countExecCalls (handleOpsTrace ops table approvals)
       ops[i].sender ops[i].callData = 1 ↔
     batchValidated ops table approvals = true ∧
     opExecutable ops i hi = true) ∧
    -- (b) The caller's storage at every slot is preserved.
    (∀ slotIdx, finalFrame.storageMap slotIdx = caller.storageMap slotIdx) ∧
    -- (c) The opInfos memory region is preserved.
    (∀ j, L.opInfosBase ≤ j → j < L.opInfosBase + L.opInfosWords →
      finalFrame.memory j = caller.memory j) := by
  refine ⟨?_, ?_, ?_⟩
  · exact yoav_counting_biconditional ops hDistinct table approvals i hi
  · intro slotIdx
    exact external_calls_preserve_caller_storage caller _ slotIdx
  · intro j hLo hHi
    apply external_calls_preserve_caller_memory_in_disjoint_region caller
      L.opInfosBase (L.opInfosBase + L.opInfosWords)
    · intro c hc
      obtain ⟨c', _hc', hcEq⟩ := List.mem_map.mp hc
      subst hcEq
      exact callOutputBuffer_disjoint_from_opInfos L S
    · exact hLo
    · exact hHi

end Benchmark.Cases.ERC4337.EntryPointInvariant
