import Benchmark.Cases.ERC4337.EntryPointInvariant.UserOp

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Multi-op `handleOps` + execution-call counting

This module is the load-bearing semantic model for the Yoav-grade theorem.
It introduces:

* A `CallEvent` record modelling `Exec.call(sender, gas, 0, callData)`.
* A `Trace` = `List CallEvent` recording the execution-phase output.
* The multi-op two-loop `handleOps` model.
* A `countExecCalls` predicate counting matching events in a trace.
* The "exactly once" lemmas that compose into Yoav's headline statement.
-/

structure CallEvent where
  target   : Address
  callData : List Uint256
  deriving Repr, DecidableEq

abbrev Trace := List CallEvent

/-! ## Multi-op two-loop `handleOps` -/

/-- Validation loop: walks the ops list, increments the per-`(sender,key)`
    nonce on each successful validation, reverts on first failure. -/
def validationLoop
    : List PackedUserOperation → Nonce2DTable → (List Bool) →
      Option Nonce2DTable
  | [], table, [] => some table
  | _ :: _, _, [] => none
  | [], _, _ :: _ => none
  | op :: rest, table, accountApprovals :: restApprovals =>
    if nonceMatches table op.sender op.nonce ∧ accountApprovals = true then
      validationLoop rest
        (bumpNonceSeq table op.sender (nonceKey op.nonce)) restApprovals
    else
      none

/-- Execution loop: emits one event per op with non-empty callData.
    Mirrors `_executeUserOp → innerHandleOp → Exec.call(sender, …, callData)`
    with the `callData.length > 0` branch encoded faithfully. -/
def executionLoop : List PackedUserOperation → Trace
  | [] => []
  | op :: rest =>
    if hasCallData op then
      ⟨op.sender, op.callData⟩ :: executionLoop rest
    else
      executionLoop rest

/-- Multi-op `handleOps`. -/
def handleOpsMulti
    (ops : List PackedUserOperation)
    (table : Nonce2DTable)
    (accountApprovals : List Bool)
    : Option (Nonce2DTable × Trace) :=
  match validationLoop ops table accountApprovals with
  | some finalTable => some (finalTable, executionLoop ops)
  | none => none

/-! ## Counting predicate -/

def matchesCallEvent (s : Address) (c : List Uint256) (e : CallEvent) : Bool :=
  decide (e.target = s ∧ e.callData = c)

def countExecCalls (trace : Trace) (s : Address) (c : List Uint256) : Nat :=
  (trace.filter (matchesCallEvent s c)).length

/-! ## Core lemmas -/

/-- **CRITICAL_PATH L2** — Every event in `executionLoop ops` originates
    from some op in `ops` with non-empty callData. Backs the at-most-once
    bound by giving the head-distinctness argument something to bite on. -/
theorem executionLoop_event_origin
    (ops : List PackedUserOperation) (e : CallEvent)
    (he : e ∈ executionLoop ops) :
    ∃ op ∈ ops, hasCallData op = true ∧
      e.target = op.sender ∧ e.callData = op.callData := by
  induction ops with
  | nil => simp [executionLoop] at he
  | cons op rest ih =>
    simp only [executionLoop] at he
    split at he
    · rename_i hHas
      rcases List.mem_cons.mp he with hHd | hTl
      · refine ⟨op, List.mem_cons_self .., hHas, ?_, ?_⟩ <;>
          (subst hHd; rfl)
      · obtain ⟨op', hMem', hHas', hT, hD⟩ := ih hTl
        exact ⟨op', List.mem_cons_of_mem _ hMem', hHas', hT, hD⟩
    · obtain ⟨op', hMem', hHas', hT, hD⟩ := ih he
      exact ⟨op', List.mem_cons_of_mem _ hMem', hHas', hT, hD⟩

/-- An op `op` with non-empty callData contributes its event to the loop. -/
theorem executionLoop_contains_op_event
    (ops : List PackedUserOperation) (op : PackedUserOperation)
    (hMem : op ∈ ops) (hHas : hasCallData op = true) :
    ⟨op.sender, op.callData⟩ ∈ executionLoop ops := by
  induction ops with
  | nil => cases hMem
  | cons hd rest ih =>
    simp only [executionLoop]
    rcases List.mem_cons.mp hMem with hEq | hTail
    · subst hEq
      rw [if_pos hHas]; exact List.mem_cons_self ..
    · split
      · exact List.mem_cons_of_mem _ (ih hTail)
      · exact ih hTail

/-- **CRITICAL_PATH L6** — The trace contains at most one event matching
    `(s, c)` when all ops in the batch have distinct `(sender, callData)`
    pairs. This is the "exactly once" upper bound Yoav describes. -/
theorem executionLoop_count_le_one
    (ops : List PackedUserOperation)
    (hDistinct : List.Pairwise
      (fun a b => ¬ (a.sender = b.sender ∧ a.callData = b.callData)) ops)
    (s : Address) (c : List Uint256) :
    countExecCalls (executionLoop ops) s c ≤ 1 := by
  induction ops with
  | nil => simp [executionLoop, countExecCalls]
  | cons op rest ih =>
    have hRestDistinct := (List.pairwise_cons.mp hDistinct).2
    have hHeadDistinct := (List.pairwise_cons.mp hDistinct).1
    simp only [executionLoop]
    split
    · rename_i hHas
      -- Head emits its event ⟨op.sender, op.callData⟩.
      by_cases hHd : op.sender = s ∧ op.callData = c
      · -- Head matches. No tail op can match by hDistinct, so tail count = 0.
        have hTailCount : countExecCalls (executionLoop rest) s c = 0 := by
          unfold countExecCalls
          have : (executionLoop rest).filter (matchesCallEvent s c) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e he hMatch
            unfold matchesCallEvent at hMatch
            simp at hMatch
            obtain ⟨op', hMem', _, hET, hED⟩ :=
              executionLoop_event_origin rest e he
            have hopop' :
                ¬ (op.sender = op'.sender ∧ op.callData = op'.callData) :=
              hHeadDistinct op' hMem'
            apply hopop'
            constructor
            · rw [hHd.1, ← hMatch.1, hET]
            · rw [hHd.2, ← hMatch.2, hED]
          rw [this]; simp
        unfold countExecCalls
        simp only [List.filter_cons]
        have hMatchHead : matchesCallEvent s c ⟨op.sender, op.callData⟩ = true := by
          unfold matchesCallEvent; simp [hHd]
        rw [if_pos hMatchHead]
        simp only [List.length_cons]
        unfold countExecCalls at hTailCount
        omega
      · -- Head does not match.
        unfold countExecCalls
        simp only [List.filter_cons]
        have hMatchHead : matchesCallEvent s c ⟨op.sender, op.callData⟩ = false := by
          unfold matchesCallEvent; simp; intro h1 h2; exact hHd ⟨h1, h2⟩
        rw [if_neg (by simp [hMatchHead])]
        exact ih hRestDistinct
    · exact ih hRestDistinct

/-- **CRITICAL_PATH L7** — `countExecCalls ≥ 1` whenever a validated op
    with non-empty callData matches. The companion lower bound to L6. -/
theorem executionLoop_count_ge_one
    (ops : List PackedUserOperation) (op : PackedUserOperation)
    (hMem : op ∈ ops) (hHas : hasCallData op = true)
    (s : Address) (c : List Uint256)
    (hMatch : op.sender = s ∧ op.callData = c) :
    countExecCalls (executionLoop ops) s c ≥ 1 := by
  unfold countExecCalls
  have hEvent : ⟨op.sender, op.callData⟩ ∈ executionLoop ops :=
    executionLoop_contains_op_event ops op hMem hHas
  have hFilterMem :
      (⟨op.sender, op.callData⟩ : CallEvent) ∈
      (executionLoop ops).filter (matchesCallEvent s c) := by
    rw [List.mem_filter]
    refine ⟨hEvent, ?_⟩
    unfold matchesCallEvent; simp [hMatch]
  exact List.length_pos_of_mem hFilterMem

/-- **Counting biconditional (head form)**: under pairwise distinctness and
    given an op `op` matching `(s, c)` with non-empty callData,
    `countExecCalls = 1` exactly. -/
theorem executionLoop_count_eq_one
    (ops : List PackedUserOperation)
    (hDistinct : List.Pairwise
      (fun a b => ¬ (a.sender = b.sender ∧ a.callData = b.callData)) ops)
    (op : PackedUserOperation) (hMem : op ∈ ops) (hHas : hasCallData op = true)
    (s : Address) (c : List Uint256) (hMatch : op.sender = s ∧ op.callData = c) :
    countExecCalls (executionLoop ops) s c = 1 := by
  have hUpper := executionLoop_count_le_one ops hDistinct s c
  have hLower := executionLoop_count_ge_one ops op hMem hHas s c hMatch
  omega

end Benchmark.Cases.ERC4337.EntryPointInvariant
