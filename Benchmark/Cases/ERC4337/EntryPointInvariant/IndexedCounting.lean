import Benchmark.Cases.ERC4337.EntryPointInvariant.Trace
import Benchmark.Cases.ERC4337.EntryPointInvariant.Yoav

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
# Indexed counting — Yoav's claim without the pairwise-distinct premise

The `yoav_counting_biconditional` in `Yoav.lean` counts execution events
by `(sender, callData)`. This requires the bundler to enforce pairwise
distinctness of those pairs, otherwise two ops with identical
`(sender, callData)` would each contribute one event, and the counting
biconditional would say "count = 2" for each op rather than "exactly one
per op."

Real ERC-4337 bundlers do enforce per-op uniqueness — but via per-
`(sender, nonce)` uniqueness, not per-`(sender, callData)`. So the
pairwise-distinct premise is meaningful but ergonomic.

This file gives the cleaner form: tag each emitted event with its source
op index. Then "exactly once per validated op" is a counting property
indexed by the op's position in the batch — no distinctness premise
needed, because op indices are inherently unique.

The Yoav English claim, restated:

> "Execution will happen exactly once, if and only if validation was
> successful for that UserOp."

The phrase "that UserOp" picks out the op by identity, not by
`(sender, callData)`. The indexed counting captures that directly.
-/

/-- A CallEvent tagged with its source op index. -/
structure IndexedCallEvent where
  opIdx    : Nat
  target   : Address
  callData : List Uint256
  deriving Repr, DecidableEq

abbrev IndexedTrace := List IndexedCallEvent

/-- Indexed execution loop: emits one event per executable op with its
    source index. The index is just the position in the input list. -/
def executionLoopIndexed
    (ops : List PackedUserOperation) : IndexedTrace :=
  let rec go : Nat → List PackedUserOperation → IndexedTrace
    | _, [] => []
    | i, op :: rest =>
      if hasCallData op then
        ⟨i, op.sender, op.callData⟩ :: go (i + 1) rest
      else
        go (i + 1) rest
  go 0 ops

/-- Indexed counting: how many events in the trace have a given op index. -/
def countByIndex (trace : IndexedTrace) (idx : Nat) : Nat :=
  (trace.filter (fun e => decide (e.opIdx = idx))).length

/-! ## Core lemmas — no distinctness premise -/

/-- Helper: `executionLoopIndexed.go` with a non-zero offset adjusts each
    emitted index by the offset. -/
private theorem executionLoopIndexed_go_offset
    (i : Nat) (ops : List PackedUserOperation) (target : Nat) :
    (executionLoopIndexed.go i ops).filter (fun e => decide (e.opIdx = target)) =
    if target ≥ i then
      (executionLoopIndexed.go i ops).filter (fun e => decide (e.opIdx = target))
    else [] := by
  split <;> rfl

/-- The indexed loop emits the event for op `i` exactly when op `i` has
    non-empty callData. The index of that event equals `i`. -/
theorem executionLoopIndexed_count_eq_one_of_executable
    (ops : List PackedUserOperation) (i : Nat) (hi : i < ops.length)
    (hHas : hasCallData ops[i] = true) :
    countByIndex (executionLoopIndexed ops) i = 1 := by
  -- Inductive argument on the list with an offset.
  unfold countByIndex executionLoopIndexed
  -- Generalise the offset.
  suffices h : ∀ (start : Nat) (xs : List PackedUserOperation) (j : Nat)
      (hj : j < xs.length),
        hasCallData xs[j] = true →
        ((executionLoopIndexed.go start xs).filter
          (fun e => decide (e.opIdx = start + j))).length = 1 by
    have := h 0 ops i hi hHas
    simpa using this
  intro start xs
  induction xs generalizing start with
  | nil => intros; omega
  | cons hd rest ih =>
    intro j hj hHas
    cases j with
    | zero =>
      -- Op at position 0 is `hd`.
      simp only [executionLoopIndexed.go]
      simp at hHas
      rw [if_pos hHas]
      simp only [List.filter_cons]
      have hHead : decide ((⟨start, hd.sender, hd.callData⟩ :
          IndexedCallEvent).opIdx = start + 0) = true := by simp
      rw [if_pos hHead]
      simp only [List.length_cons]
      -- Tail filter is empty because indices are start+1, start+2, ... ≠ start.
      have hTailZero :
          ((executionLoopIndexed.go (start + 1) rest).filter
            (fun e => decide (e.opIdx = start + 0))).length = 0 := by
        suffices h : (executionLoopIndexed.go (start + 1) rest).filter
            (fun e => decide (e.opIdx = start + 0)) = [] by
          rw [h]; rfl
        apply List.filter_eq_nil_iff.mpr
        intro e he
        have : e.opIdx ≥ start + 1 := by
          clear * - he
          induction rest generalizing e start with
          | nil => simp [executionLoopIndexed.go] at he
          | cons hd' rest' ih' =>
            simp only [executionLoopIndexed.go] at he
            split at he
            · rcases List.mem_cons.mp he with hHd | hTl
              · subst hHd; simp
              · have := ih' (start + 1) e hTl; omega
            · have := ih' (start + 1) e he; omega
        simp; omega
      omega
    | succ k =>
      -- Op at position k+1 is in rest at position k.
      simp only [executionLoopIndexed.go]
      simp [List.length_cons] at hj
      have hk : k < rest.length := by omega
      have hHasK : hasCallData rest[k] = true := by simpa using hHas
      have hIH := ih (start + 1) k hk hHasK
      -- start + (k + 1) = (start + 1) + k
      have hShift : start + (k + 1) = (start + 1) + k := by omega
      rw [hShift]
      split
      · rename_i hHasHd
        simp only [List.filter_cons]
        have hHeadFalse :
            decide ((⟨start, hd.sender, hd.callData⟩ :
              IndexedCallEvent).opIdx = (start + 1) + k) = false := by
          simp; omega
        rw [if_neg (by simp [hHeadFalse])]
        exact hIH
      · exact hIH

/-- If op `i` is not executable (empty callData), the indexed loop emits
    no event for it: `countByIndex = 0`. -/
theorem executionLoopIndexed_count_eq_zero_of_not_executable
    (ops : List PackedUserOperation) (i : Nat) (hi : i < ops.length)
    (hHas : hasCallData ops[i] = false) :
    countByIndex (executionLoopIndexed ops) i = 0 := by
  unfold countByIndex executionLoopIndexed
  suffices h : ∀ (start : Nat) (xs : List PackedUserOperation) (j : Nat)
      (hj : j < xs.length),
        hasCallData xs[j] = false →
        ((executionLoopIndexed.go start xs).filter
          (fun e => decide (e.opIdx = start + j))).length = 0 by
    have := h 0 ops i hi hHas
    simpa using this
  intro start xs
  induction xs generalizing start with
  | nil => intros; omega
  | cons hd rest ih =>
    intro j hj hHas
    cases j with
    | zero =>
      simp only [executionLoopIndexed.go]
      simp at hHas
      rw [if_neg (by simp [hHas])]
      -- Tail filter is empty by same offset argument.
      suffices h : (executionLoopIndexed.go (start + 1) rest).filter
          (fun e => decide (e.opIdx = start + 0)) = [] by
        rw [h]; rfl
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have : e.opIdx ≥ start + 1 := by
        clear * - he
        induction rest generalizing e start with
        | nil => simp [executionLoopIndexed.go] at he
        | cons hd' rest' ih' =>
          simp only [executionLoopIndexed.go] at he
          split at he
          · rcases List.mem_cons.mp he with hHd | hTl
            · subst hHd; simp
            · have := ih' (start + 1) e hTl; omega
          · have := ih' (start + 1) e he; omega
      simp; omega
    | succ k =>
      simp only [executionLoopIndexed.go]
      simp [List.length_cons] at hj
      have hk : k < rest.length := by omega
      have hHasK : hasCallData rest[k] = false := by simpa using hHas
      have hIH := ih (start + 1) k hk hHasK
      have hShift : start + (k + 1) = (start + 1) + k := by omega
      rw [hShift]
      split
      · simp only [List.filter_cons]
        have hHeadFalse :
            decide ((⟨start, hd.sender, hd.callData⟩ :
              IndexedCallEvent).opIdx = (start + 1) + k) = false := by
          simp; omega
        rw [if_neg (by simp [hHeadFalse])]
        exact hIH
      · exact hIH

/-! ## Top-level indexed biconditional (no distinctness premise!)

The headline result without the pairwise-distinct assumption. This is
the strongest defensible form of Yoav's claim: it counts execution
events *per op*, not per `(sender, callData)`, so two ops with identical
calldata each get their own counted event, and the biconditional holds
unconditionally.
-/

def handleOpsIndexedTrace
    (ops : List PackedUserOperation) (table : Nonce2DTable)
    (approvals : List Bool) : IndexedTrace :=
  match validationLoop ops table approvals with
  | some _ => executionLoopIndexed ops
  | none   => []

/-- **The Yoav biconditional, indexed form — unconditional**.

    For each op index `i`, the execution-event count is `1` iff the batch
    validated AND op `i` has non-empty callData. Otherwise the count is
    `0`. No pairwise-distinctness premise required — op indices are
    inherently unique. -/
theorem yoav_indexed_counting_biconditional
    (ops : List PackedUserOperation) (table : Nonce2DTable)
    (approvals : List Bool) (i : Nat) (hi : i < ops.length) :
    countByIndex (handleOpsIndexedTrace ops table approvals) i = 1 ↔
    batchValidated ops table approvals = true ∧
    hasCallData ops[i] = true := by
  unfold handleOpsIndexedTrace batchValidated
  cases hVL : validationLoop ops table approvals with
  | some _ =>
    simp only
    by_cases hHas : hasCallData ops[i] = true
    · have := executionLoopIndexed_count_eq_one_of_executable ops i hi hHas
      simp [this, hHas]
    · have hHasFalse : hasCallData ops[i] = false := by
        cases h : hasCallData ops[i] with
        | true  => exact absurd h hHas
        | false => rfl
      have := executionLoopIndexed_count_eq_zero_of_not_executable ops i hi hHasFalse
      simp [this, hHasFalse]
  | none =>
    simp [countByIndex]

end Benchmark.Cases.ERC4337.EntryPointInvariant
