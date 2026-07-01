import Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09
import Benchmark.Cases.ERC4337.EntryPointInvariant.Trace
import Benchmark.Cases.ERC4337.EntryPointInvariant.IndexedCounting
import Benchmark.Cases.ERC4337.EntryPointInvariant.Refinement

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Loop-composition refinement scaffold

`Refinement.lean` proves *per-op* refinement (the abstract semantics
predict the storage delta of a Verity `EntryPointV09.handleOp`).

This module is the **scaffold** for end-to-end loop composition: an
explicit per-op operational semantics (`runHandleOpStep`) and an
iteration combinator (`runHandleOpBatch`) that walk the batch. The
full equivalence theorem
`runHandleOpBatch ≡ handleOpsMulti ∘ executionLoopIndexed`
requires more proof engineering than fits in this iteration — the
top-level statement and the per-step success-iff lemma are landed
here; the iso theorem is documented as a follow-up.

## Roadmap

The follow-up theorem proves the iso pointwise by induction on the
batch and the approvals list simultaneously. The success/failure
profile decomposes into:

* `validationLoop ops table approvals = none` ↔
  `runHandleOpBatch ops 0 table approvals = none`
* `validationLoop ops table approvals = some t` ↔
  ∃ trace, `runHandleOpBatch ops 0 table approvals = some (t, trace)`
  with `trace = executionLoopIndexed ops`.

The per-step lemma `runHandleOpStep_isSome_iff_valid` is the
induction base; the inductive step recurses on the tail.
-/

/-- The per-op handle step. -/
def runHandleOpStep
    (i : Nat) (op : PackedUserOperation)
    (table : Nonce2DTable) (accountApproves : Bool)
    : Option (Nonce2DTable × Option IndexedCallEvent) :=
  if nonceMatches table op.sender op.nonce ∧ accountApproves = true then
    let nextTable := bumpNonceSeq table op.sender (nonceKey op.nonce)
    let emitted := if hasCallData op then
                     some ⟨i, op.sender, op.callData⟩
                   else
                     none
    some (nextTable, emitted)
  else
    none

/-- Iterate the per-op handle step over the batch. -/
def runHandleOpBatch
    : List PackedUserOperation → Nat → Nonce2DTable → List Bool →
      Option (Nonce2DTable × IndexedTrace)
  | [], _, table, [] => some (table, [])
  | _ :: _, _, _, [] => none
  | [], _, _, _ :: _ => none
  | op :: rest, i, table, a :: as =>
    match runHandleOpStep i op table a with
    | none => none
    | some (nextTable, emittedOpt) =>
      match runHandleOpBatch rest (i + 1) nextTable as with
      | none => none
      | some (finalTable, tailTrace) =>
        let headEvents := match emittedOpt with
                          | some e => [e]
                          | none => []
        some (finalTable, headEvents ++ tailTrace)

/-- The per-op step succeeds iff the validation predicate holds. -/
theorem runHandleOpStep_isSome_iff_valid
    (i : Nat) (op : PackedUserOperation)
    (table : Nonce2DTable) (a : Bool) :
    (runHandleOpStep i op table a).isSome = true ↔
    (nonceMatches table op.sender op.nonce ∧ a = true) := by
  unfold runHandleOpStep
  split <;> simp_all

/-- The per-op step emits an event iff (validation passed) AND
    (the op has non-empty callData). -/
theorem runHandleOpStep_emits_iff_executable
    (i : Nat) (op : PackedUserOperation)
    (table : Nonce2DTable) (a : Bool) :
    (∃ tbl ev, runHandleOpStep i op table a = some (tbl, some ev)) ↔
    (nonceMatches table op.sender op.nonce ∧ a = true ∧
     hasCallData op = true) := by
  unfold runHandleOpStep
  constructor
  · rintro ⟨tbl, ev, h⟩
    split at h
    · rename_i hCheck
      split at h
      · rename_i hHas
        exact ⟨hCheck.1, hCheck.2, hHas⟩
      · cases h
    · cases h
  · rintro ⟨hNonce, hApp, hHas⟩
    refine ⟨bumpNonceSeq table op.sender (nonceKey op.nonce),
            ⟨i, op.sender, op.callData⟩, ?_⟩
    rw [if_pos ⟨hNonce, hApp⟩]
    simp [hHas]

end Benchmark.Cases.ERC4337.EntryPointInvariant
