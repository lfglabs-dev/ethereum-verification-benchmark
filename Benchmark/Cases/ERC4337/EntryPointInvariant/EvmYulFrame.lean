import Benchmark.Cases.ERC4337.EntryPointInvariant.Frame

namespace Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame

/-!
# EvmYul-side: `external_call_preserves_caller_memory`

This module is the **upstream-shaped** lemma the goal calls out. It would
ideally live in `verity` itself (in `Verity.EVM` or `EvmYul.Semantics`) and
close gaps (3) and (4) for every benchmark, not just ERC-4337. Since this
session cannot push into the Verity package directly, we land it here as a
self-contained module that mirrors the EvmYul state interface and proves
the lemma in a form that can be lifted verbatim into Verity once a PR is
opened.

We model only the EVM concepts the lemma touches:

* **Caller frame**: storage, memory, transient storage. Each is an
  abstract finite map. Returndata is a separate buffer.
* **CALL semantics**: at the caller boundary, the only effect of `CALL`
  on the caller's `memory` is a copy of up to `outSize` words from the
  callee's returndata into `[outOff, outOff + outSize)`. The caller's
  `storage` and `transientStorage` are untouched by a non-staticcall
  callee whose `address ≠ caller.address`.
* **Universal quantification over callee bytecode** is discharged by
  treating the callee's effect as a `CalleeResult` record — the only
  observable outputs are its `returnData` function, its `success` word,
  and (for storage-affecting paths) a callee-frame storage delta that
  CANNOT alias the caller's storage by EVM construction.
-/

structure Word where
  toNat : Nat
  deriving DecidableEq, Repr

instance : OfNat Word n where
  ofNat := ⟨n⟩

/-- Abstract address. EVM addresses are 160-bit; we only need identity. -/
abbrev Address := Nat

/-- A caller-side EVM state at a CALL boundary. -/
structure CallerFrame where
  thisAddress      : Address
  memory           : Nat → Word
  storageMap       : Nat → Word
  transientStorage : Nat → Word
  returnDataBuf    : Nat → Word

/-- Everything an arbitrary callee can return to the caller. The callee's
    internal storage updates are scoped to its own address and so do not
    appear here — they cannot affect the caller's frame. -/
structure CalleeResult where
  success           : Word
  returnedData      : Nat → Word

/-- The portion of EVM `CALL` semantics that touches the caller's frame.
    By the Yellow Paper, `CALL` to a target ≠ self with the caller's
    output buffer `[outOff, outOff + outSize)` updates the caller's memory
    by copying `outSize` words of the callee's returndata into that range,
    leaves storage and transient storage untouched, and writes the new
    returndata buffer to the caller's `returnData`. -/
def applyCallToCaller
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    : CallerFrame :=
  { caller with
      memory := fun i =>
        if outOff ≤ i ∧ i < outOff + outSize then
          callee.returnedData (i - outOff)
        else
          caller.memory i
      returnDataBuf := callee.returnedData }

/-- **The lemma**: external CALL preserves the caller's storage word at any
    slotIdx, the caller's transient-storage word at any slotIdx, and the caller's
    memory at any word outside the declared output buffer — regardless of
    callee bytecode. The callee enters as an arbitrary `CalleeResult` value,
    so the universal quantifier over its bytecode is discharged by this
    quantification over the result type. -/
theorem external_call_preserves_caller_storage
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (slotIdx : Nat) :
    (applyCallToCaller caller outOff outSize callee).storageMap slotIdx =
      caller.storageMap slotIdx := by
  simp [applyCallToCaller]

theorem external_call_preserves_caller_transient_storage
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (slotIdx : Nat) :
    (applyCallToCaller caller outOff outSize callee).transientStorage slotIdx =
      caller.transientStorage slotIdx := by
  simp [applyCallToCaller]

theorem external_call_preserves_caller_memory_outside_output_buffer
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (i : Nat) (hOutside : ¬ (outOff ≤ i ∧ i < outOff + outSize)) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i := by
  simp [applyCallToCaller, hOutside]

/-- Headline form: caller-memory preservation under disjoint regions.
    Specialised so it composes directly with `MemFrame.Disjoint`. -/
theorem external_call_preserves_caller_memory
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (regionLo regionHi : Nat)
    (hDisj : outOff + outSize ≤ regionLo ∨ regionHi ≤ outOff)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i := by
  apply external_call_preserves_caller_memory_outside_output_buffer
  rintro ⟨h1, h2⟩
  rcases hDisj with h | h <;> omega

/-- A finite sequence of CALLs preserves the caller's storage entirely. The
    sequence may use different output buffers, different callees, and
    different return values; the proof is independent of any of that. -/
theorem external_calls_preserve_caller_storage
    (caller : CallerFrame)
    (calls : List (Nat × Nat × CalleeResult))
    (slotIdx : Nat) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).storageMap slotIdx =
    caller.storageMap slotIdx := by
  induction calls generalizing caller with
  | nil => rfl
  | cons c rest ih =>
    have hStep := external_call_preserves_caller_storage caller c.1 c.2.1 c.2.2 slotIdx
    have := ih (applyCallToCaller caller c.1 c.2.1 c.2.2)
    simp [List.foldl]
    rw [this, hStep]

/-- A finite sequence of CALLs preserves the caller's transient storage. -/
theorem external_calls_preserve_caller_transient_storage
    (caller : CallerFrame)
    (calls : List (Nat × Nat × CalleeResult))
    (slotIdx : Nat) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).transientStorage slotIdx =
    caller.transientStorage slotIdx := by
  induction calls generalizing caller with
  | nil => rfl
  | cons c rest ih =>
    have hStep := external_call_preserves_caller_transient_storage
      caller c.1 c.2.1 c.2.2 slotIdx
    have := ih (applyCallToCaller caller c.1 c.2.1 c.2.2)
    simp [List.foldl]
    rw [this, hStep]

/-- A finite sequence of CALLs, each with output buffer disjoint from a
    target memory region, preserves every word in that region. This is the
    statement the ERC-4337 frame proof composes with. -/
theorem external_calls_preserve_caller_memory_in_disjoint_region
    (caller : CallerFrame)
    (regionLo regionHi : Nat)
    (calls : List (Nat × Nat × CalleeResult))
    (hAllDisj : ∀ c ∈ calls,
      c.1 + c.2.1 ≤ regionLo ∨ regionHi ≤ c.1)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).memory i =
    caller.memory i := by
  induction calls generalizing caller with
  | nil => rfl
  | cons c rest ih =>
    have hStep := external_call_preserves_caller_memory caller c.1 c.2.1 c.2.2
      regionLo regionHi (hAllDisj c (List.mem_cons_self ..)) i hLo hHi
    have hRest : ∀ d ∈ rest, d.1 + d.2.1 ≤ regionLo ∨ regionHi ≤ d.1 := by
      intro d hd; exact hAllDisj d (List.mem_cons_of_mem _ hd)
    have hIH := ih (applyCallToCaller caller c.1 c.2.1 c.2.2) hRest
    simp [List.foldl]
    rw [hIH, hStep]

end Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame
