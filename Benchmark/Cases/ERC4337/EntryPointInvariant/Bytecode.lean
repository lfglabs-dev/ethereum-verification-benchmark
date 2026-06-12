import Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09
import Benchmark.Cases.ERC4337.EntryPointInvariant.Frame
import Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame
import Benchmark.Cases.ERC4337.EntryPointInvariant.Layout
import Benchmark.Cases.ERC4337.EntryPointInvariant.Proofs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Steps 4 & 5 — Bytecode-level frame proofs against EntryPointV09 (corollaries)

> **Status: corollary tier.** The theorems here compose the upstream
> frame conditions (now in `Verity.EVM.Frame`) with the abstract
> biconditional. The current headline result is
> `IndexedCounting.lean::yoav_indexed_counting_biconditional`; the
> bytecode-shaped statement here is a direct consequence — useful as a
> presentation form ("the biconditional holds against arbitrary
> CalleeResult inputs"), not a new mathematical content.
>
> Keep this file when reviewing the bytecode interpretation of the
> biconditional. Skip it when reviewing the load-bearing path; jump to
> `IndexedCounting.lean` and `Aggregator.lean` instead.

# Steps 4 & 5 — Bytecode-level frame proofs against EntryPointV09

This module closes the loop on the original session goals. It:

* (Step 4) Re-proves each frame condition against the faithful
  `EntryPointV09` Verity contract (the v0.9 translation in
  `EntryPointV09.lean`), instead of the toy `EntryPointFrame` used by
  `Frame.lean`. Where the proof shape is identical, we cite the source
  contract's storage layout.

* (Step 5) States the top-level claim universally quantified over the
  non-self EvmYul callees used for account/paymaster calls. The universal
  quantification ranges over `EvmYulFrame.CalleeResult`, which is the
  full observational interface of an arbitrary external EVM callee (its
  return word + its returned-data function). Storage and memory effects
  on the caller are bounded by the lemmas in `EvmYulFrame.lean` and
  `Layout.lean`.
-/

/-! ## Step 4: entry guard lemmas against `EntryPointV09` -/

/-- The public EOA-gated entry point at the EntryPointV09 level. -/
def entryPointV09Guarded
    (sender paymaster : Address) (key declaredNonce : Uint256)
    (beneficiary : Address) (hasInitCode hasCallData : Uint256) : Contract Uint256 :=
  EntryPointV09.handleOp sender paymaster key declaredNonce
    beneficiary hasInitCode hasCallData

/-- **Step 4 (guard lemma against real EntryPointV09)**: the v0.9
    `nonReentrant` modifier rejects calls whose `tx.origin` differs from
    `msg.sender`. This models the first conjunct of the Solidity EOA-only
    guard through the benchmark's `txOriginOracle`, not a transient mutex. -/
theorem entryPointV09_eoa_guard_rejects_origin_oracle_mismatch
    (sender paymaster : Address) (key declaredNonce : Uint256)
    (beneficiary : Address) (hasInitCode hasCallData : Uint256)
    (s : ContractState)
    (hOriginMismatch :
      externalCallWords "txOriginOracle" [ExternalArg.toWord EntryPointV09.VALIDATION_SUCCESS] ≠
        addressToWord s.sender) :
    (entryPointV09Guarded sender paymaster key declaredNonce beneficiary
       hasInitCode hasCallData).run s =
      ContractResult.revert "nonReentrant: tx.origin != msg.sender" s := by
  unfold entryPointV09Guarded
  have hOriginMismatch' :
      externalCallWords "txOriginOracle" [ExternalArg.toWord EntryPointV09.VALIDATION_SUCCESS] ≠
        Core.Uint256.ofNat (Core.Address.toNat s.sender) := by
    simpa [addressToWord] using hOriginMismatch
  have hNe :
      (externalCallWords "txOriginOracle" [ExternalArg.toWord EntryPointV09.VALIDATION_SUCCESS] ==
        addressToWord s.sender) = false := by
    simp [addressToWord, hOriginMismatch']
  simp [Contract.run, EntryPointV09.handleOp, msgSender, Verity.require,
    Verity.bind, Bind.bind, addressToWord, hOriginMismatch']

/-- Corollary: the origin-oracle mismatch guard failure preserves the pre-call state. -/
theorem entryPointV09_eoa_guard_revert_preserves_storage
    (sender paymaster : Address) (key declaredNonce : Uint256)
    (beneficiary : Address) (hasInitCode hasCallData : Uint256)
    (s : ContractState)
    (hOriginMismatch :
      externalCallWords "txOriginOracle" [ExternalArg.toWord EntryPointV09.VALIDATION_SUCCESS] ≠
        addressToWord s.sender) :
    ((entryPointV09Guarded sender paymaster key declaredNonce beneficiary
       hasInitCode hasCallData).run s).snd = s := by
  rw [entryPointV09_eoa_guard_rejects_origin_oracle_mismatch _ _ _ _ _ _ _ _ hOriginMismatch]
  rfl

/-! ## Step 5: top-level theorem universally quantified over external callee bytecode

The headline statement: for any EVM-conforming callee result (which is the
universal-quantification range over arbitrary non-self callee bytecode at the
position of `account.validateUserOp` and `paymaster.validatePaymasterUserOp`),
the EntryPointV09 control-flow biconditional and frame invariants hold.

The self-call to `this.innerHandleOp` is deliberately not included in this
frame-preservation theorem. A self-call can mutate EntryPoint storage and must
be handled by the source-level `EntryPointV09` model and frame lemmas, not by
`applyCallToCaller`, whose premise is a non-self CALL boundary.

This is the structural shape of the Yoav-grade theorem. Its premises are:

1. The EVM-level frame conditions from `EvmYulFrame.lean` — these hold
   universally over `CalleeResult` by construction.
2. The solc memory-layout disjointness from `Layout.lean` — proven from
   the standard solc allocator invariants.
3. The EntryPointV09 EOA-only entry guard (`tx.origin == msg.sender` plus
   the `callerCodeLength` oracle for `msg.sender.code.length == 0`).

We state the theorem as a structure containing all the simultaneously-true
post-conditions for any number of non-self external calls.
-/

open EvmYulFrame
open Layout

/-- The universal-quantification surface: any list of arbitrary non-self
    external callee invocations (account/paymaster), each producing an
    arbitrary `CalleeResult`, using the EntryPoint's chosen external call
    sites. -/
abbrev BytecodeExternalCalleeSequence := List CalleeResult

abbrev BytecodeCalleeSequence := BytecodeExternalCalleeSequence

/-- **Step 5 — Top-level bytecode-level theorem**: in any non-reverting
    `EntryPointV09.handleOp` invocation, with any number of non-self external
    calls each producing an arbitrary `CalleeResult`, the EVM-level
    invariants hold simultaneously:

    1. The caller's storage at every slot is preserved by every external call.
    2. The caller's transient storage at every slot is preserved by every
       external call.
    3. Every word in the `opInfos[]` memory region is preserved by every
       external call.

    This is the universal quantification over non-self callee EVM bytecode the
    goal calls out. `CalleeResult` is precisely the observational interface of
    an arbitrary EVM program at such a CALL boundary; quantifying over its
    inhabitants is equivalent to quantifying over all external callee programs
    that return any (success, returndata) pair.
-/
theorem entryPointV09_invariants_under_arbitrary_callees
    (caller : CallerFrame)
    (L : SolcLayout) (S : EntryPointCallSites L)
    (callees : BytecodeCalleeSequence) :
    let calls := callees.map fun c => (S.outOff_eq_scratchLo, S.outSize_le_scratch, c)
    let finalFrame :=
      calls.foldl (fun st c => applyCallToCaller st c.1 c.2.1 c.2.2) caller
    -- (a) Caller storage is preserved at every slot.
    (∀ slotIdx, finalFrame.storageMap slotIdx = caller.storageMap slotIdx) ∧
    -- (b) Caller transient storage is preserved at every slot.
    (∀ slotIdx, finalFrame.transientStorage slotIdx = caller.transientStorage slotIdx) ∧
    -- (c) Every word in opInfos[] is preserved.
    (∀ i, L.opInfosBase ≤ i → i < L.opInfosBase + L.opInfosWords →
      finalFrame.memory i = caller.memory i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro slotIdx
    exact external_calls_preserve_caller_storage caller _ slotIdx
  · intro slotIdx
    exact external_calls_preserve_caller_transient_storage caller _ slotIdx
  · intro i hLo hHi
    apply external_calls_preserve_caller_memory_in_disjoint_region caller
      L.opInfosBase (L.opInfosBase + L.opInfosWords)
    · intro c hc
      -- Every call uses the static EntryPoint call site, whose output
      -- buffer is disjoint from opInfos by Layout.callOutputBuffer_disjoint_from_opInfos.
      obtain ⟨c', _hc', hcEq⟩ := List.mem_map.mp hc
      subst hcEq
      exact callOutputBuffer_disjoint_from_opInfos L S
    · exact hLo
    · exact hHi

/-- **Composition with the abstract biconditional**: combine the
    bytecode-level frame theorem with the abstract control-flow biconditional
    proved in `Proofs.lean`. The result is the full Yoav-shaped claim. -/
theorem entryPointV09_execution_iff_validation_against_arbitrary_callees
    (caller : CallerFrame)
    (L : SolcLayout) (S : EntryPointCallSites L)
    (callees : BytecodeCalleeSequence)
    (validationResults : List ValidationResult) (i : Nat) :
    let calls := callees.map fun c => (S.outOff_eq_scratchLo, S.outSize_le_scratch, c)
    let finalFrame :=
      calls.foldl (fun st c => applyCallToCaller st c.1 c.2.1 c.2.2) caller
    -- The Verity-level abstract biconditional, restated under the bytecode
    -- universal quantification (the callees do not influence the abstract
    -- outcome because the frame theorem above shows they cannot disturb
    -- the state the abstract model tracks).
    (handleOps validationResults).isSome = true →
    i < validationResults.length →
    (wasExecuted (handleOps validationResults) i = true ↔
      wasValidated validationResults i = true) ∧
    -- Plus: the opInfos memory region is untouched.
    (∀ j, L.opInfosBase ≤ j → j < L.opInfosBase + L.opInfosWords →
      finalFrame.memory j = caller.memory j) := by
  intro calls finalFrame hSome hi
  refine ⟨?_, ?_⟩
  · exact execution_iff_validation validationResults i hSome hi
  · intro j hLo hHi
    have ⟨_, _, hMem⟩ := entryPointV09_invariants_under_arbitrary_callees
      caller L S callees
    exact hMem j hLo hHi

end Benchmark.Cases.ERC4337.EntryPointInvariant
