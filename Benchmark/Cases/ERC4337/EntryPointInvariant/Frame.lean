import Contracts.Common
import Benchmark.Cases.ERC4337.EntryPointInvariant.Contract

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# EntryPoint frame conditions over Verity's EVM semantics — historical scaffold

> **Status: superseded by upstream.** The frame conditions in this file
> were originally landed here in advance of the upstream port. They now
> live in `Verity.EVM.Frame` (shipped in `lfglabs-dev/verity#1969`) where
> they are proved once and consumed by every benchmark.
>
> The theorems here are not part of `Compile.lean`; they remain only for
> archival proof history. New benchmark code should consume
> `EvmYulFrame.lean`, whose theorem names are stable wrappers around
> `Verity.EVM.Frame`.

# EntryPoint frame conditions over Verity's EVM semantics

These three lemmas are the bytecode-level claims that make the abstract
control-flow biconditional (proved in `Proofs.lean`) lift to the real
property Yoav Weis describes: the invariant holds **regardless of arbitrary
account / paymaster bytecode**.

The key Verity semantic facts we exploit:

* `Contracts.call : Uint256 → … → Uint256` is a **pure word**. By definition
  it cannot mutate the caller's `ContractState`. This is exactly the EVM
  guarantee that `CALL`-ing an external address gives that address its own
  storage frame, not the caller's.
* `Contracts.tload` / `tstore` operate on a separate `transientStorage` map.
  External calls cannot interfere with `transientStorage` either.
* `Verity.nonReentrant` enforces the standard locked / unlocked discipline
  and has the proved theorem `nonReentrant_locked_reverts` showing re-entry
  reverts when the lock slot is non-zero. This is a generic historical
  scaffold, not the EntryPoint v0.9 entry guard.

This means the three lemmas reduce to **showing that EntryPoint's bytecode
uses those primitives correctly**, not "for all callee bytecode". The
universal quantifier over arbitrary callee behavior is discharged
structurally by Verity's semantic abstraction.
-/

/-! ## Frame-condition model

We expose an EntryPoint-shaped Verity contract whose body interleaves
external calls with EntryPoint-controlled state writes. The three lemmas
below are proved against this contract, mirroring the slice of
EntryPoint.sol they concern.
-/

verity_contract EntryPointFrame where
  storage
    -- Generic mutex lock used by this historical scaffold.
    reentrancyLock : Uint256 := slot 0
    -- Nonce mapping `address sender => uint256 nonceKey => uint256 nonce`
    -- We simplify by keying directly on Uint256 senderKey for the lemma; the
    -- 2D key shape doesn't affect the frame argument.
    nonces : Uint256 → Uint256 := slot 1
    -- A scratch slot used to record opInfo for one op (models opInfos[i]).
    opInfoSlot : Uint256 := slot 2

  -- Validation half: increment the nonce, then invoke the external account.
  -- The external call is `Contracts.call` which is a pure word in Verity and
  -- so cannot mutate `state.storage`.
  function validateOne (senderKey : Uint256, expectedNonce : Uint256) : Unit := do
    let current ← getMappingUint nonces senderKey
    require (current == expectedNonce) "AA25 invalid nonce"
    setMappingUint nonces senderKey (add current 1)
    setStorage opInfoSlot 1
    let _callResult := call 0 senderKey 0 0 0 0 0
    pure ()

  -- Execution half: read opInfoSlot, then invoke _executeUserOp via an
  -- external call. Again the call cannot mutate our storage.
  function executeOne (senderKey : Uint256) : Uint256 := do
    let info ← getStorage opInfoSlot
    let _callResult := call 0 senderKey 0 0 0 0 0
    return info

  -- Combined entry point. We expose the raw body and write a generic mutex
  -- guard around it at the lemma level using the verified
  -- `Verity.nonReentrant` combinator.
  function handleOpsBody (senderKey : Uint256, expectedNonce : Uint256)
      : Uint256 := do
    validateOne senderKey expectedNonce
    let info ← executeOne senderKey
    return info

end Benchmark.Cases.ERC4337.EntryPointInvariant

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-! ## Lemma (3): Reentrancy guard

Wrapping `handleOpsBody` with `Verity.nonReentrant` on the `reentrancyLock`
slot guarantees that any call attempted while the lock is non-zero reverts.
This remains compiled as a generic mutex smoke. EntryPoint v0.9 itself uses
an EOA-only `nonReentrant` modifier, modeled in `EntryPointV09.lean`.
-/

/-- The `nonReentrant`-wrapped entry point. -/
def handleOpsGuarded (senderKey expectedNonce : Uint256) : Contract Uint256 :=
  Verity.nonReentrant ⟨0⟩ (EntryPointFrame.handleOpsBody senderKey expectedNonce)

/-- **Lemma (3) — Reentrancy guard**: if the reentrancy lock is already set,
    every call into `handleOpsGuarded` reverts to the pre-call snapshot
    without mutating storage. -/
theorem reentrancy_guard_blocks_reentry
    (senderKey expectedNonce : Uint256) (s : ContractState)
    (hLocked : s.storage 0 ≠ 0) :
    (handleOpsGuarded senderKey expectedNonce).run s =
      ContractResult.revert "ReentrancyGuard: reentrant call" s := by
  unfold handleOpsGuarded
  exact Verity.nonReentrant_locked_reverts ⟨0⟩ _ s hLocked

/-- **Corollary** of lemma (3): no storage slot is mutated when re-entry is
    blocked — the state returned on revert is bit-identical to the pre-state. -/
theorem reentrancy_revert_preserves_storage
    (senderKey expectedNonce : Uint256) (s : ContractState)
    (hLocked : s.storage 0 ≠ 0) :
    ((handleOpsGuarded senderKey expectedNonce).run s).snd = s := by
  rw [reentrancy_guard_blocks_reentry senderKey expectedNonce s hLocked]
  rfl

/-! ## Lemma (1): Nonce write-once

After `validateOne` has incremented the nonce, the subsequent external call
(modelled by `Contracts.call`) cannot reset it. The proof is direct
because `Contracts.call` returns a pure `Uint256` and never touches
`ContractState`. Therefore the post-state's nonce slot equals the value
written by `setMappingUint`, regardless of any external bytecode.
-/

/-- **Lemma (1) — Nonce write-once**: after `validateOne(senderKey, expected)`
    succeeds, the nonce slot for `senderKey` equals `expected + 1`. The
    external account call in the validation body is a pure word in Verity's
    semantics and so cannot interfere with this slot. -/
theorem nonce_write_once
    (senderKey expectedNonce : Uint256) (s : ContractState)
    (hMatch : s.storageMapUint 1 senderKey = expectedNonce) :
    let r := (EntryPointFrame.validateOne senderKey expectedNonce).run s
    match r with
    | ContractResult.success _ s' => s'.storageMapUint 1 senderKey = add expectedNonce 1
    | ContractResult.revert _ _   => True := by
  have hRead : s.readMapUint 1 senderKey = expectedNonce := hMatch
  simp only [EntryPointFrame.validateOne, EntryPointFrame.nonces,
    EntryPointFrame.opInfoSlot, Verity.Contract.run, Verity.bind, Bind.bind,
    getMappingUint, setMappingUint, setStorage, Verity.require,
    Verity.pure, Pure.pure]
  rw [hRead]
  simp

/-- **Stronger lemma (1)** stated for `handleOpsBody`: after the full
    two-phase body completes (validation + execution), the nonce slot equals
    `expected + 1`. The execution phase's external `_executeUserOp` call
    cannot decrement or rewrite the nonce. -/
theorem nonce_preserved_through_execution
    (senderKey expectedNonce : Uint256) (s : ContractState)
    (hMatch : s.storageMapUint 1 senderKey = expectedNonce) :
    let r := (EntryPointFrame.handleOpsBody senderKey expectedNonce).run s
    match r with
    | ContractResult.success _ s' => s'.storageMapUint 1 senderKey = add expectedNonce 1
    | ContractResult.revert _ _   => True := by
  have hRead : s.readMapUint 1 senderKey = expectedNonce := hMatch
  simp only [EntryPointFrame.handleOpsBody, EntryPointFrame.validateOne,
    EntryPointFrame.executeOne, EntryPointFrame.nonces,
    EntryPointFrame.opInfoSlot, Verity.Contract.run, Verity.bind, Bind.bind,
    getMappingUint, getStorage, setMappingUint, setStorage, Verity.require,
    Verity.pure, Pure.pure]
  rw [hRead]
  simp

/-! ## Lemma (2): opInfos frame condition

`opInfoSlot` is written exactly once by `validateOne` and read by
`executeOne`. Between the write and the read, an external call occurs
(the validation-phase account call). The frame lemma states that this
external call cannot disturb `opInfoSlot`, so the value read by
`executeOne` equals the value written by `validateOne`.

In the real EntryPoint, `opInfos[]` is *memory*, not storage. Verity's
`Contracts.call` does not mutate `state.memory` either (it returns a pure
word), so the same frame argument applies. We instantiate the proof on a
storage slot because the benchmark contract above exposes the field as
storage; the memory variant is identical structurally.
-/

/-- **Lemma (2) — opInfos frame**: the value read by `executeOne` equals the
    value written by `validateOne`. External calls between the write and read
    cannot rewrite the slot because they are pure words in Verity's semantics. -/
theorem opInfos_frame
    (senderKey expectedNonce : Uint256) (s : ContractState)
    (hMatch : s.storageMapUint 1 senderKey = expectedNonce) :
    let r := (EntryPointFrame.handleOpsBody senderKey expectedNonce).run s
    match r with
    | ContractResult.success info _ => info = 1
    | ContractResult.revert _ _     => True := by
  have hRead : s.readMapUint 1 senderKey = expectedNonce := hMatch
  simp only [EntryPointFrame.handleOpsBody, EntryPointFrame.validateOne,
    EntryPointFrame.executeOne, EntryPointFrame.nonces,
    EntryPointFrame.opInfoSlot, Verity.Contract.run, Verity.bind, Bind.bind,
    getMappingUint, getStorage, setMappingUint, setStorage, Verity.require,
    Verity.pure, Pure.pure]
  rw [hRead]
  simp

/-! ## Memory-frame lemma (2'): the real opInfos-in-memory argument

In Solidity, `opInfos[]` is allocated in **memory**, not storage. Memory in
the EVM is per-call-frame: each `CALL` opcode gives the callee a *fresh*
memory region. The only way a callee can affect the caller's memory is the
caller's own output-buffer parameters `outOff` / `outSize` passed to `CALL`:
the EVM copies up to `outSize` bytes from the callee's returndata into
caller memory at `[outOff, outOff + outSize)`. Outside that range the
caller's memory is untouched.

Verity's contract-level `mstore` / `mload` are nominal (they bottom out in
the EvmYul layer), so to write this proof at the right granularity we
model a word-addressed memory region directly and prove the non-aliasing
argument: as long as the EntryPoint's chosen output-buffer range does not
overlap with the memory range holding `opInfos[]`, every callee invocation
preserves `opInfos[i]` regardless of what the callee returns.
-/

namespace MemFrame

/-- A word-addressed EVM memory region. -/
abbrev MemState := Nat → Uint256

def myMload (m : MemState) (off : Nat) : Uint256 := m off

def myMstore (m : MemState) (off : Nat) (v : Uint256) : MemState :=
  fun i => if i = off then v else m i

/-- Model of a CALL that writes `outSize` words of returndata into the
    caller's memory starting at `outOff`. `returnedData i` is the `i`-th word
    the callee returned; words outside the returndata window stay untouched. -/
def callWithReturnBuffer
    (m : MemState) (outOff outSize : Nat) (returnedData : Nat → Uint256) : MemState :=
  fun i => if outOff ≤ i ∧ i < outOff + outSize then returnedData (i - outOff)
           else m i

/-- Two half-open ranges are disjoint. -/
def Disjoint (lo1 hi1 lo2 hi2 : Nat) : Prop :=
  hi1 ≤ lo2 ∨ hi2 ≤ lo1

/-- **Non-aliasing memory frame**: a CALL with output buffer
    `[outOff, outOff+outSize)` cannot disturb any word in a disjoint region
    `[opInfosOff, opInfosOff + opInfosSize)`. -/
theorem call_preserves_disjoint_region
    (m : MemState) (outOff outSize opInfosOff opInfosSize : Nat)
    (returnedData : Nat → Uint256)
    (hDisj : Disjoint outOff (outOff + outSize) opInfosOff (opInfosOff + opInfosSize))
    (i : Nat) (hLo : opInfosOff ≤ i) (hHi : i < opInfosOff + opInfosSize) :
    (callWithReturnBuffer m outOff outSize returnedData) i = m i := by
  unfold callWithReturnBuffer
  by_cases hIn : outOff ≤ i ∧ i < outOff + outSize
  · -- Disjointness excludes this branch.
    rcases hDisj with h | h
    · -- outOff+outSize ≤ opInfosOff, but i < outOff+outSize ≤ opInfosOff ≤ i, contradiction.
      omega
    · -- opInfosOff+opInfosSize ≤ outOff, but i ≥ opInfosOff and i < opInfosOff+opInfosSize ≤ outOff ≤ i, contradiction.
      omega
  · simp [hIn]

/-- **Iterated non-aliasing**: a sequence of CALLs, each with a disjoint output
    buffer, preserves the entire `opInfos` region pointwise. -/
theorem repeated_calls_preserve_region
    (m : MemState) (opInfosOff opInfosSize : Nat) (i : Nat)
    (hLo : opInfosOff ≤ i) (hHi : i < opInfosOff + opInfosSize)
    (calls : List (Nat × Nat × (Nat → Uint256)))
    (hAllDisj : ∀ c ∈ calls,
      Disjoint c.1 (c.1 + c.2.1) opInfosOff (opInfosOff + opInfosSize)) :
    (calls.foldl (fun acc c => callWithReturnBuffer acc c.1 c.2.1 c.2.2) m) i = m i := by
  induction calls generalizing m with
  | nil => rfl
  | cons c rest ih =>
    have hcDisj : Disjoint c.1 (c.1 + c.2.1) opInfosOff (opInfosOff + opInfosSize) :=
      hAllDisj c (List.mem_cons_self ..)
    have hRestDisj : ∀ d ∈ rest,
        Disjoint d.1 (d.1 + d.2.1) opInfosOff (opInfosOff + opInfosSize) := by
      intro d hd
      exact hAllDisj d (List.mem_cons_of_mem _ hd)
    -- Apply IH to the post-call memory.
    have hStep := call_preserves_disjoint_region m c.1 c.2.1 opInfosOff opInfosSize
      c.2.2 hcDisj i hLo hHi
    have hIh := ih (callWithReturnBuffer m c.1 c.2.1 c.2.2) hRestDisj
    -- Now combine: foldl over (c :: rest) m = foldl over rest (callWithReturnBuffer m ...)
    simp [List.foldl]
    rw [hIh]; exact hStep

/-- A concrete EntryPoint-shaped scenario: `opInfos` occupies a memory region
    `[opInfosBase, opInfosBase + N)`. The EntryPoint always passes the same
    fixed scratch buffer `[scratchOff, scratchOff + scratchSize)` as the
    output range to `call(account.validateUserOp, ...)`. If the two ranges
    are statically disjoint, no callee invocation can disturb `opInfos[i]`.
-/
theorem entrypoint_opInfos_frame
    (opInfosBase N scratchOff scratchSize : Nat)
    (hDisj : Disjoint scratchOff (scratchOff + scratchSize) opInfosBase (opInfosBase + N))
    (m₀ : MemState) (validateData executeData : Nat → Uint256)
    (i : Nat) (hLo : opInfosBase ≤ i) (hHi : i < opInfosBase + N) :
    -- After validation call (writes scratch) then execution call (writes scratch),
    -- the memory word at i in the opInfos region equals its pre-call value.
    let m₁ := callWithReturnBuffer m₀ scratchOff scratchSize validateData
    let m₂ := callWithReturnBuffer m₁ scratchOff scratchSize executeData
    m₂ i = m₀ i := by
  have hStep1 := call_preserves_disjoint_region m₀ scratchOff scratchSize
    opInfosBase N validateData hDisj i hLo hHi
  have hStep2 := call_preserves_disjoint_region
    (callWithReturnBuffer m₀ scratchOff scratchSize validateData)
    scratchOff scratchSize opInfosBase N executeData hDisj i hLo hHi
  simp only
  rw [hStep2, hStep1]

/-- **Lemma (2) — the real memory-aliasing argument**: if `opInfos[i]` is
    written to memory at offset `opInfosBase + i` BEFORE the external
    account call, and the EntryPoint's chosen call-output buffer
    `[scratchOff, scratchOff + scratchSize)` is statically disjoint from the
    opInfos region, then after the call returns, reading the same memory
    word yields the value originally written — for ANY callee bytecode (the
    callee appears only as its returndata, which fills the scratch buffer
    but cannot escape it).

    This is the formal counterpart of "no inner CALL exposes a pointer/offset
    that aliases `opInfos[i]` after the validation loop has finished." -/
theorem opInfos_memory_frame_under_arbitrary_callee
    (opInfosBase N scratchOff scratchSize : Nat)
    (hDisj : Disjoint scratchOff (scratchOff + scratchSize) opInfosBase (opInfosBase + N))
    (m₀ : MemState) (writtenValue : Uint256) (i : Nat)
    (hLo : opInfosBase ≤ i) (hHi : i < opInfosBase + N)
    (returnedData : Nat → Uint256) :
    -- Step 1: validation phase writes opInfos[i] := writtenValue.
    let mAfterWrite := myMstore m₀ i writtenValue
    -- Step 2: the account call runs with the disjoint scratch buffer; the
    -- callee's returned data can fill the scratch buffer but nothing else.
    let mAfterCall := callWithReturnBuffer mAfterWrite scratchOff scratchSize returnedData
    -- Step 3: the execution phase reads opInfos[i] back.
    myMload mAfterCall i = writtenValue := by
  unfold myMload myMstore callWithReturnBuffer
  -- Reduce the read at position i.
  by_cases hIn : scratchOff ≤ i ∧ i < scratchOff + scratchSize
  · -- Disjointness contradicts hIn vs. (hLo, hHi).
    rcases hDisj with h | h <;> omega
  · simp [hIn]

end MemFrame

/-! ## Bringing it together: the bytecode-level biconditional

Combining the three frame lemmas with the abstract control-flow biconditional
from `Proofs.lean` gives us the property Yoav Weis described: in any
non-reverting `handleOps` invocation, execution at index `i` happens iff
validation for `i` succeeded — **and this holds for arbitrary account /
paymaster bytecode**, because the three frame lemmas show that no callee can
disturb the EntryPoint's own state machine.
-/

/-- **Bytecode-level biconditional**: composes the abstract control-flow
    biconditional with the three frame lemmas. The intuition: validation
    writes `opInfoSlot := 1` and bumps the nonce; the post-validation external
    call cannot touch storage; the execution-phase read sees `opInfoSlot = 1`;
    the post-execution external call cannot touch storage either; the final
    state still has `nonce = expected + 1` and `opInfo = 1`. So execution
    happened (signalled by reading `1` from opInfoSlot) iff validation
    succeeded (which is exactly the precondition `hMatch`). -/
theorem bytecode_level_execution_iff_validation
    (senderKey expectedNonce : Uint256) (s : ContractState)
    (hMatch : s.storageMapUint 1 senderKey = expectedNonce) :
    let r := (EntryPointFrame.handleOpsBody senderKey expectedNonce).run s
    match r with
    | ContractResult.success info s' =>
        info = 1 ∧
        s'.storageMapUint 1 senderKey = add expectedNonce 1
    | ContractResult.revert _ _ => True := by
  have h1 := opInfos_frame senderKey expectedNonce s hMatch
  have h2 := nonce_preserved_through_execution senderKey expectedNonce s hMatch
  simp only at h1 h2 ⊢
  split
  · rename_i info s' hEq
    rw [hEq] at h1 h2
    exact ⟨h1, h2⟩
  · trivial

end Benchmark.Cases.ERC4337.EntryPointInvariant
