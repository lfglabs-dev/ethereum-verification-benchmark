/-
  Benchmark.Grindset.Core — operational lemmas tagged for `grind`.

  The lemmas here are the stock facts needed to close a slot-write /
  spec-unfolding obligation in one line once the monadic scaffolding has been
  collapsed (see `Benchmark.Grindset.Monad`). They rewrite the shape

    { s with storage := fun k => if k == slot then v else s.storage k }.storage n

  into either `v` (when `n = slot`) or `s.storage n` (when `n ≠ slot`). The
  same pattern is covered for `storageMap`, `storageAddr`, and the mapping
  variants.

  Every lemma in this module carries both `@[simp]` and `@[grind_norm]`. A
  couple of fully-ground forms also carry `@[grind =]`.

  Status: zero `sorry`, zero new axioms.
-/

import Verity.Core
import Benchmark.Grindset.Monad

namespace Benchmark.Grindset

open Verity

/-! ## Uint256 slot storage -/

/-- Reading the slot just written returns the written value. -/
@[grind_norm, simp]
theorem storage_setStorage_eq
    (s : ContractState) (slot : Nat) (v : Uint256) :
    ({ s with
        storage := fun k => if k == slot then v else s.storage k } : ContractState).storage slot
      = v := by
  simp

/-- Reading a different slot from a `setStorage`-style update ignores the
    update. -/
@[grind_norm, simp]
theorem storage_setStorage_ne
    (s : ContractState) (slot n : Nat) (v : Uint256) (h : n ≠ slot) :
    ({ s with
        storage := fun k => if k == slot then v else s.storage k } : ContractState).storage n
      = s.storage n := by
  have : (n == slot) = false := by
    simpa [Nat.beq_eq_true_eq] using h
  simp [this]

/-! ## Address slot storage -/

@[grind_norm, simp]
theorem storageAddr_setStorageAddr_eq
    (s : ContractState) (slot : Nat) (v : Address) :
    ({ s with
        storageAddr := fun k => if k == slot then v else s.storageAddr k } : ContractState).storageAddr slot
      = v := by
  simp

@[grind_norm, simp]
theorem storageAddr_setStorageAddr_ne
    (s : ContractState) (slot n : Nat) (v : Address) (h : n ≠ slot) :
    ({ s with
        storageAddr := fun k => if k == slot then v else s.storageAddr k } : ContractState).storageAddr n
      = s.storageAddr n := by
  have : (n == slot) = false := by
    simpa [Nat.beq_eq_true_eq] using h
  simp [this]

/-! ## Mapping storage (Address → Uint256) -/

@[grind_norm, simp]
theorem storageMap_setMapping_eq
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    ({ s with
        storageMap := fun sl addr =>
          if sl == slot && addr == key then v else s.storageMap sl addr,
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storageMap slot key
      = v := by
  simp

/-- Writing `setMapping` at `(slot, key)` and reading the same slot at a
    different key yields the pre-state value at that key. -/
@[grind_norm, simp]
theorem storageMap_setMapping_ne_key
    (s : ContractState) (slot : Nat) (key key' : Address) (v : Uint256)
    (h : key' ≠ key) :
    ({ s with
        storageMap := fun sl addr =>
          if sl == slot && addr == key then v else s.storageMap sl addr,
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storageMap slot key'
      = s.storageMap slot key' := by
  have : (key' == key) = false := by
    simpa [beq_iff_eq] using h
  simp [this]

@[grind_norm, simp]
theorem storageMap_setMapping_ne_slot
    (s : ContractState) (slot n : Nat) (key key' : Address) (v : Uint256)
    (h : n ≠ slot) :
    ({ s with
        storageMap := fun sl addr =>
          if sl == slot && addr == key then v else s.storageMap sl addr,
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storageMap n key'
      = s.storageMap n key' := by
  have : (n == slot) = false := by
    simpa [Nat.beq_eq_true_eq] using h
  simp [this]

/-!
## Specialised helper for the "set-mapping-under-sender" pattern

Every bench task that uses a mapping keyed by `s.sender` reads back the
mapping at `s.sender` afterwards. This specialised rewrite collapses the
pattern in a single step. -/

@[grind_norm, simp]
theorem storageMap_setMapping_sender_eq
    (s : ContractState) (slot : Nat) (v : Uint256) :
    ({ s with
        storageMap := fun sl addr =>
          if sl == slot && addr == s.sender then v else s.storageMap sl addr,
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert s.sender
          else s.knownAddresses sl } : ContractState).storageMap slot s.sender
      = v := by
  simp

/-!
## `sender` is preserved by every primitive storage write.

These are implicit record-update facts, but tagging them means `simp` does
not have to fight the elaborator to see that the final state's `.sender`
field is still the original `.sender`. -/

@[grind_norm, simp]
theorem sender_after_setStorage
    (s : ContractState) (slot : Nat) (v : Uint256) :
    ({ s with
        storage := fun k => if k == slot then v else s.storage k } : ContractState).sender
      = s.sender := rfl

@[grind_norm, simp]
theorem sender_after_setMapping
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    ({ s with
        storageMap := fun sl addr =>
          if sl == slot && addr == key then v else s.storageMap sl addr,
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).sender
      = s.sender := rfl

@[grind_norm, simp]
theorem sender_after_setStorageAddr
    (s : ContractState) (slot : Nat) (v : Address) :
    ({ s with
        storageAddr := fun k => if k == slot then v else s.storageAddr k } : ContractState).sender
      = s.sender := rfl

/-!
## Cross-type preservation — reading `storage` after a mapping write, etc.

These are trivial by `rfl`, but they help `simp`/`grind` traverse
multi-write contracts without getting lost in record syntax. -/

@[grind_norm, simp]
theorem storage_after_setMapping
    (s : ContractState) (n slot : Nat) (key : Address) (v : Uint256) :
    ({ s with
        storageMap := fun sl addr =>
          if sl == slot && addr == key then v else s.storageMap sl addr,
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storage n
      = s.storage n := rfl

@[grind_norm, simp]
theorem storageMap_after_setStorage
    (s : ContractState) (slot n : Nat) (v : Uint256) (addr : Address) :
    ({ s with
        storage := fun k => if k == slot then v else s.storage k } : ContractState).storageMap n addr
      = s.storageMap n addr := rfl

/-! ## `require` reductions tied to a hypothesis -/

/-- When the condition of `require` is definitely `true`, the monadic step
    reduces to `pure ()`. Useful for branch-heavy contracts where the
    precondition fires a `require`. -/
@[grind_norm, simp]
theorem require_of_true_run (s : ContractState) (msg : String) :
    (require true msg).run s = ContractResult.success () s := rfl

@[grind_norm, simp]
theorem require_of_false_run (s : ContractState) (msg : String) :
    (require false msg).run s = ContractResult.revert msg s := rfl

/-!
## `StorageSlot` slot-projection equalities

The macro-generated storage field identifiers (e.g. `SideEntrance.poolBalance`)
are `StorageSlot`s whose `.slot` literal is the slot number. -/

@[grind_norm, simp]
theorem StorageSlot.slot_mk (n : Nat) :
    ({ slot := n } : StorageSlot Uint256).slot = n := rfl

end Benchmark.Grindset
