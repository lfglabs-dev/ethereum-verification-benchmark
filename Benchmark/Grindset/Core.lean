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

/-! ## Record-update projection lemmas for `storageWords`-backed views

When a record update modifies non-storage fields such as `knownAddresses` (as in
`setMapping`) or `events` (as in `emitEvent`), Lean elaborates the update to
`ContractState.mk s.storageWords ...`. Because `storage`, `storageAddr`,
`storageMap`, `storageMapUint`, `storageMap2`, and `transientStorage` are
compatibility views over `storageWords` rather than raw structure fields, these
lemmas let `simp` and `grind` project straight through the non-storage update. -/

@[grind_norm, simp]
theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl

@[grind_norm, simp]
theorem storageAddr_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageAddr =
      s.storageAddr := rfl

@[grind_norm, simp]
theorem storageMap_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      s.storageMap := rfl

@[grind_norm, simp]
theorem storageMapUint_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapUint =
      s.storageMapUint := rfl

@[grind_norm, simp]
theorem storageMap2_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap2 =
      s.storageMap2 := rfl

@[grind_norm, simp]
theorem transientStorage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).transientStorage =
      s.transientStorage := rfl

@[grind_norm, simp]
theorem storageMapChain_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapChain =
      s.storageMapChain := rfl

@[grind_norm, simp]
theorem transientStorageMapChain_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).transientStorageMapChain =
      s.transientStorageMapChain := rfl

/-! ## Uint256 slot storage -/

/-- Reading the slot just written returns the written value. -/
@[grind_norm, simp]
theorem storage_setStorage_eq
    (s : ContractState) (slot : Nat) (v : Uint256) :
    (s.writeSlot slot v).storage slot = v := by
  simp

/-- Reading a different slot from a `setStorage`-style update ignores the
    update. -/
@[grind_norm, simp]
theorem storage_setStorage_ne
    (s : ContractState) (slot n : Nat) (v : Uint256) (h : n ≠ slot) :
    (s.writeSlot slot v).storage n = s.storage n := by
  simp [h]

/-! ## Address slot storage -/

@[grind_norm, simp]
theorem storageAddr_setStorageAddr_eq
    (s : ContractState) (slot : Nat) (v : Address) :
    (s.writeAddrSlot slot v).storageAddr slot = v := by
  simp

@[grind_norm, simp]
theorem storageAddr_setStorageAddr_ne
    (s : ContractState) (slot n : Nat) (v : Address) (h : n ≠ slot) :
    (s.writeAddrSlot slot v).storageAddr n = s.storageAddr n := by
  simp [h]

/-! ## Mapping storage (Address → Uint256) -/

@[grind_norm, simp]
theorem storageMap_writeMap_eq
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    (s.writeMap slot key v).storageMap slot key = v := by
  simp

@[grind_norm, simp]
theorem storageMap_writeMap_ne_key
    (s : ContractState) (slot : Nat) (key key' : Address) (v : Uint256)
    (h : key' ≠ key) :
    (s.writeMap slot key v).storageMap slot key' = s.storageMap slot key' := by
  simp [h]

@[grind_norm, simp]
theorem storageMap_writeMap_ne_slot
    (s : ContractState) (slot n : Nat) (key key' : Address) (v : Uint256)
    (h : n ≠ slot) :
    (s.writeMap slot key v).storageMap n key' = s.storageMap n key' := by
  simp [ContractState.storageMap, ContractState.writeMap, h]

@[grind_norm, simp]
theorem storageMap_setMapping_eq
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    ({ s.writeMap slot key v with
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
    ({ s.writeMap slot key v with
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storageMap slot key'
      = s.storageMap slot key' := by
  simp [h]

@[grind_norm, simp]
theorem storageMap_setMapping_ne_slot
    (s : ContractState) (slot n : Nat) (key key' : Address) (v : Uint256)
    (h : n ≠ slot) :
    ({ s.writeMap slot key v with
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storageMap n key'
      = s.storageMap n key' := by
  simp [h]

/-!
## Specialised helper for the "set-mapping-under-sender" pattern

Every bench task that uses a mapping keyed by `s.sender` reads back the
mapping at `s.sender` afterwards. This specialised rewrite collapses the
pattern in a single step. -/

@[grind_norm, simp]
theorem storageMap_setMapping_sender_eq
    (s : ContractState) (slot : Nat) (v : Uint256) :
    ({ s.writeMap slot s.sender v with
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
    (s.writeSlot slot v).sender = s.sender := rfl

@[grind_norm, simp]
theorem sender_after_setMapping
    (s : ContractState) (slot : Nat) (key : Address) (v : Uint256) :
    ({ s.writeMap slot key v with
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).sender
      = s.sender := rfl

@[grind_norm, simp]
theorem sender_after_setStorageAddr
    (s : ContractState) (slot : Nat) (v : Address) :
    (s.writeAddrSlot slot v).sender = s.sender := rfl

/-!
## Cross-type preservation — reading `storage` after a mapping write, etc.

These are trivial by `rfl`, but they help `simp`/`grind` traverse
multi-write contracts without getting lost in record syntax. -/

@[grind_norm, simp]
theorem storage_after_setMapping
    (s : ContractState) (n slot : Nat) (key : Address) (v : Uint256) :
    ({ s.writeMap slot key v with
        knownAddresses := fun sl =>
          if sl == slot then (s.knownAddresses sl).insert key
          else s.knownAddresses sl } : ContractState).storage n
      = s.storage n := by
  simp

@[grind_norm, simp]
theorem storageMap_after_setStorage
    (s : ContractState) (slot n : Nat) (v : Uint256) (addr : Address) :
    (s.writeSlot slot v).storageMap n addr = s.storageMap n addr := by
  simp

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


/-! ## Uint256-keyed mapping storage (`setMappingUint`, Verity #154)

Same read-after-write family as `storageMap`, for `Uint256 → Uint256`
mappings. The update shape mirrors `Verity.setMappingUint`. -/

@[grind_norm, simp]
theorem storageMapUint_setMappingUint_eq
    (s : ContractState) (slot : Nat) (key v : Uint256) :
    (s.writeMapUint slot key v).storageMapUint slot key = v := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint]

@[grind_norm, simp]
theorem storageMapUint_setMappingUint_ne_key
    (s : ContractState) (slot : Nat) (key key' v : Uint256)
    (h : key' ≠ key) :
    (s.writeMapUint slot key v).storageMapUint slot key'
      = s.storageMapUint slot key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint, h]

@[grind_norm, simp]
theorem storageMapUint_setMappingUint_ne_slot
    (s : ContractState) (slot n : Nat) (key key' v : Uint256)
    (h : n ≠ slot) :
    (s.writeMapUint slot key v).storageMapUint n key'
      = s.storageMapUint n key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint, h]

/-! ## Double-mapping storage (`setMapping2`, Verity #154) -/

@[grind_norm, simp]
theorem storageMap2_setMapping2_eq
    (s : ContractState) (slot : Nat) (key1 key2 : Address) (v : Uint256) :
    (s.writeMap2 slot key1 key2 v).storageMap2 slot key1 key2 = v := by
  simp

@[grind_norm, simp]
theorem storageMap2_setMapping2_ne_slot
    (s : ContractState) (slot n : Nat) (key1 key2 a1 a2 : Address) (v : Uint256)
    (h : n ≠ slot) :
    (s.writeMap2 slot key1 key2 v).storageMap2 n a1 a2
      = s.storageMap2 n a1 a2 := by
  simp [ContractState.storageMap2, ContractState.writeMap2, h]

@[grind_norm, simp]
theorem storageMap2_setMapping2_ne_key1
    (s : ContractState) (slot : Nat) (key1 key2 a1 a2 : Address) (v : Uint256)
    (h : a1 ≠ key1) :
    (s.writeMap2 slot key1 key2 v).storageMap2 slot a1 a2
      = s.storageMap2 slot a1 a2 := by
  simp [ContractState.storageMap2, ContractState.writeMap2, h]

@[grind_norm, simp]
theorem storageMap2_setMapping2_ne_key2
    (s : ContractState) (slot : Nat) (key1 key2 a1 a2 : Address) (v : Uint256)
    (h : a2 ≠ key2) :
    (s.writeMap2 slot key1 key2 v).storageMap2 slot a1 a2
      = s.storageMap2 slot a1 a2 := by
  simp [ContractState.storageMap2, ContractState.writeMap2, h]

/-! ## Cross-type preservation for the newer mapping families -/

@[grind_norm, simp]
theorem storage_after_setMappingUint
    (s : ContractState) (n slot : Nat) (key v : Uint256) :
    (s.writeMapUint slot key v).storage n = s.storage n := by
  simp

@[grind_norm, simp]
theorem storageMapUint_after_setStorage
    (s : ContractState) (slot n : Nat) (v key : Uint256) :
    (s.writeSlot slot v).storageMapUint n key = s.storageMapUint n key := by
  simp

@[grind_norm, simp]
theorem sender_after_setMappingUint
    (s : ContractState) (slot : Nat) (key v : Uint256) :
    (s.writeMapUint slot key v).sender = s.sender := rfl

attribute [grind_norm]
  ContractState.storage_writeSlot_same
  ContractState.storage_writeSlot_other
  ContractState.storageAddr_writeSlot
  ContractState.storageMap_writeSlot
  ContractState.storageMapUint_writeSlot
  ContractState.storageMap2_writeSlot
  ContractState.storageAddr_writeAddrSlot_same
  ContractState.storageAddr_writeAddrSlot_other
  ContractState.storage_writeAddrSlot
  ContractState.storageMap_writeAddrSlot
  ContractState.storageMapUint_writeAddrSlot
  ContractState.storageMap2_writeAddrSlot
  ContractState.storageMap_writeMap_same
  ContractState.storageMap_writeMap_other_key
  ContractState.storage_writeMap
  ContractState.storageAddr_writeMap
  ContractState.storageMapUint_writeMap
  ContractState.storageMap2_writeMap
  ContractState.storage_writeMapUint
  ContractState.storageAddr_writeMapUint
  ContractState.storageMap_writeMapUint
  ContractState.storageMap2_writeMapUint
  ContractState.storageMap2_writeMap2_same
  ContractState.storage_writeMap2
  ContractState.storageAddr_writeMap2
  ContractState.storageMap_writeMap2
  ContractState.storageMapUint_writeMap2

end Benchmark.Grindset
