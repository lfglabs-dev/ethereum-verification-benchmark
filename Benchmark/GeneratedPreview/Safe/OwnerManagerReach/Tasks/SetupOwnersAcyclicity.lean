import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256


/-
  Reference proofs for the Safe OwnerManager linked list invariants.

  This module contains only fully proven theorems (no placeholders).
  Incomplete proof stubs live in `OpenProofs.lean`.

  Structure:
    Part 0 — Shared utilities (word/address roundtrips, reachability combinators)
    Part 1 — addOwner (storageMap characterisation, inListReachable preservation)
    Part 2 — setupOwners (storageMap characterisation, all three invariants)
    Part 3 — removeOwner (storageMap / next characterisation helpers)
    Part 4 — swapOwner (storageMap / next characterisation helpers)
-/

/-! ═══════════════════════════════════════════════════════════════════
    Part 0: Shared utilities
    ═══════════════════════════════════════════════════════════════════ -/

@[simp] private theorem wordToAddress_addressToWord (a : Address) :
    wordToAddress (addressToWord a) = a := by
  simp [addressToWord, wordToAddress, Verity.Core.Address.ofNat, Verity.Core.Address.toNat,
    Verity.Core.Uint256.ofNat]
  ext
  change a.val % Verity.Core.Uint256.modulus % Verity.Core.Address.modulus = a.val
  simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS]
  have hlt : a.val < 2 ^ 160 := a.isLt
  omega

private theorem reachable_self (s : ContractState) (a : Address) :
    reachable s a a :=
  ⟨[a], rfl, rfl, trivial⟩

private theorem reachable_step (s : ContractState) (a b : Address) (h : next s a = b) :
    reachable s a b :=
  ⟨[a, b], rfl, rfl, h, trivial⟩

private theorem reachable_prepend (s : ContractState) (a b c : Address)
    (hab : next s a = b) (hbc : reachable s b c) :
    reachable s a c := by
  obtain ⟨chain, hHead, hLast, hValid⟩ := hbc
  cases chain with
  | nil => simp at hHead
  | cons d rest =>
    simp at hHead; subst hHead
    exact ⟨a :: d :: rest, rfl, hLast, hab, hValid⟩

private theorem ne_of_bne {a b : Address} (h : (a != b) = true) : a ≠ b := by
  intro hab; subst hab; simp at h

private theorem ne_sentinel_of_bne (a : Address) (h : (a != SENTINEL) = true) :
    a ≠ Verity.Core.Address.ofNat 1 := by
  intro heq
  have : a = SENTINEL := by simp [SENTINEL]; exact heq
  simp [this] at h

-- Chain lifting: if chain avoids two addresses whose next pointers are the only ones changed.
private theorem isChain_lift_generic
    (s s' : ContractState)
    (avoid1 avoid2 : Address)
    (hNextEq : ∀ k : Address, k ≠ avoid1 → k ≠ avoid2 → next s' k = next s k)
    (chain : List Address)
    (hValid : isChain s chain)
    (hNo1 : ∀ a ∈ chain, a ≠ avoid1)
    (hNo2 : ∀ a ∈ chain, a ≠ avoid2) :
    isChain s' chain := by
  induction chain with
  | nil => exact trivial
  | cons hd tl ih =>
    match tl, hValid with
    | [], _ => exact trivial
    | b :: rest, hValid =>
      constructor
      · rw [hNextEq hd (hNo1 hd (by simp)) (hNo2 hd (by simp))]; exact hValid.1
      · exact ih hValid.2
          (fun x hx => hNo1 x (List.mem_cons_of_mem hd hx))
          (fun x hx => hNo2 x (List.mem_cons_of_mem hd hx))

-- Chain lifting with three avoided addresses.
private theorem isChain_lift_generic3
    (s s' : ContractState)
    (avoid1 avoid2 avoid3 : Address)
    (hNextEq : ∀ k : Address, k ≠ avoid1 → k ≠ avoid2 → k ≠ avoid3 → next s' k = next s k)
    (chain : List Address)
    (hValid : isChain s chain)
    (hNo1 : ∀ a ∈ chain, a ≠ avoid1)
    (hNo2 : ∀ a ∈ chain, a ≠ avoid2)
    (hNo3 : ∀ a ∈ chain, a ≠ avoid3) :
    isChain s' chain := by
  induction chain with
  | nil => exact trivial
  | cons hd tl ih =>
    match tl, hValid with
    | [], _ => exact trivial
    | b :: rest, hValid =>
      constructor
      · rw [hNextEq hd (hNo1 hd (by simp)) (hNo2 hd (by simp)) (hNo3 hd (by simp))]
        exact hValid.1
      · exact ih hValid.2
          (fun x hx => hNo1 x (List.mem_cons_of_mem hd hx))
          (fun x hx => hNo2 x (List.mem_cons_of_mem hd hx))
          (fun x hx => hNo3 x (List.mem_cons_of_mem hd hx))

-- Helpers for noDuplicates
private theorem noDuplicates_cons {a : Address} {l : List Address}
    (h : noDuplicates (a :: l)) : a ∉ l ∧ noDuplicates l := h

private theorem noDuplicates_tail {a : Address} {l : List Address}
    (h : noDuplicates (a :: l)) : noDuplicates l := h.2


/-! ═══════════════════════════════════════════════════════════════════
    Part 1: addOwner — storageMap, next_eq, proofs
    ═══════════════════════════════════════════════════════════════════ -/

set_option maxHeartbeats 6400000 in
private theorem addOwner_storageMap
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (sl : Nat) (addr : Address) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    s'.storageMap sl addr =
      if sl = 0 ∧ addr = SENTINEL then addressToWord owner
      else if sl = 0 ∧ addr = owner then addressToWord (wordToAddress (s.storageMap 0 SENTINEL))
      else s.storageMap sl addr := by
  have hNZ : owner ≠ (0 : Address) := ne_of_bne hNotZero
  have hNS_ofNat : owner ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne owner hNotSentinel
  have hFr_ofNat : Verity.Core.Address.ofNat (s.storageMap 0 owner).val = (0 : Address) := by
    have := hFresh; simp [BEq.beq, wordToAddress, zeroAddress] at this; exact this
  simp [OwnerManager.addOwner, OwnerManager.owners, OwnerManager.sentinel,
    OwnerManager.ownerCount, SENTINEL,
    Contract.run, ContractResult.snd, Verity.require, Verity.bind, Bind.bind,
    getMappingAddr, setMappingAddr, setMapping,
    getStorage, setStorage,
    hNZ, hNS_ofNat, hFr_ofNat]
  rfl

private theorem addOwner_next_eq
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (k : Address) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    next s' k =
      if k = SENTINEL then owner
      else if k = owner then next s SENTINEL
      else next s k := by
  simp only [next]
  rw [addOwner_storageMap owner s hNotZero hNotSentinel hFresh 0 k]
  simp only [true_and]
  split
  · exact wordToAddress_addressToWord owner
  · split
    · -- k = owner: goal is wordToAddress (addressToWord (wordToAddress (s.storageMap 0 SENTINEL))) = ...
      -- need wordToAddress_addressToWord applied to (wordToAddress (s.storageMap 0 SENTINEL))
      exact wordToAddress_addressToWord (wordToAddress (s.storageMap 0 SENTINEL))
    · rfl

/-! ## addOwner: inListReachable preservation -/

/--
  Legacy addOwner inListReachable proof.

  Note: this version uses raw acyclicity/freshness hypotheses that do NOT
  require `noDuplicates` on the witness chain. The `acyclic`/`freshInList`
  definitions in Specs.lean add a `noDuplicates` guard; this theorem uses
  the strictly stronger (non-guarded) form so the proof is self-contained.
-/
private theorem in_list_reachable
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreReach : ∀ key : Address, next s key ≠ zeroAddress → reachable s SENTINEL key)
    -- Raw acyclicity: SENTINEL ∉ any chain from next s SENTINEL.
    -- Strictly stronger than `acyclic s` (no noDuplicates guard).
    (hAcyclic : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      SENTINEL ∉ chain)
    -- Raw freshness: owner ∉ any chain from next s SENTINEL.
    -- Strictly stronger than `freshInList s owner` (no noDuplicates guard).
    (hOwnerFresh : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      owner ∉ chain) :
    in_list_reachable_spec s ((OwnerManager.addOwner owner).run s).snd := by
  let s' := ((OwnerManager.addOwner owner).run s).snd
  have hNextEq := addOwner_next_eq owner s hNotZero hNotSentinel hFresh
  have hSent : next s' SENTINEL = owner := by rw [hNextEq]; simp
  have hOwnerNZ : owner ≠ zeroAddress := ne_of_bne hNotZero
  have hOwnerNS : owner ≠ SENTINEL := ne_of_bne hNotSentinel
  unfold in_list_reachable_spec
  constructor
  · rw [hSent]; exact hOwnerNZ
  · intro key hKeyNZ
    by_cases hKeySent : key = SENTINEL
    · subst hKeySent; exact reachable_self s' SENTINEL
    · by_cases hKeyOwner : key = owner
      · subst hKeyOwner; exact reachable_step s' SENTINEL key hSent
      · have hNextK : next s' key = next s key := by rw [hNextEq]; simp [hKeySent, hKeyOwner]
        have hPreNZ : next s key ≠ zeroAddress := by rwa [hNextK] at hKeyNZ
        -- Get a witness chain from SENTINEL to key in the pre-state.
        obtain ⟨chain, hHead, hLast, hValid⟩ := hPreReach key hPreNZ
        match chain, hHead, hLast, hValid with
        | [], h, _, _ => simp at h
        | [a], h, hL, _ =>
          simp at h hL; subst h; subst hL; exact absurd rfl hKeySent
        | a :: b :: rest, h, hL, hV =>
          simp at h; subst h
          have hNextSent : next s SENTINEL = b := hV.1
          have hRestValid : isChain s (b :: rest) := hV.2
          -- owner ∉ (b :: rest) by raw freshness
          have hOwnerNotIn : owner ∉ (b :: rest) := by
            have hHead' : (b :: rest).head? = some (next s SENTINEL) := by simp [hNextSent]
            exact hOwnerFresh key (b :: rest) hHead' hL hRestValid
          -- SENTINEL ∉ (b :: rest) by raw acyclicity
          have hSentNotIn : SENTINEL ∉ (b :: rest) := by
            have hHead' : (b :: rest).head? = some (next s SENTINEL) := by simp [hNextSent]
            exact hAcyclic key (b :: rest) hHead' hL hRestValid
          -- In the post-state, for elements not in {SENTINEL, owner}, next is unchanged.
          -- So (b :: rest) is still a valid chain in s' (since owner and SENTINEL are not in it).
          have hRestValid' : isChain s' (b :: rest) := by
            apply isChain_lift_generic s s' SENTINEL owner
              (fun k hkS hkO => by rw [hNextEq]; simp [hkS, hkO])
              (b :: rest) hRestValid
              (fun a ha => Ne.symm (fun h => hSentNotIn (h ▸ ha)))
              (fun a ha => Ne.symm (fun h => hOwnerNotIn (h ▸ ha)))
          -- Build the post-state chain: SENTINEL :: owner :: b :: rest
          have hLast' : (SENTINEL :: owner :: b :: rest).getLast? = some key := by
            simp only [List.getLast?] at hL ⊢
            exact hL
          exact ⟨SENTINEL :: owner :: b :: rest, rfl, hLast',
                 hSent, by rw [hNextEq]; simp [hOwnerNS]; exact hNextSent, hRestValid'⟩

/-! ## addOwner: acyclicity preservation -/

private theorem addOwner_acyclicity
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true) :
    acyclic ((OwnerManager.addOwner owner).run s).snd := by
  let s' := ((OwnerManager.addOwner owner).run s).snd
  have hNextEq := addOwner_next_eq owner s hNotZero hNotSentinel hFresh
  have hSent : next s' SENTINEL = owner := by rw [hNextEq]; simp
  have hOwnerNext : next s' owner = next s SENTINEL := by
    rw [hNextEq]; simp [ne_of_bne hNotSentinel]
  have hOwnerNS : owner ≠ SENTINEL := ne_of_bne hNotSentinel
  -- Helper: in any isChain s' where SENTINEL ∈ l and owner ∉ l,
  -- SENTINEL must be the last element (because next s' SENTINEL = owner).
  have hSentIsLast : ∀ (l : List Address), isChain s' l →
      SENTINEL ∈ l → owner ∉ l → l.getLast? = some SENTINEL := by
    intro l hChV hSIn hONotIn
    induction l with
    | nil => simp at hSIn
    | cons hd tl ih =>
      match tl, hChV with
      | [], _ => simp at hSIn; simp [List.getLast?, hSIn]
      | c :: rest', hChV =>
        rcases List.mem_cons.mp hSIn with rfl | hSTl
        · -- hd = SENTINEL, so next s' SENTINEL = c, i.e. c = owner
          exfalso; apply hONotIn
          have hc : c = owner := by have := hChV.1; rw [hSent] at this; exact this.symm
          subst hc; exact List.mem_cons_of_mem _ (List.Mem.head rest')
        · -- SENTINEL ∈ (c :: rest')
          simp only [List.getLast?]
          exact ih hChV.2 hSTl (fun hO => hONotIn (List.mem_cons_of_mem _ hO))
  -- Main acyclicity proof
  unfold acyclic
  intro k hkNS ch hHead hLast hValid hNoDup hSentMem
  rw [hSent] at hHead
  match ch, hHead, hLast, hValid, hNoDup, hSentMem with
  | [a], hH, _, _, _, hSM =>
    simp at hH hSM; exact hOwnerNS (hH ▸ hSM).symm
  | a :: b :: rest, hH, hL, hV, hND, hSM =>
    simp at hH
    -- hH : a = owner. Use rw to avoid subst renaming.
    rw [hH] at hV hND hSM hL
    have hOwnerNotInTail : owner ∉ (b :: rest) := hND.1
    rcases List.mem_cons.mp hSM with rfl | hSentInTail
    · exact hOwnerNS rfl
    · have hTailLast := hSentIsLast (b :: rest) hV.2 hSentInTail hOwnerNotInTail
      have hL' : (b :: rest).getLast? = some k := by
        simp only [List.getLast?] at hL ⊢; exact hL
      rw [hTailLast] at hL'
      exact hkNS (Option.some.inj hL').symm

/-! ═══════════════════════════════════════════════════════════════════
    Part 2: setupOwners — storageMap, next_eq, proofs
    ═══════════════════════════════════════════════════════════════════ -/

-- setupOwners writes 4 mapping entries and 1 storage entry.
-- We characterize only the mapping (slot 0) since that's what next uses.
-- Phase 1: characterize the raw storageMap (Uint256) value.
set_option maxHeartbeats 12800000 in
private theorem setupOwners_storageMap_raw
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (sl : Nat) (addr : Address) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    s'.storageMap sl addr =
      if sl = 0 ∧ addr = owner3 then addressToWord SENTINEL
      else if sl = 0 ∧ addr = owner2 then addressToWord owner3
      else if sl = 0 ∧ addr = owner1 then addressToWord owner2
      else if sl = 0 ∧ addr = SENTINEL then addressToWord owner1
      else s.storageMap sl addr := by
  have hNZ1 : owner1 ≠ (0 : Address) := ne_of_bne h1NZ
  have hNS1 : owner1 ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne owner1 h1NS
  have hNZ2 : owner2 ≠ (0 : Address) := ne_of_bne h2NZ
  have hNS2 : owner2 ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne owner2 h2NS
  have hNZ3 : owner3 ≠ (0 : Address) := ne_of_bne h3NZ
  have hNS3 : owner3 ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne owner3 h3NS
  have hNE12 : owner1 ≠ owner2 := ne_of_bne h12
  have hNE13 : owner1 ≠ owner3 := ne_of_bne h13
  have hNE23 : owner2 ≠ owner3 := ne_of_bne h23
  simp [OwnerManager.setupOwners, OwnerManager.owners, OwnerManager.sentinel,
    OwnerManager.ownerCount, SENTINEL,
    Contract.run, ContractResult.snd, Verity.require, Verity.bind, Bind.bind,
    setMappingAddr, setMapping, setStorage,
    hNZ1, hNS1, hNZ2, hNS2, hNZ3, hNS3, hNE12, hNE13, hNE23]
  rfl

-- Phase 2: derive next characterization from storageMap characterization.
private theorem setupOwners_storageMap
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (addr : Address) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    next s' addr =
      if addr = SENTINEL then owner1
      else if addr = owner1 then owner2
      else if addr = owner2 then owner3
      else if addr = owner3 then SENTINEL
      else next s addr := by
  have hNS1 : owner1 ≠ SENTINEL := ne_of_bne h1NS
  have hNS2 : owner2 ≠ SENTINEL := ne_of_bne h2NS
  have hNS3 : owner3 ≠ SENTINEL := ne_of_bne h3NS
  have hNE12 : owner1 ≠ owner2 := ne_of_bne h12
  have hNE13 : owner1 ≠ owner3 := ne_of_bne h13
  have hNE23 : owner2 ≠ owner3 := ne_of_bne h23
  simp only [next]
  rw [setupOwners_storageMap_raw owner1 owner2 owner3 s h1NZ h1NS h2NZ h2NS h3NZ h3NS h12 h13 h23 0 addr]
  simp only [true_and]
  -- The raw branches are: owner3, owner2, owner1, SENTINEL (reverse order).
  -- The target branches are: SENTINEL, owner1, owner2, owner3.
  -- We case-split on addr and resolve each if-then-else branch.
  by_cases hS : addr = SENTINEL
  · simp only [hS, Ne.symm hNS3, Ne.symm hNS2, Ne.symm hNS1, ite_false, ite_true]
    exact wordToAddress_addressToWord owner1
  · by_cases h1 : addr = owner1
    · simp only [h1, hNE13, hNE12, hNS1, ite_false, ite_true]
      exact wordToAddress_addressToWord owner2
    · by_cases h2 : addr = owner2
      · simp only [h2, hNE23, Ne.symm hNE12, hNS2, ite_false, ite_true]
        exact wordToAddress_addressToWord owner3
      · by_cases h3 : addr = owner3
        · simp only [h3, Ne.symm hNE13, Ne.symm hNE23, hNS3, ite_true, ite_false]
          exact wordToAddress_addressToWord SENTINEL
        · simp only [hS, h1, h2, h3, ite_false]

/-! ## setupOwners_inListReachable -/

private theorem setupOwners_inListReachable
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (hClean : ∀ addr : Address, s.storageMap 0 addr = 0) :
    inListReachable ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd := by
  let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
  have hNxt := setupOwners_storageMap owner1 owner2 owner3 s h1NZ h1NS h2NZ h2NS h3NZ h3NS h12 h13 h23
  have hSent : next s' SENTINEL = owner1 := by rw [hNxt]; simp
  have hO1 : next s' owner1 = owner2 := by rw [hNxt]; simp [ne_of_bne h1NS]
  have hO2 : next s' owner2 = owner3 := by
    rw [hNxt]; simp [ne_of_bne h2NS, Ne.symm (ne_of_bne h12)]
  have hO3 : next s' owner3 = SENTINEL := by
    rw [hNxt]; simp [ne_of_bne h3NS, Ne.symm (ne_of_bne h13), Ne.symm (ne_of_bne h23)]
  unfold inListReachable
  constructor
  · rw [hSent]; exact ne_of_bne h1NZ
  · intro key hKeyNZ
    by_cases hk1 : key = SENTINEL
    · subst hk1; exact reachable_self s' SENTINEL
    · by_cases hk2 : key = owner1
      · subst hk2; exact reachable_step s' SENTINEL key hSent
      · by_cases hk3 : key = owner2
        · subst hk3
          exact reachable_prepend s' SENTINEL owner1 key hSent (reachable_step s' owner1 key hO1)
        · by_cases hk4 : key = owner3
          · subst hk4
            exact reachable_prepend s' SENTINEL owner1 key hSent
              (reachable_prepend s' owner1 owner2 key hO1 (reachable_step s' owner2 key hO2))
          · exfalso; apply hKeyNZ
            have : next s' key = next s key := by rw [hNxt]; simp [hk1, hk2, hk3, hk4]
            rw [this]; simp [next, hClean]

/-! ## setupOwners_acyclicity -/

/--
setupOwners establishes acyclicity of the owner linked list (base case).

The constructed list SENTINEL → o1 → o2 → o3 → SENTINEL has no internal
cycles because all three owners are distinct, non-zero, and non-sentinel.
SENTINEL appears only as the list head and the terminal pointer
(o3 → SENTINEL), never in the interior of any chain starting from
SENTINEL's successor.
-/
theorem setupOwners_acyclicity
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (hClean : ∀ addr : Address, s.storageMap 0 addr = 0) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    acyclic s' := by
  show acyclic ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
  let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
  have hNxt := setupOwners_storageMap owner1 owner2 owner3 s h1NZ h1NS h2NZ h2NS h3NZ h3NS h12 h13 h23
  have hSent : next s' SENTINEL = owner1 := by rw [hNxt]; simp
  have hO1 : next s' owner1 = owner2 := by rw [hNxt]; simp [ne_of_bne h1NS]
  have hO2 : next s' owner2 = owner3 := by
    rw [hNxt]; simp [ne_of_bne h2NS, Ne.symm (ne_of_bne h12)]
  have hO3 : next s' owner3 = SENTINEL := by
    rw [hNxt]; simp [ne_of_bne h3NS, Ne.symm (ne_of_bne h13), Ne.symm (ne_of_bne h23)]
  have hNZ1 : owner1 ≠ zeroAddress := ne_of_bne h1NZ
  have hNS1 : owner1 ≠ SENTINEL := ne_of_bne h1NS
  have hNS2 : owner2 ≠ SENTINEL := ne_of_bne h2NS
  have hNS3 : owner3 ≠ SENTINEL := ne_of_bne h3NS
  have hNE12 : owner1 ≠ owner2 := ne_of_bne h12
  have hNE13 : owner1 ≠ owner3 := ne_of_bne h13
  have hNE23 : owner2 ≠ owner3 := ne_of_bne h23
  -- For any address not in {SENTINEL, o1, o2, o3}, next s' addr = next s addr
  -- and next s addr = wordToAddress 0 = zeroAddress (by hClean).
  have hOther : ∀ addr : Address, addr ≠ SENTINEL → addr ≠ owner1 → addr ≠ owner2 →
      addr ≠ owner3 → next s' addr = next s addr := by
    intro a h1 h2 h3 h4; rw [hNxt]; simp [h1, h2, h3, h4]
  have hOtherZero : ∀ addr : Address, addr ≠ SENTINEL → addr ≠ owner1 → addr ≠ owner2 →
      addr ≠ owner3 → next s addr = zeroAddress := by
    intro a _ _ _ _; simp [next, hClean]
  -- acyclic s': for any dup-free chain starting at owner1 (= next s' SENTINEL)
  -- ending at key ≠ SENTINEL, SENTINEL ∉ chain.
  -- The chain follows next pointers: o1 → o2 → o3 → SENTINEL.
  -- With noDuplicates, the chain is a strict prefix of [o1, o2, o3].
  -- (It can't include SENTINEL and continue because that would require
  -- revisiting o1, violating noDuplicates.)
  unfold acyclic
  intro key hKeyNS chain hHead hLast hValid hNoDup hSentIn
  rw [hSent] at hHead
  -- Prove by induction on the chain that SENTINEL cannot appear in it.
  -- The chain starts at owner1 and follows next pointers.
  -- Each element in the chain must be in {o1, o2, o3} or an "other" address.
  -- If an "other" address appears, next s' other = 0, so the chain cannot
  -- continue past it (the next element would need to be 0, then stuck at 0).
  -- Actually, isChain [a, b, ...] only requires next a = b; it doesn't
  -- require anything about b. So a chain could go o1 → o2 → someOther.
  -- But for SENTINEL to appear, we'd need it at some position.
  -- Let's trace: chain starts at o1. Possible dup-free chains:
  -- [o1]: no SENTINEL. [o1, o2]: no S. [o1, o2, o3]: no S.
  -- [o1, o2, o3, SENTINEL]: last = SENTINEL = key, but key ≠ SENTINEL. Contradiction.
  -- So SENTINEL can only appear as the 4th element, but then it's the last = key = SENTINEL.
  -- Any chain where S appears in the middle would need to continue to o1 (= next S),
  -- but o1 is already at position 0, violating noDuplicates.
  -- Therefore S ∉ chain for any valid dup-free chain ending at key ≠ S.
  -- Let's prove this by case analysis on the chain structure.
  match chain, hHead, hLast, hValid, hNoDup with
  | [a], hH, hL, _, _ =>
    simp at hH hL hSentIn
    -- hH : a = owner1, hL : a = key, hSentIn : SENTINEL = a
    -- So SENTINEL = owner1, contradicting hNS1
    exact hNS1 (hH ▸ hSentIn).symm
  | [a, b], hH, hL, hV, hND =>
    simp at hH; subst hH
    have hb : b = owner2 := by have h := hV.1; rw [hO1] at h; exact h.symm
    subst hb
    simp at hSentIn
    exact hSentIn.elim (Ne.symm hNS1) (Ne.symm hNS2)
  | [a, b, c], hH, hL, hV, hND =>
    simp at hH; subst hH
    have hb : b = owner2 := by have h := hV.1; rw [hO1] at h; exact h.symm
    subst hb
    have hc : c = owner3 := by have h := hV.2.1; rw [hO2] at h; exact h.symm
    subst hc
    simp at hSentIn
    rcases hSentIn with h | h | h
    · exact hNS1 h.symm
    · exact hNS2 h.symm
    · exact hNS3 h.symm
  | [a, b, c, d], hH, hL, hV, hND =>
    simp at hH
    -- hH : a = owner1. Use rw instead of subst to avoid renaming.
    rw [hH] at hV hSentIn hND hL
    have hb : b = owner2 := by have h := hV.1; rw [hO1] at h; exact h.symm
    subst hb
    have hc : c = owner3 := by have h := hV.2.1; rw [hO2] at h; exact h.symm
    subst hc
    have hd : d = SENTINEL := by have h := hV.2.2.1; rw [hO3] at h; exact h.symm
    subst hd
    -- hL : [owner1, owner2, owner3, SENTINEL].getLast? = some key
    -- getLast? of 4-element list = some (last element) = some SENTINEL
    simp [List.getLast?] at hL
    exact absurd hL.symm hKeyNS
  | a :: b :: c :: d :: e :: rest, hH, hL, hV, hND =>
    simp at hH
    rw [hH] at hV hSentIn hND hL
    have hb : b = owner2 := by have h := hV.1; rw [hO1] at h; exact h.symm
    subst hb
    have hc : c = owner3 := by have h := hV.2.1; rw [hO2] at h; exact h.symm
    subst hc
    have hd : d = SENTINEL := by have h := hV.2.2.1; rw [hO3] at h; exact h.symm
    subst hd
    have he : e = owner1 := by have h := hV.2.2.2.1; rw [hSent] at h; exact h.symm
    subst he
    -- noDuplicates (owner1 :: owner2 :: owner3 :: SENTINEL :: owner1 :: rest)
    -- owner1 ∉ (owner2 :: owner3 :: SENTINEL :: owner1 :: rest), but owner1 is at position 4
    exact hND.1 (by simp)

/-! ## setupOwners_ownerListInvariant -/


end Benchmark.Cases.Safe.OwnerManagerReach
