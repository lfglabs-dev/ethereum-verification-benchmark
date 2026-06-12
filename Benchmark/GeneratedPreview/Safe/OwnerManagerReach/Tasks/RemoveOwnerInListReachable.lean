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

private theorem setupOwners_acyclicity
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
    acyclic ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd := by
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

private theorem setupOwners_ownerListInvariant
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
    ownerListInvariant ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd := by
  let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
  have hNxt := setupOwners_storageMap owner1 owner2 owner3 s h1NZ h1NS h2NZ h2NS h3NZ h3NS h12 h13 h23
  have hSent : next s' SENTINEL = owner1 := by rw [hNxt]; simp
  have hO1 : next s' owner1 = owner2 := by rw [hNxt]; simp [ne_of_bne h1NS]
  have hO2 : next s' owner2 = owner3 := by
    rw [hNxt]; simp [ne_of_bne h2NS, Ne.symm (ne_of_bne h12)]
  have hO3 : next s' owner3 = SENTINEL := by
    rw [hNxt]; simp [ne_of_bne h3NS, Ne.symm (ne_of_bne h13), Ne.symm (ne_of_bne h23)]
  have hNZ1 : owner1 ≠ zeroAddress := ne_of_bne h1NZ
  have hNZ2 : owner2 ≠ zeroAddress := ne_of_bne h2NZ
  have hNZ3 : owner3 ≠ zeroAddress := ne_of_bne h3NZ
  have hNS1 : owner1 ≠ SENTINEL := ne_of_bne h1NS
  have hNS2 : owner2 ≠ SENTINEL := ne_of_bne h2NS
  have hNS3 : owner3 ≠ SENTINEL := ne_of_bne h3NS
  have hNE12 : owner1 ≠ owner2 := ne_of_bne h12
  have hNE13 : owner1 ≠ owner3 := ne_of_bne h13
  have hNE23 : owner2 ≠ owner3 := ne_of_bne h23
  unfold ownerListInvariant
  constructor
  · rw [hSent]; exact hNZ1
  · intro key hKeyNZ
    constructor
    · -- (→) next s' key ≠ 0 → reachable s' SENTINEL key
      intro hNxtNZ
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
            · exfalso; apply hNxtNZ
              have : next s' key = next s key := by rw [hNxt]; simp [hk1, hk2, hk3, hk4]
              rw [this]; simp [next, hClean]
    · -- (←) reachable s' SENTINEL key → next s' key ≠ 0
      intro ⟨chain, hHead, hLast, hValid⟩
      -- key ≠ 0, and we need next s' key ≠ 0.
      -- key must be one of {SENTINEL, o1, o2, o3} or an "other" address.
      -- For SENTINEL: excluded (key ≠ 0 but SENTINEL = 1 ≠ 0, and next s' SENTINEL = o1 ≠ 0) ✓
      -- For o1: next = o2 ≠ 0. For o2: next = o3 ≠ 0. For o3: next = SENTINEL = 1 ≠ 0.
      -- For other: next s' other = next s other = wordToAddress 0.
      --   wordToAddress 0 = Address.ofNat 0 = 0. So next = 0.
      --   But then key is reachable from SENTINEL. Let's check: is it?
      --   The only reachable keys are {SENTINEL, o1, o2, o3}, so "other" can't be reachable.
      --   But we have a chain witnessing it. We need to show no valid chain from SENTINEL
      --   reaches an "other" address. This follows because every chain from SENTINEL
      --   stays in {o1, o2, o3, SENTINEL} (next of any other address maps to itself or 0).
      by_cases hk1 : key = SENTINEL
      · subst hk1; rw [hSent]; exact hNZ1
      · by_cases hk2 : key = owner1
        · subst hk2; rw [hO1]; exact hNZ2
        · by_cases hk3 : key = owner2
          · subst hk3; rw [hO2]; exact hNZ3
          · by_cases hk4 : key = owner3
            · subst hk4; rw [hO3]; decide
            · -- key is "other": next s' key = 0. But key is reachable.
              -- We need to show this case is impossible.
              -- Prove: all elements in a valid chain from SENTINEL are in {S, o1, o2, o3}.
              -- Then key ∈ {S, o1, o2, o3}, contradicting hk1..hk4.
              exfalso
              -- Any chain starting at SENTINEL and following next pointers stays in {S, o1, o2, o3}.
              -- We prove: for any element x in a valid chain starting from SENTINEL,
              -- x ∈ {SENTINEL, o1, o2, o3} ∨ next s' x = zeroAddress.
              -- Then since the chain reaches key (last element), key ∈ {S, o1, o2, o3} or
              -- key has next = 0. But key ≠ S, o1, o2, o3, so next s' key = 0.
              -- But we already know next s' key ≠ 0 wouldn't be provable...
              -- Actually let's just show key must be in {S, o1, o2, o3}.
              -- The chain starts at SENTINEL. next SENTINEL = o1.
              -- next o1 = o2. next o2 = o3. next o3 = SENTINEL.
              -- next (other) = next s other = wordToAddress(storageMap 0 other) = wordToAddress 0.
              -- For the chain to continue past an "other", next other = 0 would need to be
              -- the next element. And next 0 = wordToAddress(storageMap 0 0) = wordToAddress 0 = 0.
              -- So from "other", the chain is stuck at 0 forever.
              -- This means any chain from SENTINEL can only reach {S, o1, o2, o3, 0, ...}.
              -- key ≠ 0 and key ≠ S, o1, o2, o3, so key is unreachable. Contradiction with the chain.
              --
              -- Formal approach: induction on chain length showing all elements ∈ {S,o1,o2,o3,0}.
              have hOtherNext : next s' key = zeroAddress := by
                have : next s' key = next s key := by rw [hNxt]; simp [hk1, hk2, hk3, hk4]
                rw [this]; simp [next, hClean]
              -- We prove by induction on the chain that the last element must be in {S,o1,o2,o3}
              -- or be zeroAddress (which contradicts key ≠ 0).
              -- Actually, we'll show: every element that appears at position > 0 in a chain
              -- starting at SENTINEL follows from next pointers, so it's in {o1,o2,o3,S,0}.
              -- The chain starts at SENTINEL by hHead.
              -- Claim: in any isChain starting at SENTINEL, all subsequent elements ∈ {o1,o2,o3,S,0}.
              -- Proof: next S = o1, next o1 = o2, next o2 = o3, next o3 = S.
              -- next 0 = wordToAddress(clean 0) = 0.
              -- next (other) = wordToAddress(clean other) = 0. So next of anything is in {o1,o2,o3,S,0}.
              -- So by induction, all chain elements after position 0 are in {o1,o2,o3,S,0}.
              -- Position 0 = SENTINEL. The last element = key ∉ {S,o1,o2,o3}, so key = 0.
              -- But key ≠ 0. Contradiction.
              -- We'll need a helper lemma for this induction. Let's inline it.
              suffices hSuff : ∀ ch : List Address, isChain s' ch →
                  (∀ x ∈ ch.tail, x = SENTINEL ∨ x = owner1 ∨ x = owner2 ∨ x = owner3 ∨ x = zeroAddress) by
                match chain, hHead, hLast, hValid with
                | [a], hH, hL, _ => simp at hH hL; subst hH; subst hL; exact hk1 rfl
                | a :: b :: rest, hH, hL, hV =>
                  simp at hH; subst hH
                  have := hSuff (SENTINEL :: b :: rest) hV
                  -- last element of chain = key, which is in chain.tail
                  -- chain.tail = b :: rest, last = key
                  have hKeyInTail : key ∈ (b :: rest) := by
                    have hL' : (b :: rest).getLast? = some key := hL
                    have : (b :: rest).getLast (by simp) = key := by
                      rw [← Option.some_inj]
                      rw [← List.getLast?_eq_getLast]
                      exact hL'
                    rw [← this]
                    exact List.getLast_mem _
                  have := this key hKeyInTail
                  rcases this with h | h | h | h | h
                  · exact hk1 h
                  · exact hk2 h
                  · exact hk3 h
                  · exact hk4 h
                  · exact hKeyNZ h
              -- Prove the sufficiency by induction on the chain
              intro ch hChV
              induction ch with
              | nil => intro x hx; simp [List.tail] at hx
              | cons hd tl ih =>
                intro x hx
                match tl, hChV with
                | [], _ => simp [List.tail] at hx
                | b :: rest, hChV =>
                  simp [List.tail] at hx
                  -- b = next s' hd, which is in {o1,o2,o3,S,0} (or hd itself maps somewhere)
                  have hb_eq : next s' hd = b := hChV.1
                  rcases hx with rfl | hxrest
                  · -- x = b, show b ∈ {S,o1,o2,o3,0}
                    by_cases hhdS : hd = SENTINEL
                    · rw [hhdS, hSent] at hb_eq; right; left; exact hb_eq.symm
                    · by_cases hhd1 : hd = owner1
                      · rw [hhd1, hO1] at hb_eq; right; right; left; exact hb_eq.symm
                      · by_cases hhd2 : hd = owner2
                        · rw [hhd2, hO2] at hb_eq; right; right; right; left; exact hb_eq.symm
                        · by_cases hhd3 : hd = owner3
                          · rw [hhd3, hO3] at hb_eq; left; exact hb_eq.symm
                          · have : next s' hd = next s hd := by rw [hNxt]; simp [hhdS, hhd1, hhd2, hhd3]
                            rw [this] at hb_eq
                            have : next s hd = zeroAddress := by simp [next, hClean]
                            rw [this] at hb_eq
                            right; right; right; right; exact hb_eq.symm
                  · -- x ∈ rest, use IH
                    exact ih hChV.2 x (by simp [List.tail]; exact hxrest)

/-! ═══════════════════════════════════════════════════════════════════
    Generic acyclicity helper
    ═══════════════════════════════════════════════════════════════════ -/

/-- In any dup-free isChain, if SENTINEL ∈ l and some address `a ∉ l`
    satisfies `next s SENTINEL = a`, then SENTINEL must be the last element.
    Reason: SENTINEL at a non-last position is followed by `next s SENTINEL = a`,
    but a ∉ l gives a contradiction. -/
private theorem sentinel_last_if_succ_absent
    (s : ContractState) (l : List Address) (a : Address)
    (ha_eq : next s SENTINEL = a)
    (hValid : isChain s l)
    (hSentIn : SENTINEL ∈ l)
    (hANotIn : a ∉ l) :
    l.getLast? = some SENTINEL := by
  induction l with
  | nil => simp at hSentIn
  | cons hd tl ih =>
    match tl, hValid with
    | [], _ => simp at hSentIn; simp [List.getLast?, hSentIn]
    | c :: rest, hV =>
      rcases List.mem_cons.mp hSentIn with rfl | hSTl
      · -- hd = SENTINEL, so next s SENTINEL = c. ha_eq says next s SENTINEL = a, so c = a.
        exfalso
        have hc : c = a := by rw [← ha_eq]; exact hV.1.symm
        exact hANotIn (hc ▸ List.mem_cons_of_mem _ (List.Mem.head rest))
      · simp only [List.getLast?]
        exact ih hV.2 hSTl (fun h => hANotIn (List.mem_cons_of_mem _ h))

/-- Generic acyclicity: in any dup-free chain starting at `next s SENTINEL`
    ending at `key ≠ SENTINEL`, SENTINEL cannot appear. This is because
    SENTINEL at a non-last position forces `next s SENTINEL` (the head) to
    appear twice, and at the last position it contradicts `key ≠ SENTINEL`. -/
private theorem acyclic_generic
    (s : ContractState) (key : Address) (hKeyNS : key ≠ SENTINEL)
    (chain : List Address)
    (hHead : chain.head? = some (next s SENTINEL))
    (hLast : chain.getLast? = some key)
    (hValid : isChain s chain)
    (hNoDup : noDuplicates chain)
    (hSentMem : SENTINEL ∈ chain) :
    False := by
  match chain, hHead, hLast, hValid, hNoDup, hSentMem with
  | [a], _, hL, _, _, hSM =>
    simp at hSM hL; exact hKeyNS (hSM ▸ hL).symm
  | a :: b :: rest, hH, hL, hV, hND, hSM =>
    simp at hH
    -- a = next s SENTINEL. noDuplicates: a ∉ (b :: rest).
    have ha_not_in_tl : a ∉ (b :: rest) := hND.1
    rcases List.mem_cons.mp hSM with rfl | hSTl
    · -- a = SENTINEL. next s SENTINEL = b (hV.1). hH: a = next s SENTINEL, so SENTINEL = next s SENTINEL.
      -- Then b = next s SENTINEL = SENTINEL. But SENTINEL ∉ (b :: rest). Contradiction.
      have hb : b = next s SENTINEL := hV.1.symm
      rw [← hH] at hb
      exact ha_not_in_tl (hb ▸ List.Mem.head rest)
    · -- SENTINEL ∈ (b :: rest). Show SENTINEL is last element using sentinel_last_if_succ_absent.
      -- next s SENTINEL = a (from hH). a ∉ (b :: rest) (from hND.1).
      have hSentLast := sentinel_last_if_succ_absent s (b :: rest) a
        (hH ▸ rfl) hV.2 hSTl ha_not_in_tl
      have hL' : (b :: rest).getLast? = some key := by
        simp only [List.getLast?] at hL ⊢; exact hL
      rw [hSentLast] at hL'
      exact hKeyNS (Option.some.inj hL').symm

/-! ═══════════════════════════════════════════════════════════════════
    Part 3: removeOwner — storageMap, next_eq, acyclicity, inListReachable
    ═══════════════════════════════════════════════════════════════════ -/

set_option maxHeartbeats 6400000 in
private theorem removeOwner_storageMap_raw
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (sl : Nat) (addr : Address) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    s'.storageMap sl addr =
      if sl = 0 ∧ addr = owner then addressToWord zeroAddress
      else if sl = 0 ∧ addr = prevOwner then addressToWord (wordToAddress (s.storageMap 0 owner))
      else s.storageMap sl addr := by
  have hNZ : owner ≠ (0 : Address) := ne_of_bne hNotZero
  have hNS : owner ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne owner hNotSentinel
  have hPL : Verity.Core.Address.ofNat (s.storageMap 0 prevOwner).val = owner := by
    have := hPrevLink; simp [BEq.beq, wordToAddress] at this; exact this
  simp [OwnerManager.removeOwner, OwnerManager.owners, OwnerManager.sentinel,
    OwnerManager.ownerCount,
    Contract.run, ContractResult.snd, Verity.require, Verity.bind, Bind.bind,
    getMappingAddr, setMappingAddr, setMapping,
    getStorage, setStorage,
    hNZ, hNS, hPL]

private theorem removeOwner_storageMap
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (addr : Address) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    next s' addr =
      if addr = owner then zeroAddress
      else if addr = prevOwner then next s owner
      else next s addr := by
  simp only [next]
  rw [removeOwner_storageMap_raw prevOwner owner s hNotZero hNotSentinel hPrevLink 0 addr]
  simp only [true_and]
  by_cases h1 : addr = owner
  · subst h1
    simp only [ite_true]
    exact wordToAddress_addressToWord zeroAddress
  · simp only [h1, ite_false]
    by_cases h2 : addr = prevOwner
    · subst h2
      simp only [ite_true]
      exact wordToAddress_addressToWord (wordToAddress (s.storageMap 0 owner))
    · simp only [h2, ite_false]

/-! ## removeOwner: acyclicity preservation -/

private theorem removeOwner_acyclicity
    (prevOwner owner : Address) (s : ContractState)
    (_hNotZero : (owner != zeroAddress) = true)
    (_hNotSentinel : (owner != SENTINEL) = true)
    (_hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (_hOwnerInList : next s owner ≠ zeroAddress) :
    acyclic ((OwnerManager.removeOwner prevOwner owner).run s).snd := by
  let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
  unfold acyclic
  intro key hKeyNS chain hHead hLast hValid hNoDup hSentMem
  exact acyclic_generic s' key hKeyNS chain hHead hLast hValid hNoDup hSentMem

/-! ═══════════════════════════════════════════════════════════════════
    Part 4: swapOwner — storageMap, next_eq (helpers for future proofs)
    ═══════════════════════════════════════════════════════════════════ -/

set_option maxHeartbeats 6400000 in
private theorem swapOwner_storageMap_raw
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (sl : Nat) (addr : Address) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    s'.storageMap sl addr =
      if sl = 0 ∧ addr = oldOwner then addressToWord zeroAddress
      else if sl = 0 ∧ addr = prevOwner then addressToWord newOwner
      else if sl = 0 ∧ addr = newOwner then addressToWord (wordToAddress (s.storageMap 0 oldOwner))
      else s.storageMap sl addr := by
  have hNZNew : newOwner ≠ (0 : Address) := ne_of_bne hNewNotZero
  have hNSNew : newOwner ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne newOwner hNewNotSentinel
  have hFrNew : Verity.Core.Address.ofNat (s.storageMap 0 newOwner).val = (0 : Address) := by
    have := hNewFresh; simp [BEq.beq, wordToAddress, zeroAddress] at this; exact this
  have hNZOld : oldOwner ≠ (0 : Address) := ne_of_bne hOldNotZero
  have hNSOld : oldOwner ≠ Verity.Core.Address.ofNat 1 := ne_sentinel_of_bne oldOwner hOldNotSentinel
  have hPL : Verity.Core.Address.ofNat (s.storageMap 0 prevOwner).val = oldOwner := by
    have := hPrevLink; simp [BEq.beq, wordToAddress] at this; exact this
  simp [OwnerManager.swapOwner, OwnerManager.owners, OwnerManager.sentinel,
    Contract.run, ContractResult.snd, Verity.require, Verity.bind, Bind.bind,
    getMappingAddr, setMappingAddr, setMapping,
    hNZNew, hNSNew, hFrNew, hNZOld, hNSOld, hPL]

private theorem swapOwner_storageMap
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (addr : Address) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    next s' addr =
      if addr = oldOwner then zeroAddress
      else if addr = prevOwner then newOwner
      else if addr = newOwner then next s oldOwner
      else next s addr := by
  simp only [next]
  rw [swapOwner_storageMap_raw prevOwner oldOwner newOwner s hNewNotZero hNewNotSentinel hNewFresh hOldNotZero hOldNotSentinel hPrevLink 0 addr]
  simp only [true_and]
  by_cases h1 : addr = oldOwner
  · subst h1
    simp only [ite_true]
    exact wordToAddress_addressToWord zeroAddress
  · simp only [h1, ite_false]
    by_cases h2 : addr = prevOwner
    · subst h2
      simp only [ite_true]
      exact wordToAddress_addressToWord newOwner
    · simp only [h2, ite_false]
      by_cases h3 : addr = newOwner
      · subst h3
        simp only [ite_true]
        exact wordToAddress_addressToWord (wordToAddress (s.storageMap 0 oldOwner))
      · simp only [h3, ite_false]

/-! ## swapOwner: acyclicity preservation -/

private theorem swapOwner_acyclicity
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (_hNewNotZero : (newOwner != zeroAddress) = true)
    (_hNewNotSentinel : (newOwner != SENTINEL) = true)
    (_hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (_hOldNotZero : (oldOwner != zeroAddress) = true)
    (_hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (_hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true) :
    acyclic ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd := by
  let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
  unfold acyclic
  intro key hKeyNS chain hHead hLast hValid hNoDup hSentMem
  exact acyclic_generic s' key hKeyNS chain hHead hLast hValid hNoDup hSentMem

/-! ═══════════════════════════════════════════════════════════════════
    Part 5: reachable_has_simple_witness — loop removal
    ═══════════════════════════════════════════════════════════════════ -/

-- Decidability of noDuplicates (Address has DecidableEq via deriving)
private def decidable_noDuplicates : (l : List Address) → Decidable (noDuplicates l)
  | [] => isTrue trivial
  | a :: rest =>
    match decidable_noDuplicates rest with
    | isFalse h => isFalse (fun ⟨_, hnd⟩ => h hnd)
    | isTrue hnd =>
      if hm : a ∈ rest then
        isFalse (fun ⟨hni, _⟩ => hni hm)
      else
        isTrue ⟨hm, hnd⟩

-- getLast? of (pfx ++ x :: sfx) = getLast? of (x :: sfx)
private theorem getLast?_append_cons (pfx : List Address) (x : Address) (sfx : List Address) :
    (pfx ++ x :: sfx).getLast? = (x :: sfx).getLast? := by
  rw [List.getLast?_append]; simp [List.getLast?_cons]

-- isChain tail extraction
private theorem isChain_cons_tail₂ (s : ContractState) (a : Address) (l : List Address)
    (hl : l ≠ []) (h : isChain s (a :: l)) : isChain s l := by
  match l, h with | _ :: _, h => exact h.2

-- isChain suffix extraction
private theorem isChain_suffix₂ (s : ContractState) (l₁ l₂ : List Address)
    (h : isChain s (l₁ ++ l₂)) (h₂ne : l₂ ≠ []) : isChain s l₂ := by
  induction l₁ with
  | nil => exact h
  | cons a l₁' ih =>
    exact ih (isChain_cons_tail₂ s a (l₁' ++ l₂)
      (by intro heq; exact h₂ne (List.append_eq_nil_iff.mp heq).2) h)

-- isChain prefix extraction
private theorem isChain_prefix₂ (s : ContractState) (l₁ l₂ : List Address)
    (h : isChain s (l₁ ++ l₂)) : isChain s l₁ := by
  induction l₁ with
  | nil => exact trivial
  | cons a l₁' ih =>
    cases l₁' with
    | nil => exact trivial
    | cons b rest => simp at h ⊢; exact ⟨h.1, ih h.2⟩

-- isChain overlap join
private theorem isChain_append_overlap₂ (s : ContractState)
    (l₁ : List Address) (x : Address) (l₂ : List Address)
    (h1 : isChain s (l₁ ++ [x])) (h2 : isChain s (x :: l₂)) :
    isChain s (l₁ ++ x :: l₂) := by
  induction l₁ with
  | nil => simp; exact h2
  | cons a l₁' ih =>
    cases l₁' with
    | nil => simp [isChain] at h1 ⊢; exact ⟨h1, h2⟩
    | cons b rest => simp at h1 ⊢; exact ⟨h1.1, ih h1.2⟩

-- First occurrence split
private theorem mem_split_first₂ (x : Address) (l : List Address) (hx : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ [x] ++ l₂ ∧ x ∉ l₁ := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    by_cases ha : a = x
    · subst ha; exact ⟨[], rest, by simp, fun h => nomatch h⟩
    · obtain ⟨l₁, l₂, heq, hni⟩ := ih (List.mem_of_ne_of_mem (Ne.symm ha) hx)
      refine ⟨a :: l₁, l₂, by simp [heq], ?_⟩
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | h
      · exact ha rfl
      · exact hni h

-- Loop removal preserves isChain
private theorem isChain_remove_loop₂ (s : ContractState)
    (l₁ : List Address) (x : Address) (l₂ l₃ : List Address)
    (h : isChain s (l₁ ++ [x] ++ l₂ ++ [x] ++ l₃)) :
    isChain s (l₁ ++ [x] ++ l₃) := by
  have h_prefix : isChain s (l₁ ++ [x]) :=
    isChain_prefix₂ s (l₁ ++ [x]) (l₂ ++ [x] ++ l₃)
      (by simp [List.append_assoc] at h ⊢; exact h)
  have h_x_l₃ : isChain s (x :: l₃) :=
    isChain_suffix₂ s (l₁ ++ [x] ++ l₂) (x :: l₃)
      (by simp [List.append_assoc] at h ⊢; exact h) (by simp)
  rw [show l₁ ++ [x] ++ l₃ = l₁ ++ (x :: l₃) by simp]
  exact isChain_append_overlap₂ s l₁ x l₃ h_prefix h_x_l₃

-- ¬noDuplicates implies duplicate split
private theorem not_noDuplicates_has_loop₂ (l : List Address) (h : ¬noDuplicates l) :
    ∃ (l₁ : List Address) (x : Address) (l₂ l₃ : List Address),
      l = l₁ ++ [x] ++ l₂ ++ [x] ++ l₃ := by
  induction l with
  | nil => exact absurd trivial h
  | cons a rest ih =>
    by_cases ha : a ∈ rest
    · obtain ⟨l₂, l₃, heq, _⟩ := mem_split_first₂ a rest ha
      exact ⟨[], a, l₂, l₃, by simp [heq]⟩
    · obtain ⟨l₁', x, l₂', l₃', heq'⟩ := ih (fun hnd => h ⟨ha, hnd⟩)
      exact ⟨a :: l₁', x, l₂', l₃', by simp [heq']⟩

-- Length strictly decreases after loop removal
private theorem length_remove_loop_lt₂
    (l₁ : List Address) (x : Address) (l₂ l₃ : List Address) :
    (l₁ ++ [x] ++ l₃).length < (l₁ ++ [x] ++ l₂ ++ [x] ++ l₃).length := by
  simp [List.length_append]; omega

-- Loop removal preserves head?
private theorem head?_remove_loop₂
    (l₁ : List Address) (x : Address) (l₂ l₃ : List Address) :
    (l₁ ++ [x] ++ l₃).head? = (l₁ ++ [x] ++ l₂ ++ [x] ++ l₃).head? := by
  cases l₁ with
  | nil => simp
  | cons c _ => simp

-- Loop removal preserves getLast?
private theorem getLast?_remove_loop₂
    (l₁ : List Address) (x : Address) (l₂ l₃ : List Address) :
    (l₁ ++ [x] ++ l₃).getLast? = (l₁ ++ [x] ++ l₂ ++ [x] ++ l₃).getLast? := by
  -- Use List.getLast?_append : (l ++ l').getLast? = l'.getLast?.or l.getLast?
  -- For non-empty l', (some v).or _ = some v, so (l ++ l').getLast? = l'.getLast?
  simp only [List.append_assoc, List.singleton_append]
  -- LHS: (l₁ ++ x :: l₃).getLast?  RHS: (l₁ ++ x :: (l₂ ++ x :: l₃)).getLast?
  -- Both suffixes (x :: l₃) and (x :: (l₂ ++ x :: l₃)) are nonempty
  simp only [List.getLast?_append]
  -- Goal: (x :: l₃).getLast?.or l₁.getLast? = (x :: (l₂ ++ x :: l₃)).getLast?.or l₁.getLast?
  -- It suffices to show both getLast? values are the same `some`
  cases l₃ with
  | nil =>
    simp only [List.getLast?_singleton, Option.some_or]
  | cons c l₃' =>
    congr 1

/--
  Any reachability witness chain can be trimmed to a duplicate-free chain.
-/
private theorem reachable_has_simple_witness
    (s : ContractState) (a b : Address) (h : reachable s a b) :
    ∃ chain : List Address,
      chain.head? = some a ∧
      chain.getLast? = some b ∧
      isChain s chain ∧
      noDuplicates chain := by
  obtain ⟨chain, hHead, hLast, hValid⟩ := h
  suffices hsuff : ∀ (n : Nat) (ch : List Address),
      ch.length ≤ n →
      ch.head? = some a →
      ch.getLast? = some b →
      isChain s ch →
      ∃ ch' : List Address,
        ch'.head? = some a ∧
        ch'.getLast? = some b ∧
        isChain s ch' ∧
        noDuplicates ch' by
    exact hsuff chain.length chain (Nat.le_refl _) hHead hLast hValid
  intro n
  induction n with
  | zero =>
    intro ch hLen hHead' hLast' _
    simp [List.length_eq_zero_iff.mp (Nat.le_zero.mp hLen)] at hHead'
  | succ m ih =>
    intro ch hLen hHead' hLast' hValid'
    match decidable_noDuplicates ch with
    | isTrue hnd => exact ⟨ch, hHead', hLast', hValid', hnd⟩
    | isFalse hnd =>
      obtain ⟨l₁, x, l₂, l₃, hch_eq⟩ := not_noDuplicates_has_loop₂ ch hnd
      have hHead_ch' : (l₁ ++ [x] ++ l₃).head? = some a :=
        head?_remove_loop₂ l₁ x l₂ l₃ ▸ hch_eq ▸ hHead'
      have hLast_ch' : (l₁ ++ [x] ++ l₃).getLast? = some b :=
        getLast?_remove_loop₂ l₁ x l₂ l₃ ▸ hch_eq ▸ hLast'
      have hValid_ch' : isChain s (l₁ ++ [x] ++ l₃) :=
        isChain_remove_loop₂ s l₁ x l₂ l₃ (hch_eq ▸ hValid')
      have hLen_ch' : (l₁ ++ [x] ++ l₃).length ≤ m := by
        have : (l₁ ++ [x] ++ l₃).length < ch.length :=
          hch_eq ▸ length_remove_loop_lt₂ l₁ x l₂ l₃
        omega
      exact ih (l₁ ++ [x] ++ l₃) hLen_ch' hHead_ch' hLast_ch' hValid_ch'

/-! ═══════════════════════════════════════════════════════════════════
    Part 6: removeOwner — inListReachable preservation
    ═══════════════════════════════════════════════════════════════════ -/

-- Transitivity of reachability via induction on the first chain.
private theorem reachable_trans (s : ContractState) (a b c : Address)
    (hab : reachable s a b) (hbc : reachable s b c) :
    reachable s a c := by
  obtain ⟨ch1, hH1, hL1, hV1⟩ := hab
  induction ch1 generalizing a with
  | nil => simp at hH1
  | cons x tl ih =>
    simp at hH1; subst hH1
    match tl, hV1 with
    | [], _ =>
      simp at hL1; subst hL1; exact hbc
    | y :: rest, hVx =>
      have hL1' : (y :: rest).getLast? = some b := by
        cases rest with
        | nil => simp at hL1 ⊢; exact hL1
        | cons z zs => simp at hL1 ⊢; exact hL1
      exact reachable_prepend s x y c hVx.1
        (ih y rfl hL1' hVx.2)

-- Helper: l₁ ++ [x] ++ l₂ = l₁ ++ (x :: l₂)
private theorem append_singleton_append (l₁ : List Address) (x : Address) (l₂ : List Address) :
    l₁ ++ [x] ++ l₂ = l₁ ++ (x :: l₂) := by
  simp [List.append_assoc]

-- Lift a chain to post-removeOwner state when owner ∉ chain.
private theorem isChain_lift_removeOwner
    (prevOwner owner : Address) (s : ContractState)
    (hPrevLinkN : next s prevOwner = owner)
    (hNextEq : ∀ addr : Address,
      next ((OwnerManager.removeOwner prevOwner owner).run s).snd addr =
        if addr = owner then zeroAddress
        else if addr = prevOwner then next s owner
        else next s addr)
    (chain : List Address)
    (hValid : isChain s chain)
    (hOwnerNotIn : owner ∉ chain) :
    isChain ((OwnerManager.removeOwner prevOwner owner).run s).snd chain := by
  induction chain with
  | nil => exact trivial
  | cons hd tl ih =>
    match tl, hValid with
    | [], _ => exact trivial
    | b :: rest, hV =>
      have hHdNO : hd ≠ owner := fun h => hOwnerNotIn (h ▸ List.Mem.head _)
      have hTlNO : owner ∉ b :: rest := fun h => hOwnerNotIn (List.mem_cons_of_mem _ h)
      have hHdNP : hd ≠ prevOwner := by
        intro heq
        have hV1 := hV.1
        rw [heq, hPrevLinkN] at hV1
        exact hTlNO (hV1 ▸ List.Mem.head _)
      constructor
      · show next ((OwnerManager.removeOwner prevOwner owner).run s).snd hd = b
        rw [hNextEq]; simp [hHdNO, hHdNP]; exact hV.1
      · exact ih hV.2 hTlNO

-- Given a non-empty list and a valid chain prefix ++ [target], the last element of prefix
-- has next = target. (Moved here so it's available to owner_not_in_chain_to_prevOwner.)
private theorem last_step_of_prefix'
    (s' : ContractState) (a : Address) (l₁' : List Address) (target : Address)
    (hPref : isChain s' ((a :: l₁') ++ [target])) :
    next s' ((a :: l₁').getLast (by simp)) = target := by
  induction l₁' generalizing a with
  | nil =>
    simp at hPref ⊢; exact hPref.1
  | cons b rest ih =>
    simp only [List.cons_append] at hPref
    have : (a :: b :: rest).getLast (by simp) = (b :: rest).getLast (by simp) := by simp
    rw [this]
    exact ih b hPref.2

-- If noDuplicates (prefix ++ rest) and x ∈ prefix, then x ∉ rest.
-- (Each prefix element is absent from everything after it.)
private theorem noDup_prefix_elem_not_in_rest
    (pfx rest : List Address)
    (hND : noDuplicates (pfx ++ rest))
    (hIn : x ∈ pfx) :
    x ∉ rest := by
  induction pfx with
  | nil => nomatch hIn
  | cons a tl ih =>
    cases hIn with
    | head =>
      -- x = a; hND.1 : a ∉ tl ++ rest
      intro hm; exact hND.1 (List.mem_append_right _ hm)
    | tail _ hInTl =>
      exact ih hND.2 hInTl

-- owner ∉ any noDuplicates chain ending at prevOwner (when owner ≠ prevOwner),
-- because uniquePredecessor forces owner's predecessor to be prevOwner,
-- but prevOwner already appears at the end, violating noDuplicates.
private theorem owner_not_in_chain_to_prevOwner
    (s : ContractState) (prevOwner owner : Address) (chain : List Address)
    (hPrevLinkN : next s prevOwner = owner)
    (hUniquePred : uniquePredecessor s)
    (hHead : chain.head? = some SENTINEL)
    (hLast : chain.getLast? = some prevOwner)
    (hValid : isChain s chain)
    (hOwnerNePrev : owner ≠ prevOwner)
    (hND : noDuplicates chain)
    (hOwnerNZ : owner ≠ zeroAddress)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hOwnerNS : owner ≠ SENTINEL)
    (hZeroInert : next s zeroAddress = zeroAddress) :
    owner ∉ chain := by
  intro hOwnerIn
  obtain ⟨l₁, l₂, hSplit, _⟩ := mem_split_first₂ owner chain hOwnerIn
  rw [hSplit, append_singleton_append] at hValid hLast hND hHead
  match l₁, hHead, hValid with
  | [], hHd, _ =>
    simp at hHd; exact hOwnerNS hHd
  | a :: l₁', _, hV =>
    have hPfx : isChain s ((a :: l₁') ++ [owner]) :=
      isChain_prefix₂ s ((a :: l₁') ++ [owner]) l₂
        (by simp only [List.cons_append, List.append_assoc]; exact hV)
    have hLastPred := last_step_of_prefix' s a l₁' owner hPfx
    -- next s ((a :: l₁').getLast _) = owner and next s prevOwner = owner
    -- By uniquePredecessor: (a :: l₁').getLast _ = prevOwner
    have hPredNZ : (a :: l₁').getLast (by simp) ≠ zeroAddress := by
      intro h; rw [h, hZeroInert] at hLastPred; exact hOwnerNZ hLastPred.symm
    have hPredEqPrev : (a :: l₁').getLast (by simp) = prevOwner :=
      hUniquePred _ prevOwner owner hPredNZ hPrevNZ hOwnerNZ hLastPred hPrevLinkN
    have hPrevInPrefix : prevOwner ∈ a :: l₁' := by
      rw [← hPredEqPrev]; exact List.getLast_mem _
    -- prevOwner ∈ l₂ (from chain getLast? = some prevOwner)
    have hPrevInSuffix : prevOwner ∈ l₂ := by
      cases l₂ with
      | nil =>
        -- hLast : (a :: l₁' ++ [owner]).getLast? = some prevOwner
        -- getLast? of (... ++ [owner]) = some owner, so prevOwner = owner, contradiction
        have hLC : ((a :: l₁') ++ [owner]).getLast? = some owner := List.getLast?_concat
        have hLC' : (a :: l₁' ++ [owner]).getLast? = some owner := by
          rwa [List.cons_append] at hLC
        rw [hLC'] at hLast; exact absurd (Option.some.inj hLast) hOwnerNePrev
      | cons c rest =>
        -- (a :: l₁' ++ owner :: c :: rest).getLast? = (c :: rest).getLast?
        have hL : (c :: rest).getLast? = some prevOwner := by
          rw [show a :: l₁' ++ owner :: c :: rest =
              (a :: l₁') ++ (owner :: c :: rest) from rfl] at hLast
          rw [getLast?_append_cons (a :: l₁') owner (c :: rest)] at hLast
          simp at hLast; exact hLast
        have hmem := (c :: rest).getLast_mem (by simp)
        rw [show (c :: rest).getLast (by simp) = prevOwner from by
          rw [← Option.some_inj, ← List.getLast?_eq_getLast]; exact hL] at hmem
        exact hmem
    -- noDuplicates says prevOwner can't be in both prefix and suffix
    -- Inline proof: from noDuplicates (a :: l₁' ++ owner :: l₂) and prevOwner ∈ (a :: l₁'),
    -- derive prevOwner ∉ l₂ by induction on the prefix.
    have hPrevNotInSuffix : prevOwner ∉ l₂ := by
      -- noDuplicates (a :: l₁' ++ owner :: l₂) = noDuplicates ((a :: l₁') ++ (owner :: l₂))
      -- prevOwner ∈ (a :: l₁') implies prevOwner ∉ (owner :: l₂) implies prevOwner ∉ l₂
      have hNotInRest := noDup_prefix_elem_not_in_rest (a :: l₁') (owner :: l₂) hND hPrevInPrefix
      exact fun hm => hNotInRest (List.mem_cons_of_mem _ hm)
    exact absurd hPrevInSuffix hPrevNotInSuffix

-- Extract noDuplicates: owner ∉ suffix from noDuplicates (prefix ++ [owner] ++ suffix)
private theorem noDup_owner_not_in_suffix
    (owner : Address) (l₁ l₂ : List Address)
    (h : noDuplicates (l₁ ++ [owner] ++ l₂)) :
    owner ∉ l₂ := by
  rw [append_singleton_append] at h
  induction l₁ with
  | nil =>
    -- h : noDuplicates (owner :: l₂)
    cases l₂ with
    | nil => intro hm; nomatch hm
    | cons c rest => exact h.1
  | cons x xs ih =>
    -- h : noDuplicates (x :: (xs ++ owner :: l₂))
    -- xs ++ owner :: l₂ is always nonempty since owner :: l₂ is nonempty
    have hne : xs ++ (owner :: l₂) ≠ [] := by simp
    match hxs : xs ++ (owner :: l₂), hne, h with
    | _ :: _, _, h => exact ih h.2

-- prevOwner ∉ suffix after owner, given noDuplicates of the full chain and
-- prevOwner appearing in the prefix before owner.
private theorem prevOwner_not_in_suffix
    (_prevOwner _owner : Address) (l₁ suffix : List Address)
    (hND : noDuplicates (l₁ ++ [_owner] ++ suffix))
    (hPrevInL1 : _prevOwner ∈ l₁) :
    _prevOwner ∉ suffix := by
  rw [append_singleton_append] at hND
  induction l₁ with
  | nil => nomatch hPrevInL1
  | cons x xs ih =>
    cases hPrevInL1 with
    | head =>
      intro hPI
      exact hND.1 (List.mem_append_right _ (List.mem_cons_of_mem _ hPI))
    | tail _ hInXs =>
      exact ih hND.2 hInXs

-- Helper: the predecessor of owner in a chain is prevOwner (via uniquePredecessor).
-- Returns prevOwner ∈ l₁ for a chain l₁ ++ [owner] ++ suffix.
private theorem prevOwner_in_prefix
    (s : ContractState) (prevOwner owner : Address) (l₁ suffix : List Address)
    (hUniquePred : uniquePredecessor s)
    (hPrevLinkN : next s prevOwner = owner)
    (hValid : isChain s (l₁ ++ [owner] ++ suffix))
    (hOwnerNZ : owner ≠ zeroAddress)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hZeroInert : next s zeroAddress = zeroAddress)
    (hOwnerNS : owner ≠ SENTINEL)
    (hHead : (l₁ ++ [owner] ++ suffix).head? = some SENTINEL) :
    prevOwner ∈ l₁ := by
  match l₁, hHead with
  | [], hHd =>
    -- owner is at position 0, so owner = SENTINEL — contradiction
    simp at hHd; exact absurd hHd hOwnerNS
  | a :: l₁', _ =>
    have hPfx : isChain s ((a :: l₁') ++ [owner]) :=
      isChain_prefix₂ s ((a :: l₁') ++ [owner]) suffix
        (by simp only [List.cons_append, List.append_assoc] at hValid ⊢; exact hValid)
    have hPredNext := last_step_of_prefix' s a l₁' owner hPfx
    have hPredNZ : (a :: l₁').getLast (by simp) ≠ zeroAddress := by
      intro h; rw [h, hZeroInert] at hPredNext; exact hOwnerNZ hPredNext.symm
    have hPredEqPrev : (a :: l₁').getLast (by simp) = prevOwner :=
      hUniquePred _ prevOwner owner hPredNZ hPrevNZ hOwnerNZ hPredNext hPrevLinkN
    rw [← hPredEqPrev]; exact List.getLast_mem _

-- Split a chain at `owner`, extracting the suffix `c :: rest` and proving:
-- owner ∉ suffix, prevOwner ∈ prefix, prevOwner ∉ suffix, c = next s owner.
private theorem split_chain_at_owner
    (s : ContractState) (prevOwner owner key : Address)
    (chain : List Address)
    (hPrevLinkN : next s prevOwner = owner)
    (hUniquePred : uniquePredecessor s)
    (hOwnerNZ : owner ≠ zeroAddress)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hZeroInert : next s zeroAddress = zeroAddress)
    (hOwnerNS : owner ≠ SENTINEL)
    (hKeyNO : key ≠ owner)
    (hOC : owner ∈ chain)
    (hHead : chain.head? = some SENTINEL)
    (hLast : chain.getLast? = some key)
    (hValid : isChain s chain)
    (hND : noDuplicates chain) :
    ∃ l₁ c rest,
      chain = l₁ ++ owner :: c :: rest ∧
      c = next s owner ∧
      isChain s (owner :: c :: rest) ∧
      owner ∉ c :: rest ∧
      prevOwner ∈ l₁ ∧
      prevOwner ∉ c :: rest ∧
      noDuplicates (l₁ ++ owner :: c :: rest) ∧
      (c :: rest).getLast? = some key := by
  obtain ⟨l₁, l₂, hSp, _⟩ := mem_split_first₂ owner chain hOC
  have hHeadOrig : (l₁ ++ [owner] ++ l₂).head? = some SENTINEL := by
    rw [hSp] at hHead; exact hHead
  rw [hSp, append_singleton_append] at hValid hND hLast
  have hSuf : isChain s (owner :: l₂) :=
    isChain_suffix₂ s l₁ (owner :: l₂) hValid (by simp)
  have hl₂ne : l₂ ≠ [] := by
    intro hempty; rw [hempty] at hLast; simp at hLast; exact hKeyNO hLast.symm
  match l₂, hl₂ne, hSuf with
  | c :: rest, _, hSuf' =>
    have hceq : c = next s owner := hSuf'.1.symm
    have hONS : owner ∉ c :: rest := by
      rw [← append_singleton_append] at hND
      exact noDup_owner_not_in_suffix owner l₁ (c :: rest) hND
    have hValidAS : isChain s (l₁ ++ [owner] ++ (c :: rest)) := by
      rw [append_singleton_append]; exact hValid
    have hPrevInL1 : prevOwner ∈ l₁ :=
      prevOwner_in_prefix s prevOwner owner l₁ (c :: rest) hUniquePred hPrevLinkN
        hValidAS hOwnerNZ hPrevNZ hZeroInert hOwnerNS hHeadOrig
    have hPNS : prevOwner ∉ c :: rest := by
      rw [← append_singleton_append] at hND
      exact prevOwner_not_in_suffix prevOwner owner l₁ (c :: rest) hND hPrevInL1
    have hLS : (c :: rest).getLast? = some key := by simp at hLast ⊢; exact hLast
    exact ⟨l₁, c, rest, by rw [← append_singleton_append, ← hSp],
      hceq, hSuf', hONS, hPrevInL1, hPNS, hND, hLS⟩

-- Proof of removeOwner_inListReachable
/--
Certora `inListReachable` invariant preservation under `removeOwner`.

After removing `owner` by unlinking it from `prevOwner`, show that every
node with a non-zero successor in the post-state is still reachable from
SENTINEL.

Proof strategy: The removed owner's mapping becomes 0 so it no longer
triggers the invariant. prevOwner now points to owner's old successor,
so chains that went through owner can "skip" it: replace
[... → prevOwner → owner → X → ...] with [... → prevOwner → X → ...].
All other next pointers are unchanged.
-/
theorem removeOwner_inListReachable
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    -- The removed owner must have a non-zero successor (i.e. be in the list).
    (hOwnerInList : next s owner ≠ zeroAddress)
    -- Pre-state invariant
    (hPreInv : inListReachable s)
    -- Unique predecessor: each non-zero node has at most one non-zero predecessor.
    (hUniquePred : uniquePredecessor s)
    -- prevOwner is non-zero (a valid list node)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    -- Zero address maps to itself
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    inListReachable s' := by
  let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
  have hNextEq := removeOwner_storageMap prevOwner owner s hNotZero hNotSentinel hPrevLink
  have hOwnerNZ : owner ≠ zeroAddress := ne_of_bne hNotZero
  have hOwnerNS : owner ≠ SENTINEL := ne_of_bne hNotSentinel
  have hPrevLinkN : next s prevOwner = owner := by
    have := hPrevLink; simp [BEq.beq, wordToAddress, next] at this ⊢; exact this
  have hNextOwner' : next s' owner = zeroAddress := by
    show next ((OwnerManager.removeOwner prevOwner owner).run s).snd owner = zeroAddress
    rw [hNextEq]; simp
  have hNextOther : ∀ k : Address, k ≠ owner → k ≠ prevOwner → next s' k = next s k := by
    intro k hk1 hk2
    show next ((OwnerManager.removeOwner prevOwner owner).run s).snd k = next s k
    rw [hNextEq]; simp [hk1, hk2]
  unfold inListReachable
  constructor
  · -- SENTINEL has non-zero successor in s'
    by_cases hSO : SENTINEL = owner
    · exact absurd hSO.symm hOwnerNS
    · by_cases hSP : SENTINEL = prevOwner
      · show next ((OwnerManager.removeOwner prevOwner owner).run s).snd SENTINEL ≠ zeroAddress
        rw [hNextEq]; simp [hSO, hSP.symm]; exact hOwnerInList
      · rw [hNextOther SENTINEL hSO hSP]; exact hPreInv.1
  · intro key hKeyNZ
    have hKeyNO : key ≠ owner := by
      intro h; rw [h] at hKeyNZ; exact hKeyNZ hNextOwner'
    have hKeyPreNZ : next s key ≠ zeroAddress := by
      by_cases hkp : key = prevOwner
      · rw [hkp, hPrevLinkN]; exact hOwnerNZ
      · rw [← hNextOther key hKeyNO hkp]; exact hKeyNZ
    obtain ⟨chain, hHead, hLast, hValid, hND⟩ :=
      reachable_has_simple_witness s SENTINEL key (hPreInv.2 key hKeyPreNZ)
    by_cases hOC : owner ∈ chain
    · -- === owner ∈ chain (hard case) ===
      -- owner ≠ prevOwner: if equal, self-loop creates duplicate
      have hONP : owner ≠ prevOwner := by
        intro heq
        obtain ⟨l₁, l₂, hSp, _⟩ := mem_split_first₂ owner chain hOC
        rw [hSp, append_singleton_append] at hValid hND
        have hSuf : isChain s (owner :: l₂) :=
          isChain_suffix₂ s l₁ (owner :: l₂) hValid (by simp)
        have hl₂ne : l₂ ≠ [] := by
          intro hempty; rw [hSp, hempty] at hLast
          simp at hLast; exact hKeyNO hLast.symm
        match l₂, hl₂ne, hSuf with
        | c :: rest, _, hSV =>
          have hceq : c = owner := by
            have := hSV.1; rw [heq, hPrevLinkN] at this; exact this.symm
          have hONS : owner ∉ c :: rest := by
            rw [← append_singleton_append] at hND
            exact noDup_owner_not_in_suffix owner l₁ (c :: rest) hND
          exact hONS (hceq ▸ List.Mem.head _)
      -- Get chain from SENTINEL to prevOwner in s
      have hPNZ : next s prevOwner ≠ zeroAddress := by rw [hPrevLinkN]; exact hOwnerNZ
      obtain ⟨chP, hHP, hLP, hVP, hNDP⟩ :=
        reachable_has_simple_witness s SENTINEL prevOwner (hPreInv.2 prevOwner hPNZ)
      have hONP' : owner ∉ chP :=
        owner_not_in_chain_to_prevOwner s prevOwner owner chP hPrevLinkN
          hUniquePred hHP hLP hVP hONP hNDP hOwnerNZ hPrevNZ hOwnerNS hZeroInert
      have hVP' : isChain s' chP :=
        isChain_lift_removeOwner prevOwner owner s hPrevLinkN hNextEq chP hVP hONP'
      have hReachPrev : reachable s' SENTINEL prevOwner :=
        ⟨chP, hHP, hLP, hVP'⟩
      -- Split original chain at first occurrence of owner
      obtain ⟨l₁, c, rest, _, hceq, hSuf', hONS, _, hPNS, _, hLS⟩ :=
        split_chain_at_owner s prevOwner owner key chain hPrevLinkN hUniquePred
          hOwnerNZ hPrevNZ hZeroInert hOwnerNS hKeyNO hOC hHead hLast hValid hND
      -- Lift suffix to s'
      have hRV' : isChain s' (c :: rest) := by
        apply isChain_lift_generic s s' owner prevOwner
          (fun k hk1 hk2 => by
            show next ((OwnerManager.removeOwner prevOwner owner).run s).snd k = next s k
            rw [hNextEq]; simp [hk1, hk2])
          (c :: rest) hSuf'.2
          (fun a ha h => hONS (h ▸ ha))
          (fun a ha h => hPNS (h ▸ ha))
      have hStep : next s' prevOwner = c := by
        show next ((OwnerManager.removeOwner prevOwner owner).run s).snd prevOwner = c
        rw [hNextEq]; simp [Ne.symm hONP]; rw [hceq]
      have hReachSuffix : reachable s' prevOwner key :=
        reachable_prepend s' prevOwner c key hStep ⟨c :: rest, rfl, hLS, hRV'⟩
      exact reachable_trans s' SENTINEL prevOwner key hReachPrev hReachSuffix
    · -- === owner ∉ chain: lift directly ===
      exact ⟨chain, hHead, hLast,
        isChain_lift_removeOwner prevOwner owner s hPrevLinkN hNextEq chain hValid hOC⟩

/-! ═══════════════════════════════════════════════════════════════════
    Part 7: swapOwner — inListReachable preservation
    ═══════════════════════════════════════════════════════════════════ -/

-- Lift a chain to post-swapOwner state when oldOwner ∉ chain and newOwner ∉ chain.

end Benchmark.Cases.Safe.OwnerManagerReach
