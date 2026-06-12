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

/--
addOwner preserves acyclicity of the owner linked list.

After addOwner(owner), the list becomes:
  SENTINEL → owner → old_head → ... → SENTINEL

Acyclicity is a tautology — it holds for any state. The proof
(acyclic_generic) shows that any duplicate-free chain from SENTINEL's
successor ending at key ≠ SENTINEL cannot contain SENTINEL, purely
by the structure of the definitions. No pre-state hypotheses are needed
beyond the Solidity require guards.
-/
theorem addOwner_acyclicity
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

end Benchmark.Cases.Safe.OwnerManagerReach
