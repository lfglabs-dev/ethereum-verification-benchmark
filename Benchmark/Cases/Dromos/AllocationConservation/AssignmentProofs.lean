import Benchmark.Cases.Dromos.AllocationConservation.SetProofs

/-!
Reference proof development for the Dromos Labs team's single selected invariant.
Concrete assignment, independent stored positions and finite-sum replacement
are mechanically checked against actual successful execution. No domain axiom
is declared or used. These are symbolic-model proofs, not source/bytecode
correspondence proofs.
The operational model and the original source correspondence remain separate.
-/
namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity
set_option maxHeartbeats 1000000

theorem initialized_set_representation {s : ContractState}
    (h : initializedLedger s) (t : Uint256) : setRepresentationValid s t := by
  obtain ⟨hi, _, _, hp⟩ := h t
  simp [setRepresentationValid, hi, hp, expectedPosition]

theorem initialized_ledger {s : ContractState}
    (h : initializedLedger s) : ledgerInvariant s := by
  intro t
  obtain ⟨hi, hc, ha, _⟩ := h t
  refine ⟨?_, ?_, ?_, initialized_set_representation h t⟩
  · simp [allocationConserved, allocationSum, hi, hc]
  · simp [supportValid, hi, ha]
  · intro c
    simp [ha, amountLimit]

theorem set_values_snapshot (s : ContractState) (t : Uint256) :
    (setValues t).run s = .success (allocationChainIds s t) s := rfl

-- Sum lemmas use arbitrary lists and non-modular Nat arithmetic.
def mass {α : Type} (f : α → Nat) (xs : List α) : Nat :=
  xs.foldr (fun x n => f x + n) 0

@[simp] theorem mass_nil {α : Type} (f : α → Nat) : mass f [] = 0 := rfl
@[simp] theorem mass_cons {α : Type} (f : α → Nat) (a : α) (xs : List α) :
    mass f (a :: xs) = f a + mass f xs := rfl

theorem mass_zero {α : Type} (f : α → Nat) (xs : List α)
    (hz : ∀ a ∈ xs, f a = 0) : mass f xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [mass_cons, hz a (by simp), Nat.zero_add]
    exact ih (fun b hb => hz b (by simp [hb]))

theorem mass_erase {α : Type} [BEq α] [LawfulBEq α]
    (f : α → Nat) (xs : List α) (a : α) (ha : a ∈ xs) :
    mass f xs = f a + mass f (xs.erase a) := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hab : b = a
    · subst b
      simp
    · have hax : a ∈ xs := by simpa [hab, Ne.symm hab] using ha
      rw [List.erase_cons_tail (by simpa using hab), mass_cons, mass_cons, ih hax]
      omega

-- Complete support is the bridge between a stored-set sum and all map slots.
-- The second enumeration is any duplicate-free finite covering list.
theorem mass_cover {α : Type} [BEq α] [LawfulBEq α]
    (f : α → Nat) (xs ys : List α) (hx : xs.Nodup) (hy : ys.Nodup)
    (hsub : ∀ a ∈ xs, a ∈ ys) (hz : ∀ a ∈ ys, a ∉ xs → f a = 0) :
    mass f xs = mass f ys := by
  induction xs generalizing ys with
  | nil =>
    exact (mass_zero f ys (fun a ha => hz a ha (by simp))).symm
  | cons a xs ih =>
    obtain ⟨hnot, hnod⟩ := List.nodup_cons.mp hx
    have ha : a ∈ ys := hsub a (by simp)
    have heq := ih (ys.erase a) hnod (List.Nodup.erase a hy)
      (fun b hb => (hy.mem_erase_iff).mpr
        ⟨by intro h; subst b; exact hnot hb, hsub b (by simp [hb])⟩)
      (fun b hby hb => by
        have hba : b ≠ a := ((hy.mem_erase_iff).mp hby).1
        exact hz b (List.mem_of_mem_erase hby) (by simp [hb, hba]))
    rw [mass_cons, mass_erase f ys a ha]
    exact congrArg (fun n => f a + n) heq

theorem support_covering_witness {s : ContractState} {t : Uint256}
    (hs : supportValid s t) :
    (allocationChainIds s t).Nodup ∧
    (∀ c : Uint256, allocationChainAmounts s t c > 0 → c ∈ allocationChainIds s t) :=
  ⟨hs.1, fun c hc => (hs.2 c).mpr hc⟩

theorem all_chain_interpretation_of_ledger {s : ContractState}
    (h : ledgerInvariant s) (t : Uint256) : allChainInterpretation s t := by
  obtain ⟨hc, hs, _, _⟩ := h t
  intro chains hn hcover
  have heq := mass_cover (allocationChainAmounts s t) (allocationChainIds s t) chains
    hs.1 hn (fun c hm => hcover c ((hs.2 c).mp hm))
    (fun c _ hnot => by
      have hzero : ¬allocationChainAmounts s t c > 0 :=
        fun hp => hnot ((hs.2 c).mpr hp)
      omega)
  change mass (allocationChainAmounts s t) chains = (tokenStates s t).committed
  rw [← heq]
  exact hc

theorem expected_position_zero_iff (xs : List Uint256) (c : Uint256) :
    expectedPosition xs c = 0 ↔ c ∉ xs := by
  unfold expectedPosition
  cases hf : xs.findIdx? (fun x => x == c) with
  | none =>
    simp only [true_iff]
    have hh := List.findIdx?_eq_none_iff.mp hf
    intro hm
    have hfalse := hh c hm
    simp at hfalse
  | some i =>
    have hm : c ∈ xs := by
      by_cases hm : c ∈ xs
      · exact hm
      · have hf' : xs.findIdx? (fun x => x == c) = none :=
          List.findIdx?_eq_none_iff.mpr (fun x hx => by
            have hne : x ≠ c := by intro he; subst x; exact hm hx
            simpa using hne)
        simp [hf] at hf'
    simp [hm]

theorem set_contains_iff_mem {s : ContractState} {t c : Uint256}
    (hr : setRepresentationValid s t) :
    allocationChainPositions s t c ≠ 0 ↔ c ∈ allocationChainIds s t := by
  by_cases hm : c ∈ allocationChainIds s t
  · simp [hr.2.2 c, Ne, expected_position_zero_iff, hm]
  · simp [hr.2.2 c, Ne, expected_position_zero_iff, hm]

-- Exact executable monad laws. These are not assumed source refinements.
theorem run_success_iff {α : Type} (op : Contract α) (s out : ContractState) (a : α) :
    op.run s = .success a out ↔ op s = .success a out := by
  unfold Contract.run
  cases h : op s <;> simp

theorem pure_preserves_ledger (a : Unit) : preservesLedger (Verity.pure a) := by
  intro before after hb hs
  have heq : after = before := by
    have hh := (run_success_iff _ _ _ _).mp hs
    cases hh
    rfl
  simpa [heq] using hb

theorem bind_preserves_ledger (op : Contract Unit) (k : Unit → Contract Unit)
    (ho : preservesLedger op) (hk : ∀ a, preservesLedger (k a)) :
    preservesLedger (Verity.bind op k) := by
  intro before after hb hs
  have hs' := (run_success_iff _ _ _ _).mp hs
  unfold Verity.bind at hs'
  cases he : op before with
  | revert msg mid => simp [he] at hs'
  | success a mid =>
    simp only [he] at hs'
    have hm := ho before mid hb ((run_success_iff _ _ _ _).mpr he)
    exact hk a mid after hm ((run_success_iff _ _ _ _).mpr hs')

-- Canonical field lenses. The full-width key distinction is proved, not sampled.
@[simp] theorem token_val_injective (t u : Uint256) : t.val = u.val ↔ t = u := by
  constructor
  · intro h
    cases t
    cases u
    simp_all
  · intro h
    cases h
    rfl

@[simp] theorem amounts_write_position (s : ContractState) (t c u d : Uint256) (n : Nat) :
    allocationChainAmounts (s.writeMapChain 2 [t.val, c.val] 1 (Verity.Core.Uint256.ofNat n)) u d =
      allocationChainAmounts s u d := by
  simp [allocationChainAmounts]

@[simp] theorem tokens_write_position (s : ContractState) (t c u : Uint256) (n : Nat) :
    tokenStates (s.writeMapChain 2 [t.val, c.val] 1 (Verity.Core.Uint256.ofNat n)) u =
      tokenStates s u := by
  simp [tokenStates]

@[simp] theorem amounts_write_array (s : ContractState) (t u c : Uint256) (xs : List Uint256) :
    allocationChainAmounts (s.writeArray t.val xs) u c = allocationChainAmounts s u c := rfl

@[simp] theorem tokens_write_array (s : ContractState) (t u : Uint256) (xs : List Uint256) :
    tokenStates (s.writeArray t.val xs) u = tokenStates s u := rfl

@[simp] theorem positions_write_array (s : ContractState) (t u c : Uint256) (xs : List Uint256) :
    allocationChainPositions (s.writeArray t.val xs) u c = allocationChainPositions s u c := rfl

@[simp] theorem ids_write_position (s : ContractState) (t c u : Uint256) (n : Nat) :
    allocationChainIds (s.writeMapChain 2 [t.val,c.val] 1 (Verity.Core.Uint256.ofNat n)) u =
      allocationChainIds s u := rfl

def bookkeepingValid (s : ContractState) : Prop :=
  ∀ t : Uint256, supportValid s t ∧ allocationRange s t ∧ setRepresentationValid s t

-- This relation deliberately does not state conservation or require it.
-- It records the exact local change caused by one allocation-cell assignment.
def ChainAssignmentEffect (before after : ContractState) (t c : Uint256) (n : Nat) : Prop :=
  bookkeepingValid after ∧
  (∀ u : Uint256, tokenStates after u = tokenStates before u) ∧
  (∀ u d : Uint256, allocationChainAmounts after u d =
    if u = t ∧ d = c then n else allocationChainAmounts before u d) ∧
  (∀ u : Uint256, allocationSum after u + (if u = t then allocationChainAmounts before t c else 0) =
    allocationSum before u + (if u = t then n else 0))


open SetRefinement

def SetFields (s out : ContractState) (t : Uint256) (xs : List Uint256)
    (p : Uint256 → Nat) : Prop :=
  (∀ u, allocationChainIds out u = if u = t then xs else allocationChainIds s u) ∧
  (∀ u d, allocationChainPositions out u d = if u = t then p d else allocationChainPositions s u d) ∧
  (∀ u d, allocationChainAmounts out u d = allocationChainAmounts s u d) ∧
  (∀ u, tokenStates out u = tokenStates s u)

theorem array_fields (s : ContractState) (t : Uint256) (xs : List Uint256) (u : Uint256) :
    allocationChainIds (s.writeArray t.val xs) u = if u = t then xs else allocationChainIds s u := by
  simp only [allocationChainIds, ContractState.readArray, ContractState.writeArray]
  simp [beq_iff_eq]

theorem position_fields (s : ContractState) (t c u d : Uint256) (n : Nat) (hn : n < 2^256) :
    allocationChainPositions (s.writeMapChain 2 [t.val,c.val] 1 (Verity.Core.Uint256.ofNat n)) u d =
      if u = t ∧ d = c then n else allocationChainPositions s u d := by
  by_cases hu : u = t
  · subst u
    by_cases hd : d = c
    · subst d
      simp [allocationChainPositions, Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS, Nat.mod_eq_of_lt hn]
    · simp [allocationChainPositions, hd, Ne.symm hd]
  · simp [allocationChainPositions, hu, Ne.symm hu]

theorem fields_representations {s out : ContractState} {t : Uint256} {xs : List Uint256}
    {p : Uint256 → Nat} (hf : SetFields s out t xs p) (hl : PositionLaw xs p)
    (hlen : xs.length < 2^256) (hr : ∀ u, setRepresentationValid s u) :
    ∀ u, setRepresentationValid out u := by
  intro u
  by_cases hu : u = t
  · subst u
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hf.1, ite_true] using law_nodup hl
    · simpa only [hf.1, ite_true] using hlen
    · intro d
      simp only [hf.1, hf.2.1, ite_true]
      exact law_eq_expected hl d
  · simpa only [setRepresentationValid, hf.1, hf.2.1, hu, ite_false] using hr u

def addSetState (s : ContractState) (t c : Uint256) : ContractState :=
  (s.writeArray t.val (allocationChainIds s t ++ [c])).writeMapChain 2 [t.val,c.val] 1
    (Verity.Core.Uint256.ofNat ((allocationChainIds s t).length + 1))

theorem add_set_fields (s : ContractState) (t c : Uint256)
    (hlen : (allocationChainIds s t).length + 1 < 2^256) :
    SetFields s (addSetState s t c) t (allocationChainIds s t ++ [c])
      (fun d => if d = c then (allocationChainIds s t).length + 1 else allocationChainPositions s t d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u; simp only [addSetState, ids_write_position, array_fields]
  · intro u d
    simp only [addSetState, position_fields _ _ _ _ _ _ hlen, positions_write_array]
    by_cases hu : u = t <;> by_cases hd : d = c <;> simp [hu, hd]
  · intro u d; simp only [addSetState, amounts_write_position, amounts_write_array]
  · intro u; simp only [addSetState, tokens_write_position, tokens_write_array]

theorem set_add_effect (s out : ContractState) (t c : Uint256) (a : Bool)
    (hr : ∀ u, setRepresentationValid s u)
    (hs : (setAdd t c).run s = .success a out) :
    (∀ u, setRepresentationValid out u) ∧
    (∀ u d, d ∈ allocationChainIds out u ↔ d ∈ allocationChainIds s u ∨ (u = t ∧ d = c)) ∧
    (∀ u, u ≠ t → allocationChainIds out u = allocationChainIds s u) ∧
    (∀ u d, allocationChainAmounts out u d = allocationChainAmounts s u d) ∧
    (∀ u, tokenStates out u = tokenStates s u) := by
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hm : c ∈ allocationChainIds s t
  · have hp := (set_contains_iff_mem (hr t)).mpr hm
    simp [setAdd, setContains, Verity.bind, Bind.bind, hp, Verity.pure, Pure.pure] at hh
    obtain ⟨_, ho⟩ := hh
    subst out
    refine ⟨hr, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    intro u d
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h
      · exact hm
  · have hp : allocationChainPositions s t c = 0 := by
      rw [(hr t).2.2 c]; exact expected_absent _ _ hm
    by_cases hlen : (allocationChainIds s t).length + 1 < 2^256
    · simp only [setAdd, setContains, hp, bne_self_eq_false, Verity.bind, Bind.bind,
        Bool.false_eq_true, ite_false, setValues, Verity.require, hlen, decide_true, ite_true,
        writeIds, writeWord, positionKey, Verity.pure, Pure.pure] at hh
      have ho : out = addSetState s t c := by
        exact (ContractResult.success.inj hh).2.symm
      subst out
      have hf := add_set_fields s t c hlen
      have hl := append_law (allocationChainIds s t) (allocationChainPositions s t)
        (by
          have he : allocationChainPositions s t = expectedPosition (allocationChainIds s t) := funext (hr t).2.2
          rw [he]; exact law_expected _ (hr t).1) c hm
      refine ⟨fields_representations hf hl (by simpa using hlen) hr, ?_, ?_, hf.2.2.1, hf.2.2.2⟩
      · intro u d
        rw [hf.1]
        by_cases hu : u = t <;> simp [hu]
      · intro u hu; simp [hf.1, hu]
    · simp [setAdd, setContains, hp, setValues, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, hlen] at hh

def removeSetState (s : ContractState) (t c : Uint256) : ContractState :=
  let xs := allocationChainIds s t
  let position := allocationChainPositions s t c
  let mid := if position - 1 != xs.length - 1 then
    (s.writeArray t.val (xs.set (position-1) xs.getLast!)).writeMapChain 2 [t.val,xs.getLast!.val] 1
      (Verity.Core.Uint256.ofNat position) else s
  (mid.writeArray t.val (allocationChainIds mid t).dropLast).writeMapChain 2 [t.val,c.val] 1 (Verity.Core.Uint256.ofNat 0)

theorem position_index {s : ContractState} {t c : Uint256} (hr : setRepresentationValid s t)
    (hm : c ∈ allocationChainIds s t) :
    ∃ (i : Nat) (hi : i < (allocationChainIds s t).length),
      (allocationChainIds s t)[i] = c ∧ allocationChainPositions s t c = i+1 := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, hi, he, ?_⟩
  rw [hr.2.2, ← he]
  exact expected_at _ hr.1 i hi

theorem remove_set_fields (s : ContractState) (t c : Uint256) (i : Nat)
    (hi : i < (allocationChainIds s t).length)
    (hc : (allocationChainIds s t)[i] = c)
    (hp : allocationChainPositions s t c = i+1)
    (hlen : (allocationChainIds s t).length < 2^256) :
    SetFields s (removeSetState s t c) t (swapPop (allocationChainIds s t) i)
      (removedPosition (allocationChainIds s t) i (allocationChainPositions s t)) := by
  have hn : i+1 < 2^256 := by omega
  have hbang : (allocationChainIds s t)[i]! = c := by
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hc
  have hzero : (0 : Nat) < 2^256 := by decide
  have hmid : i = (allocationChainIds s t).length - 1 →
      (allocationChainIds s t).getLast! = c := by
    intro he; rw [last_eq_index _ (by omega)]; simpa only [he] using hc
  by_cases hm : i = (allocationChainIds s t).length - 1
  · have hb : (i != (allocationChainIds s t).length - 1) = false := by simp only [hm, bne_self_eq_false]
    have hset : (allocationChainIds s t).set i (allocationChainIds s t).getLast! = allocationChainIds s t := by
      rw [hmid hm, ← hc]; exact List.set_getElem_self hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u; simp only [removeSetState, hp, Nat.add_sub_cancel, hb, Bool.false_eq_true,
        ite_false, ids_write_position, array_fields, swapPop, hset]
    · intro u d
      simp only [removeSetState, hp, Nat.add_sub_cancel, hb, Bool.false_eq_true,
        ite_false, position_fields _ _ _ _ _ _ hzero, positions_write_array, removedPosition, hbang, hmid hm]
      by_cases hu : u = t <;> by_cases hd : d = c <;> simp [hu, hd]
    · intro u d; simp only [removeSetState, hp, Nat.add_sub_cancel, hb,
        Bool.false_eq_true, ite_false, amounts_write_position, amounts_write_array]
    · intro u; simp only [removeSetState, hp, Nat.add_sub_cancel, hb,
        Bool.false_eq_true, ite_false, tokens_write_position, tokens_write_array]
  · have hb : (i != (allocationChainIds s t).length - 1) = true := by simpa using hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u
      simp only [removeSetState, hp, Nat.add_sub_cancel, hb, ite_true, ids_write_position, array_fields]
      by_cases hu : u = t <;> simp [hu, swapPop]
    · intro u d
      simp only [removeSetState, hp, Nat.add_sub_cancel, hb, ite_true,
        position_fields _ _ _ _ _ _ hzero, positions_write_array,
        position_fields _ _ _ _ _ _ hn, removedPosition, hbang]
      by_cases hu : u = t <;> by_cases hd : d = c <;> simp [hu, hd]
    · intro u d; simp only [removeSetState, hp, Nat.add_sub_cancel, hb, ite_true,
        amounts_write_position, amounts_write_array]
    · intro u; simp only [removeSetState, hp, Nat.add_sub_cancel, hb, ite_true,
        tokens_write_position, tokens_write_array]

theorem set_remove_effect (s out : ContractState) (t c : Uint256) (a : Bool)
    (hr : ∀ u, setRepresentationValid s u)
    (hs : (setRemove t c).run s = .success a out) :
    (∀ u, setRepresentationValid out u) ∧
    (∀ u d, d ∈ allocationChainIds out u ↔ d ∈ allocationChainIds s u ∧ ¬(u = t ∧ d = c)) ∧
    (∀ u, u ≠ t → allocationChainIds out u = allocationChainIds s u) ∧
    (∀ u d, allocationChainAmounts out u d = allocationChainAmounts s u d) ∧
    (∀ u, tokenStates out u = tokenStates s u) := by
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hm : c ∈ allocationChainIds s t
  · obtain ⟨i, hi, hc, hp⟩ := position_index (hr t) hm
    have hpos : allocationChainPositions s t c ≠ 0 := by omega
    have hg : (allocationChainIds s t).length > 0 ∧ allocationChainPositions s t c ≤ (allocationChainIds s t).length := by omega
    have ho : out = removeSetState s t c := by
      by_cases hb : (i != (allocationChainIds s t).length - 1) = true
      · simp only [setRemove, Verity.bind, Bind.bind, hp, Nat.add_sub_cancel, beq_iff_eq,
          Nat.add_one_ne_zero, ite_false, setValues, Verity.require, hg.1, hp ▸ hg.2,
          decide_true, Bool.and_self, ite_true, hb, writeIds, writeWord, positionKey,
          array_fields, ids_write_position, Verity.pure, Pure.pure] at hh
        have he := (ContractResult.success.inj hh).2.symm
        simpa only [removeSetState, hp, Nat.add_sub_cancel, hb, ite_true, ids_write_position,
          array_fields, ite_true] using he
      · have hb' : (i != (allocationChainIds s t).length - 1) = false := Bool.eq_false_iff.mpr hb
        simp only [setRemove, Verity.bind, Bind.bind, hp, Nat.add_sub_cancel, beq_iff_eq,
          Nat.add_one_ne_zero, ite_false, setValues, Verity.require, hg.1, hp ▸ hg.2,
          decide_true, Bool.and_self, ite_true, hb', Bool.false_eq_true, writeIds, writeWord,
          positionKey, Verity.pure, Pure.pure] at hh
        have he := (ContractResult.success.inj hh).2.symm
        simpa only [removeSetState, hp, Nat.add_sub_cancel, hb', Bool.false_eq_true, ite_false] using he
    subst out
    have hf := remove_set_fields s t c i hi hc hp (hr t).2.1
    have hl := swap_law (allocationChainIds s t) (allocationChainPositions s t)
      (by
        have he : allocationChainPositions s t = expectedPosition (allocationChainIds s t) := funext (hr t).2.2
        rw [he]; exact law_expected _ (hr t).1) i hi
    refine ⟨fields_representations hf hl (by simp; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hr t).2.1) hr,
      ?_, ?_, hf.2.2.1, hf.2.2.2⟩
    · intro u d
      rw [hf.1]
      by_cases hu : u = t
      · subst u
        simpa only [ite_true, true_and, hc, and_comm] using swap_members (allocationChainIds s t) (hr t).1 i hi d
      · simp [hu]
    · intro u hu; simp [hf.1, hu]
  · have hp : allocationChainPositions s t c = 0 := by
      rw [(hr t).2.2 c]; exact expected_absent _ _ hm
    simp [setRemove, Verity.bind, Bind.bind, hp, Verity.pure, Pure.pure] at hh
    obtain ⟨_, ho⟩ := hh
    subst out
    refine ⟨hr, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    intro u d
    constructor
    · intro hd
      refine ⟨hd, ?_⟩
      rintro ⟨rfl, rfl⟩; exact hm hd
    · exact And.left

theorem mass_congr {α : Type} (f g : α → Nat) (xs : List α)
    (h : ∀ a ∈ xs, f a = g a) : mass f xs = mass g xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [mass_cons, mass_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem support_replacement_sum {s out : ContractState} {t c : Uint256} {n : Nat}
    (hs : supportValid s t) (ho : supportValid out t)
    (ha : ∀ d, allocationChainAmounts out t d = if d = c then n else allocationChainAmounts s t d) :
    allocationSum out t + allocationChainAmounts s t c = allocationSum s t + n := by
  let xs := allocationChainIds s t
  let cover := c :: xs.erase c
  have hn : cover.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨List.Nodup.not_mem_erase hs.1, List.Nodup.erase c hs.1⟩
  have oldsub : ∀ d ∈ xs, d ∈ cover := by
    intro d hd
    by_cases hc : d = c
    · simp [cover, hc]
    · exact List.mem_cons.mpr (Or.inr ((hs.1.mem_erase_iff).mpr ⟨hc, hd⟩))
  have oldzero : ∀ d ∈ cover, d ∉ xs → allocationChainAmounts s t d = 0 := by
    intro d _ hd
    have hz : ¬ allocationChainAmounts s t d > 0 := fun hp => hd ((hs.2 d).mpr hp)
    omega
  have heold := mass_cover (allocationChainAmounts s t) xs cover hs.1 hn oldsub oldzero
  have henew := mass_cover (allocationChainAmounts out t) (allocationChainIds out t) cover ho.1 hn
    (fun d hd => by
      by_cases hc : d = c
      · simp [cover, hc]
      · have hp := (ho.2 d).mp hd
        rw [ha d, if_neg hc] at hp
        exact oldsub d ((hs.2 d).mpr hp))
    (fun d _ hd => by
      have hz : ¬ allocationChainAmounts out t d > 0 := fun hp => hd ((ho.2 d).mpr hp)
      omega)
  have hrest := mass_congr (allocationChainAmounts out t) (allocationChainAmounts s t) (xs.erase c)
    (fun d hd => by
      have hc := ((hs.1.mem_erase_iff).mp hd).1
      simp only [ha, hc, ite_false])
  change allocationSum s t = mass (allocationChainAmounts s t) cover at heold
  change allocationSum out t = mass (allocationChainAmounts out t) cover at henew
  simp only [cover, mass_cons] at heold henew
  rw [ha c, if_pos rfl, hrest] at henew
  omega

theorem assignment_from_fields (s out : ContractState) (t c : Uint256) (n : Nat)
    (hq : bookkeepingValid s) (hn : n < amountLimit)
    (hr : ∀ u, setRepresentationValid out u)
    (hm : ∀ u d, d ∈ allocationChainIds out u ↔
      if u = t ∧ d = c then n > 0 else d ∈ allocationChainIds s u)
    (hi : ∀ u, u ≠ t → allocationChainIds out u = allocationChainIds s u)
    (ha : ∀ u d, allocationChainAmounts out u d = if u = t ∧ d = c then n else allocationChainAmounts s u d)
    (ht : ∀ u, tokenStates out u = tokenStates s u) : ChainAssignmentEffect s out t c n := by
  have hsupport : ∀ u, supportValid out u := by
    intro u
    refine ⟨(hr u).1, ?_⟩
    intro d
    rw [hm, ha]
    by_cases hd : u = t ∧ d = c
    · simp [hd]
    · simp only [hd, ite_false]; exact (hq u).1.2 d
  refine ⟨?_, ht, ha, ?_⟩
  · intro u
    refine ⟨hsupport u, ?_, hr u⟩
    intro d
    rw [ha]
    split
    · exact hn
    · exact (hq u).2.1 d
  · intro u
    by_cases hu : u = t
    · subst u
      have he := support_replacement_sum (hq t).1 (hsupport t) (by simpa only [true_and] using ha t)
      simpa only [ite_true] using he
    · have he : allocationSum out u = allocationSum s u := by
        unfold allocationSum
        rw [hi u hu]
        apply mass_congr
        intro d _; simp [ha, hu]
      simp [he, hu]

def amountState (s : ContractState) (t c : Uint256) (n : Nat) : ContractState :=
  s.writeMapChain 3 [t.val,c.val] 0 (Verity.Core.Uint256.ofNat n)

theorem amount_state_fields (s : ContractState) (t c : Uint256) (n : Nat) (hn : n < amountLimit) :
    (∀ u, allocationChainIds (amountState s t c n) u = allocationChainIds s u) ∧
    (∀ u d, allocationChainPositions (amountState s t c n) u d = allocationChainPositions s u d) ∧
    (∀ u, tokenStates (amountState s t c n) u = tokenStates s u) ∧
    (∀ u d, allocationChainAmounts (amountState s t c n) u d =
      if u = t ∧ d = c then n else allocationChainAmounts s u d) := by
  have hnword : n < 2^256 := by unfold amountLimit at hn; omega
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro u d; simp [amountState, allocationChainPositions]
  · intro u; simp [amountState, tokenStates]
  · intro u d
    by_cases hu : u = t
    · subst u
      by_cases hd : d = c
      · subst d
        simp [amountState, allocationChainAmounts, Verity.Core.Uint256.ofNat,
          Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, Nat.mod_eq_of_lt hnword]
      · simp [amountState, allocationChainAmounts, hd, Ne.symm hd]
    · simp [amountState, allocationChainAmounts, hu, Ne.symm hu]

theorem discard_success {α : Type} (op : Contract α) (s out : ContractState)
    (h : (Verity.bind op (fun _ => Verity.pure ())) s = .success () out) :
    ∃ a, op s = .success a out := by
  unfold Verity.bind at h
  cases he : op s with
  | revert msg mid => simp [he] at h
  | success a mid =>
    simp only [he, Verity.pure, ContractResult.success.injEq, true_and] at h
    subst mid; exact ⟨a, rfl⟩

theorem apply_chain_assignment_effect (before after : ContractState) (t c : Uint256)
    (n : Nat) (context : AllocationContext) (hq : bookkeepingValid before)
    (hs : (_applyChainAllocation t c n context).run before = .success () after) :
    ChainAssignmentEffect before after t c n := by
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hfast : allocationChainAmounts before t c = n ∧ context.oldShape = context.liveShape
  · simp [_applyChainAllocation, Verity.bind, Bind.bind, hfast.1, hfast.2, Verity.pure, Pure.pure] at hh
    subst after
    refine ⟨hq, fun _ => rfl, ?_, ?_⟩
    · intro u d
      by_cases hd : u = t ∧ d = c
      · obtain ⟨rfl, rfl⟩ := hd; simp [hfast.1]
      · simp [hd]
    · intro u; by_cases hu : u = t <;> simp [hu, hfast.1]
  · have hb : (allocationChainAmounts before t c == n && context.oldShape == context.liveShape) = false := by
      simpa [Bool.and_eq_true, beq_iff_eq] using hfast
    by_cases hn : n < amountLimit
    · have hf := amount_state_fields before t c n hn
      have hr : ∀ u, setRepresentationValid (amountState before t c n) u := by
        intro u; simpa only [setRepresentationValid, hf.1, hf.2.1] using (hq u).2.2
      by_cases hz : n = 0
      · subst n
        simp only [_applyChainAllocation, Verity.bind, Bind.bind, hb, Bool.false_eq_true,
          ite_false, Verity.require, hn, decide_true, ite_true, beq_self_eq_true,
          writeWord, amountKey, Pure.pure] at hh
        change (Verity.bind (setRemove t c) (fun _ => Verity.pure ())) (amountState before t c 0) = .success () after at hh
        obtain ⟨a, he⟩ := discard_success _ _ _ hh
        obtain ⟨hrep, hmem, hids, ha, ht⟩ := set_remove_effect _ after t c a hr ((run_success_iff _ _ _ _).mpr he)
        apply assignment_from_fields before after t c 0 hq hn hrep
        · intro u d
          rw [hmem, hf.1]
          by_cases hd : u = t ∧ d = c
          · simp [hd]
          · simp [hd]
        · intro u hu; rw [hids u hu, hf.1]
        · intro u d; rw [ha, hf.2.2.2]
        · intro u; rw [ht, hf.2.2.1]
      · have hz' : (n == 0) = false := by simpa using hz
        simp only [_applyChainAllocation, Verity.bind, Bind.bind, hb, Bool.false_eq_true,
          ite_false, Verity.require, hn, decide_true, ite_true, hz', writeWord, amountKey] at hh
        change (Verity.bind (setAdd t c) (fun _ => Verity.pure ())) (amountState before t c n) = .success () after at hh
        obtain ⟨a, he⟩ := discard_success _ _ _ hh
        obtain ⟨hrep, hmem, hids, ha, ht⟩ := set_add_effect _ after t c a hr ((run_success_iff _ _ _ _).mpr he)
        apply assignment_from_fields before after t c n hq hn hrep
        · intro u d
          rw [hmem, hf.1]
          by_cases hd : u = t ∧ d = c
          · simp [hd]; omega
          · simp [hd]
        · intro u hu; rw [hids u hu, hf.1]
        · intro u d; rw [ha, hf.2.2.2]
        · intro u; rw [ht, hf.2.2.1]
    · simp [_applyChainAllocation, Verity.bind, Bind.bind, hb, Verity.require, hn, Verity.pure, Pure.pure] at hh

#print axioms apply_chain_assignment_effect
end Benchmark.Cases.Dromos.AllocationConservation
