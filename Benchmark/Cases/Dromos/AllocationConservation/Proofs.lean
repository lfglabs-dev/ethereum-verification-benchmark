import Benchmark.Cases.Dromos.AllocationConservation.AssignmentProofs

/-! Operational preservation and Reachable closure for the Dromos Labs team's
selected allocation invariant. Concrete assignment/EnumerableSet refinement is
mechanically proved in AssignmentProofs and SetProofs with no domain axiom.
This is a symbolic ledger-model result, not Solidity/bytecode refinement.
-/
namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity
set_option maxHeartbeats 1000000

-- Quality is independent of commitment; this separation avoids assuming the
-- selected invariant inside a temporarily unbalanced helper transition.
theorem bookkeeping_of_ledger {s : ContractState} (h : ledgerInvariant s) : bookkeepingValid s :=
  fun t => ⟨(h t).2.1, (h t).2.2.1, (h t).2.2.2⟩

theorem bookkeeping_congr {s out : ContractState}
    (hi : ∀ t, allocationChainIds out t = allocationChainIds s t)
    (ha : ∀ t c, allocationChainAmounts out t c = allocationChainAmounts s t c)
    (hp : ∀ t c, allocationChainPositions out t c = allocationChainPositions s t c)
    (hq : bookkeepingValid s) : bookkeepingValid out := by
  intro t
  simpa [supportValid, allocationRange, setRepresentationValid, hi, ha, hp] using hq t

-- Packed uint128 commitment writes are proved against the real native lens.
def packed (st : TokenState) : Nat :=
  st.committed + amountLimit * st.lastStakeEnd + amountLimit * timeLimit * st.lastAllocated +
    amountLimit * timeLimit * timeLimit * (if st.isPermanent then 1 else 0)

theorem packed_commitment (st : TokenState) (hc : st.committed < amountLimit)
    (he : st.lastStakeEnd < timeLimit) (ha : st.lastAllocated < timeLimit) :
    (Verity.Core.Uint256.ofNat (packed st)).val % amountLimit = st.committed := by
  unfold packed amountLimit timeLimit at *
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  split <;> omega

@[simp] theorem amounts_write_token (s : ContractState) (t u c : Uint256) (n : Nat) :
    allocationChainAmounts (s.writeMapChain 4 [t.val] 0 (Verity.Core.Uint256.ofNat n)) u c =
      allocationChainAmounts s u c := by simp [allocationChainAmounts]

@[simp] theorem positions_write_token (s : ContractState) (t u c : Uint256) (n : Nat) :
    allocationChainPositions (s.writeMapChain 4 [t.val] 0 (Verity.Core.Uint256.ofNat n)) u c =
      allocationChainPositions s u c := by simp [allocationChainPositions]

@[simp] theorem ids_write_token (s : ContractState) (t u : Uint256) (n : Nat) :
    allocationChainIds (s.writeMapChain 4 [t.val] 0 (Verity.Core.Uint256.ofNat n)) u =
      allocationChainIds s u := rfl

def CommitmentAssignmentEffect (before after : ContractState) (t : Uint256) (n : Nat) : Prop :=
  (∀ u, allocationChainIds after u = allocationChainIds before u) ∧
  (∀ u c, allocationChainAmounts after u c = allocationChainAmounts before u c) ∧
  (∀ u c, allocationChainPositions after u c = allocationChainPositions before u c) ∧
  (∀ u, (tokenStates after u).committed = if u = t then n else (tokenStates before u).committed)

theorem write_token_effect (s out : ContractState) (t : Uint256) (st : TokenState)
    (hs : (writeTokenState t st).run s = .success () out) :
    CommitmentAssignmentEffect s out t st.committed := by
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hc : st.committed < amountLimit
  · by_cases ht : st.lastStakeEnd < timeLimit ∧ st.lastAllocated < timeLimit
    · simp only [writeTokenState, Verity.bind, Bind.bind, Verity.require, hc, ht.1, ht.2,
        decide_true, Bool.and_self, ite_true, writeWord, tokenKey,
        ContractResult.success.injEq, true_and] at hh
      subst out
      refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
      · intro u c; exact amounts_write_token _ _ _ _ _
      · intro u c; exact positions_write_token _ _ _ _ _
      · intro u
        by_cases hut : u = t
        · subst u
          simp only [tokenStates, ContractState.readMapChain_writeMapChain_same, ite_true]
          exact packed_commitment st hc ht.1 ht.2
        · simp [tokenStates, hut]
    · simp [writeTokenState, Verity.bind, Bind.bind, Verity.require, hc, ht] at hh
  · simp [writeTokenState, Verity.bind, Bind.bind, Verity.require, hc] at hh

theorem set_committed_effect (s out : ContractState) (t : Uint256) (n : Nat)
    (hs : (setCommitted t n).run s = .success () out) :
    CommitmentAssignmentEffect s out t n := by
  have hh := (run_success_iff _ _ _ _).mp hs
  simp only [setCommitted, Verity.bind, Bind.bind] at hh
  exact write_token_effect s out t { tokenStates s t with committed := n }
    ((run_success_iff _ _ _ _).mpr hh)

theorem sum_of_commitment_effect {s out : ContractState} {t : Uint256} {n : Nat}
    (h : CommitmentAssignmentEffect s out t n) (u : Uint256) :
    allocationSum out u = allocationSum s u := by
  simp [allocationSum, h.1, h.2.1]

-- Paired arithmetic composes the checked concrete set-cell refinement.
theorem paired_addition {s mid out : ContractState} {t c : Uint256} {n : Nat}
    (hi : ledgerInvariant s)
    (hcell : ChainAssignmentEffect s mid t c (allocationChainAmounts s t c + n))
    (hcommit : CommitmentAssignmentEffect mid out t ((tokenStates s t).committed + n)) :
    ledgerInvariant out := by
  have hq := bookkeeping_congr hcommit.1 hcommit.2.1 hcommit.2.2.1 hcell.1
  intro u
  refine ⟨?_, (hq u).1, (hq u).2.1, (hq u).2.2⟩
  unfold allocationConserved
  rw [sum_of_commitment_effect hcommit, hcommit.2.2.2 u]
  have heq := hcell.2.2.2 u
  have hc := (hi u).1
  unfold allocationConserved at hc
  have ht := congrArg TokenState.committed (hcell.2.1 u)
  by_cases hut : u = t
  · subst u; simp only [ite_true] at *; omega
  · simp only [if_neg hut] at *; omega

theorem paired_subtraction {s mid out : ContractState} {t c : Uint256} {n : Nat}
    (hi : ledgerInvariant s) (hbound : n ≤ allocationChainAmounts s t c)
    (hcommitbound : n ≤ (tokenStates s t).committed)
    (hcell : ChainAssignmentEffect s mid t c (allocationChainAmounts s t c - n))
    (hcommit : CommitmentAssignmentEffect mid out t ((tokenStates s t).committed - n)) :
    ledgerInvariant out := by
  have hq := bookkeeping_congr hcommit.1 hcommit.2.1 hcommit.2.2.1 hcell.1
  intro u
  refine ⟨?_, (hq u).1, (hq u).2.1, (hq u).2.2⟩
  unfold allocationConserved
  rw [sum_of_commitment_effect hcommit, hcommit.2.2.2 u]
  have heq := hcell.2.2.2 u
  have hc := (hi u).1
  unfold allocationConserved at hc
  have ht := congrArg TokenState.committed (hcell.2.1 u)
  by_cases hut : u = t
  · subst u; simp only [ite_true] at *; omega
  · simp only [if_neg hut] at *; omega

theorem remove_chain0_preserves : ∀ leg : SourceDelta, preservesLedger (_removeChain0Contribution leg) := by
  intro leg s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hz : leg.amount = 0
  · simp [hz, _removeChain0Contribution, Verity.bind, Bind.bind, Verity.pure, Pure.pure] at hh
    subst out
    exact hi
  · by_cases hr : leg.amount < amountLimit
    · by_cases hb : leg.amount ≤ allocationChainAmounts s leg.tokenId CHAIN0
      · simp only [_removeChain0Contribution, Verity.bind, Bind.bind,
          Verity.require, hz, beq_iff_eq, if_false, hr, hb, decide_true, ite_true,
          _settleChain, Verity.pure, Pure.pure] at hh
        cases he : _applyChainAllocation leg.tokenId CHAIN0
            (allocationChainAmounts s leg.tokenId CHAIN0 - leg.amount)
            (_sameShapeContext ⟨(tokenStates s leg.tokenId).lastStakeEnd,
              (tokenStates s leg.tokenId).isPermanent⟩) s with
        | revert reason mid => simp [he] at hh
        | success a mid =>
          cases a
          simp only [he] at hh
          by_cases hc : leg.amount ≤ (tokenStates s leg.tokenId).committed
          · simp only [hc, decide_true, ite_true] at hh
            exact paired_subtraction hi hb hc
              (apply_chain_assignment_effect s mid _ _ _ _ (bookkeeping_of_ledger hi)
                ((run_success_iff _ _ _ _).mpr he))
              (set_committed_effect mid out _ _ ((run_success_iff _ _ _ _).mpr hh))
          · simp [Verity.require, hc] at hh
      · simp [hr, hb, hz, _removeChain0Contribution, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure] at hh
    · simp [hr, hz, _removeChain0Contribution, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure] at hh

theorem write_token_preserves {s out : ContractState} {t : Uint256} {st : TokenState}
    (hi : ledgerInvariant s) (hc : st.committed = (tokenStates s t).committed)
    (hs : (writeTokenState t st).run s = .success () out) : ledgerInvariant out := by
  have he := write_token_effect s out t st hs
  have hq := bookkeeping_congr he.1 he.2.1 he.2.2.1 (bookkeeping_of_ledger hi)
  intro u
  refine ⟨?_, (hq u).1, (hq u).2.1, (hq u).2.2⟩
  unfold allocationConserved
  rw [sum_of_commitment_effect he, he.2.2.2 u]
  by_cases hut : u = t
  · subst u; simpa [hc, allocationConserved] using (hi t).1
  · simpa [hut, allocationConserved] using (hi u).1

theorem add_chain0_preserves : ∀ leg : DestinationDelta, preservesLedger (_addChain0Contribution leg) := by
  intro leg s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hz : leg.amount = 0
  · simp [hz, _addChain0Contribution, Verity.bind, Bind.bind, Verity.pure, Pure.pure] at hh
    subst out
    exact hi
  · by_cases hr : leg.amount < amountLimit ∧ leg.liveShape.stakeEnd < timeLimit
    · let shapeCheck := (allocationChainIds s leg.tokenId).isEmpty ||
        ((tokenStates s leg.tokenId).lastStakeEnd == leg.liveShape.stakeEnd &&
         (tokenStates s leg.tokenId).isPermanent == leg.liveShape.isPermanent)
      by_cases hg : shapeCheck = true
      · simp only [_addChain0Contribution, Verity.bind, Bind.bind, Verity.require,
          hz, beq_iff_eq, if_false, hr.1, hr.2, decide_true, Bool.and_self, ite_true,
          Verity.pure, Pure.pure] at hh
        have hg' : ((allocationChainIds s leg.tokenId).isEmpty ||
            ((tokenStates s leg.tokenId).lastStakeEnd == leg.liveShape.stakeEnd &&
             (tokenStates s leg.tokenId).isPermanent == leg.liveShape.isPermanent)) = true := hg
        simp only [hg', ite_true] at hh
        cases he : _applyChainAllocation leg.tokenId CHAIN0
            (allocationChainAmounts s leg.tokenId CHAIN0 + leg.amount) (_sameShapeContext leg.liveShape) s with
        | revert msg mid => simp [he] at hh
        | success a mid =>
          cases a
          simp only [he] at hh
          cases hce : setCommitted leg.tokenId ((tokenStates s leg.tokenId).committed + leg.amount) mid with
          | revert msg fin => simp [hce] at hh
          | success a fin =>
            cases a
            simp only [hce] at hh
            have hfin := paired_addition hi
              (apply_chain_assignment_effect s mid _ _ _ _ (bookkeeping_of_ledger hi)
                ((run_success_iff _ _ _ _).mpr he))
              (set_committed_effect mid fin _ _ ((run_success_iff _ _ _ _).mpr hce))
            by_cases hempty : (allocationChainIds s leg.tokenId).isEmpty = true
            · simp only [hempty, ite_true] at hh
              simp only [Verity.bind] at hh
              exact write_token_preserves (t := leg.tokenId)
                (st := { tokenStates fin leg.tokenId with lastStakeEnd := leg.liveShape.stakeEnd, isPermanent := leg.liveShape.isPermanent })
                hfin rfl ((run_success_iff _ _ _ _).mpr hh)
            · simp [hempty, Verity.pure] at hh
              subst out
              exact hfin
      · have hgp : ¬(allocationChainIds s leg.tokenId = [] ∨
            (tokenStates s leg.tokenId).lastStakeEnd = leg.liveShape.stakeEnd ∧
            (tokenStates s leg.tokenId).isPermanent = leg.liveShape.isPermanent) := by
          simpa [shapeCheck] using hg
        simp [_addChain0Contribution, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, hz, hr.1, hr.2, hgp] at hh
    · simp [_addChain0Contribution, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, hz, hr] at hh

theorem remove_sources_preserves (xs : List SourceDelta) : preservesLedger (removeSources xs) := by
  induction xs with
  | nil => exact pure_preserves_ledger ()
  | cons a xs ih =>
    exact bind_preserves_ledger _ _ (remove_chain0_preserves a) (fun _ => ih)

theorem add_destinations_preserves (xs : List DestinationDelta) : preservesLedger (addDestinations xs) := by
  induction xs with
  | nil => exact pure_preserves_ledger ()
  | cons a xs ih =>
    exact bind_preserves_ledger _ _ (add_chain0_preserves a) (fun _ => ih)

-- Reanchoring is a frame on all sums and commitments, not a conservation axiom.
def AllocationFrame (s out : ContractState) : Prop :=
  bookkeepingValid out ∧ (∀ t, tokenStates out t = tokenStates s t) ∧
  (∀ t, allocationSum out t = allocationSum s t) ∧
  (∀ t c, allocationChainAmounts out t c = allocationChainAmounts s t c)

theorem same_amount_frame {s out : ContractState} {t c : Uint256} {ctx : AllocationContext}
    (hq : bookkeepingValid s)
    (hs : (_applyChainAllocation t c (allocationChainAmounts s t c) ctx).run s = .success () out) :
    AllocationFrame s out := by
  have he := apply_chain_assignment_effect s out t c _ ctx hq hs
  refine ⟨he.1, he.2.1, ?_, ?_⟩
  · intro u
    have hsum := he.2.2.2 u
    omega
  · intro u d
    rw [he.2.2.1 u d]
    by_cases h : u = t ∧ d = c
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp [h]

theorem allocation_frame_trans {s mid out : ContractState}
    (h : AllocationFrame s mid) (k : AllocationFrame mid out) : AllocationFrame s out := by
  refine ⟨k.1, ?_, ?_, ?_⟩
  · intro t; rw [k.2.1 t, h.2.1 t]
  · intro t; rw [k.2.2.1 t, h.2.2.1 t]
  · intro t c; rw [k.2.2.2 t c, h.2.2.2 t c]

theorem allocation_frame_preserves {s out : ContractState}
    (h : AllocationFrame s out) (hi : ledgerInvariant s) : ledgerInvariant out := by
  intro t
  refine ⟨?_, (h.1 t).1, (h.1 t).2.1, (h.1 t).2.2⟩
  simpa [allocationConserved, h.2.1, h.2.2.1] using (hi t).1

theorem reanchor_loop_frame (t : Uint256) (ctx : AllocationContext) (xs : List Uint256) :
    ∀ s out, bookkeepingValid s → (_reanchorLoop t ctx xs).run s = .success () out → AllocationFrame s out := by
  induction xs with
  | nil =>
    intro s out hq hs
    have hh := (run_success_iff _ _ _ _).mp hs
    simp [_reanchorLoop, Verity.pure] at hh
    subst out
    exact ⟨hq, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  | cons c xs ih =>
    intro s out hq hs
    have hh := (run_success_iff _ _ _ _).mp hs
    simp only [_reanchorLoop, _settleChain, Verity.pure, Pure.pure, Verity.bind, Bind.bind] at hh
    cases he : _applyChainAllocation t c (allocationChainAmounts s t c) ctx s with
    | revert msg mid => simp [he] at hh
    | success a mid =>
      cases a
      simp only [he] at hh
      have hf := same_amount_frame hq ((run_success_iff _ _ _ _).mpr he)
      exact allocation_frame_trans hf (ih mid out hf.1 ((run_success_iff _ _ _ _).mpr hh))

theorem reanchor_frame (t : Uint256) (ctx : AllocationContext) (s out : ContractState)
    (hq : bookkeepingValid s) (hs : (_reanchor t ctx).run s = .success () out) : AllocationFrame s out := by
  have hh := (run_success_iff _ _ _ _).mp hs
  simp only [_reanchor, Verity.bind, Bind.bind] at hh
  exact reanchor_loop_frame t ctx (allocationChainIds s t) s out hq
    ((run_success_iff _ _ _ _).mpr hh)

theorem reanchor_live_preserves (t : Uint256) (shape : Shape) : preservesLedger (_reanchorToLiveShape t shape) := by
  intro s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  simp only [_reanchorToLiveShape, Verity.bind, Bind.bind] at hh
  cases he : _reanchor t
      { oldShape := ⟨(tokenStates s t).lastStakeEnd, (tokenStates s t).isPermanent⟩,
        liveShape := shape, prevCommitted := 0 } s with
  | revert msg mid => simp [he] at hh
  | success a mid =>
    cases a
    simp only [he] at hh
    have hf := reanchor_frame t _ s mid (bookkeeping_of_ledger hi)
      ((run_success_iff _ _ _ _).mpr he)
    exact write_token_preserves (st := { tokenStates s t with lastStakeEnd := shape.stakeEnd, isPermanent := shape.isPermanent })
      (allocation_frame_preserves hf hi) (by rw [hf.2.1 t])
      ((run_success_iff _ _ _ _).mpr hh)

def deltaMass (xs : List ChainAllocation) : Nat := mass (fun a => a.delta) xs

theorem validate_allocations_effect (xs : List ChainAllocation) :
    ∀ previous total s out value,
      (_validateAllocations xs previous total).run s = .success value out →
      out = s ∧ value = total + deltaMass xs ∧ (∀ a ∈ xs, a.chainId ≠ CHAIN0) := by
  induction xs with
  | nil =>
    intro previous total s out value hs
    have hh := (run_success_iff _ _ _ _).mp hs
    simp [_validateAllocations, Verity.pure] at hh
    obtain ⟨rfl, rfl⟩ := hh
    exact ⟨rfl, by simp [deltaMass], by simp⟩
  | cons a xs ih =>
    intro previous total s out value hs
    have hh := (run_success_iff _ _ _ _).mp hs
    by_cases h1 : previous < a.chainId.val
    · by_cases h2 : a.registeredActive = true
      · by_cases h3 : a.hasDestinationGas = true
        · by_cases h4 : a.delta < amountLimit ∧ total + a.delta < amountLimit
          · simp only [_validateAllocations, Verity.bind, Bind.bind, Verity.require,
              h1, h2, h3, h4.1, h4.2, decide_true, Bool.and_self, ite_true] at hh
            obtain ⟨hout, hv, hn⟩ := ih a.chainId.val (total + a.delta) s out value
              ((run_success_iff _ _ _ _).mpr hh)
            refine ⟨hout, ?_, ?_⟩
            · simpa [deltaMass, mass_cons, Nat.add_assoc] using hv
            · intro b hb
              rcases List.mem_cons.mp hb with he | hm
              · subst b
                intro hz
                have hzv : a.chainId.val = 0 := by simp [hz, CHAIN0]
                omega
              · exact hn b hm
          · simp [_validateAllocations, Verity.bind, Bind.bind, Verity.require, h1, h2, h3, h4] at hh
        · simp [_validateAllocations, Verity.bind, Bind.bind, Verity.require, h1, h2, h3] at hh
      · simp [_validateAllocations, Verity.bind, Bind.bind, Verity.require, h1, h2] at hh
    · simp [_validateAllocations, Verity.bind, Bind.bind, Verity.require, h1] at hh

def DeltaEffect (s out : ContractState) (t : Uint256) (xs : List ChainAllocation) : Prop :=
  bookkeepingValid out ∧
  (∀ u, tokenStates out u = tokenStates s u) ∧
  (∀ u, allocationSum out u = allocationSum s u + (if u = t then deltaMass xs else 0)) ∧
  (∀ u, allocationChainAmounts out u CHAIN0 = allocationChainAmounts s u CHAIN0)

theorem apply_deltas_effect (t : Uint256) (ctx : AllocationContext) (xs : List ChainAllocation) :
    ∀ s out, bookkeepingValid s → (∀ a ∈ xs, a.chainId ≠ CHAIN0) →
      (_applyChainDeltas t ctx xs).run s = .success () out → DeltaEffect s out t xs := by
  induction xs with
  | nil =>
    intro s out hq hn hs
    have hh := (run_success_iff _ _ _ _).mp hs
    simp [_applyChainDeltas, Verity.pure] at hh
    subst out
    exact ⟨hq, fun _ => rfl, by simp [deltaMass], fun _ => rfl⟩
  | cons a xs ih =>
    intro s out hq hn hs
    have hh := (run_success_iff _ _ _ _).mp hs
    simp only [_applyChainDeltas, _settleChain, Verity.bind, Bind.bind, Verity.pure] at hh
    cases he : _applyChainAllocation t a.chainId (allocationChainAmounts s t a.chainId + a.delta) ctx s with
    | revert msg mid => simp [he] at hh
    | success x mid =>
      cases x
      simp only [he] at hh
      have hf := apply_chain_assignment_effect s mid _ _ _ _ hq ((run_success_iff _ _ _ _).mpr he)
      have ht := ih mid out hf.1 (fun b hb => hn b (by simp [hb]))
        ((run_success_iff _ _ _ _).mpr hh)
      refine ⟨ht.1, ?_, ?_, ?_⟩
      · intro u; rw [ht.2.1 u, hf.2.1 u]
      · intro u
        have hs1 := hf.2.2.2 u
        rw [ht.2.2.1 u]
        by_cases hut : u = t
        · simp only [hut, ite_true, deltaMass, mass_cons] at *; omega
        · simp only [if_neg hut] at *; omega
      · intro u
        rw [ht.2.2.2 u, hf.2.2.1 u CHAIN0]
        have hnon : CHAIN0 ≠ a.chainId := fun h => hn a (by simp) h.symm
        simp [hnon]

def SumFrame (s out : ContractState) : Prop :=
  bookkeepingValid out ∧ (∀ t, tokenStates out t = tokenStates s t) ∧
  (∀ t, allocationSum out t = allocationSum s t)

theorem sum_frame_preserves {s out : ContractState}
    (h : SumFrame s out) (hi : ledgerInvariant s) : ledgerInvariant out := by
  intro t
  refine ⟨?_, (h.1 t).1, (h.1 t).2.1, (h.1 t).2.2⟩
  simpa [allocationConserved, h.2.1, h.2.2] using (hi t).1

-- Local budget closing is a primitive one-cell debit, not an assumed writer law.
def closeChain0 (t : Uint256) (ctx : AllocationContext) (total parked : Nat) : Contract Unit :=
  if total > 0 then do
    _settleChain CHAIN0
    _applyChainAllocation t CHAIN0 (parked - total) ctx
  else Verity.pure ()

theorem close_chain0_effect {base mid out : ContractState} {t : Uint256} {ctx : AllocationContext}
    {xs : List ChainAllocation} {total parked : Nat}
    (hd : DeltaEffect base mid t xs)
    (htotal : total = deltaMass xs) (hparked : allocationChainAmounts base t CHAIN0 = parked)
    (hbudget : total ≤ parked)
    (hs : (closeChain0 t ctx total parked).run mid = .success () out) : SumFrame base out := by
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hz : total > 0
  · simp only [closeChain0, hz, ite_true, _settleChain, Verity.bind, Bind.bind, Verity.pure] at hh
    have he := apply_chain_assignment_effect mid out t CHAIN0 (parked - total) ctx hd.1
      ((run_success_iff _ _ _ _).mpr hh)
    refine ⟨he.1, fun u => (he.2.1 u).trans (hd.2.1 u), ?_⟩
    intro u
    have hsum := he.2.2.2 u
    have hdSum := hd.2.2.1 u
    have hmidpark := (hd.2.2.2 t).trans hparked
    by_cases hut : u = t
    · simp only [hut, ite_true] at *; omega
    · simp only [if_neg hut] at *; omega
  · simp [closeChain0, hz, Verity.pure] at hh
    subst out
    refine ⟨hd.1, hd.2.1, ?_⟩
    intro u
    have hz0 : total = 0 := by omega
    simpa [← htotal, hz0] using hd.2.2.1 u

theorem maybe_reanchor_frame (t : Uint256) (ctx : AllocationContext) (s out : ContractState)
    (hq : bookkeepingValid s)
    (hs : (if ctx.oldShape != ctx.liveShape then _reanchor t ctx else Verity.pure ()).run s =
      .success () out) : AllocationFrame s out := by
  by_cases hc : ctx.oldShape ≠ ctx.liveShape
  · simp [hc] at hs
    exact reanchor_frame t ctx s out hq hs
  · simp [hc, Verity.pure, Contract.run] at hs
    subst out
    exact ⟨hq, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem apply_allocation_normalize (t : Uint256) (xs : List ChainAllocation) (total : Nat)
    (ctx : AllocationContext) (now : Nat) (s : ContractState)
    (hb : total ≤ allocationChainAmounts s t CHAIN0) :
    _applyAllocation t xs total ctx now s =
      (Verity.bind (if ctx.oldShape != ctx.liveShape then _reanchor t ctx else Verity.pure ())
        (fun _ => Verity.bind (_applyChainDeltas t {ctx with oldShape := ctx.liveShape} xs)
          (fun _ => Verity.bind (closeChain0 t {ctx with oldShape := ctx.liveShape} total
            (allocationChainAmounts s t CHAIN0))
            (fun _ => writeTokenState t { committed := ctx.prevCommitted, lastStakeEnd := ctx.liveShape.stakeEnd, lastAllocated := now % timeLimit, isPermanent := ctx.liveShape.isPermanent })))) s := by
  by_cases hshape : ctx.oldShape = ctx.liveShape <;> by_cases htotal : total > 0 <;>
    simp [_applyAllocation, closeChain0, Verity.bind, Bind.bind, Verity.require, hb,
      hshape, htotal, _settleChain, _refreshEmissionsPerVP, Verity.pure, Pure.pure]

theorem apply_allocation_preserves (t : Uint256) (xs : List ChainAllocation) (total : Nat)
    (ctx : AllocationContext) (now : Nat) (htotal : total = deltaMass xs)
    (hn : ∀ a ∈ xs, a.chainId ≠ CHAIN0) :
    ∀ s out, ledgerInvariant s → ctx.prevCommitted = (tokenStates s t).committed →
      (_applyAllocation t xs total ctx now).run s = .success () out → ledgerInvariant out := by
  intro s out hi hc hs
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hb : total ≤ allocationChainAmounts s t CHAIN0
  · rw [apply_allocation_normalize t xs total ctx now s hb] at hh
    simp only [Verity.bind] at hh
    cases hre : (if ctx.oldShape != ctx.liveShape then _reanchor t ctx else Verity.pure ()) s with
    | revert msg first => simp only [hre] at hh; cases hh
    | success a first =>
      cases a
      simp only [hre] at hh
      have hf := maybe_reanchor_frame t ctx s first (bookkeeping_of_ledger hi)
        ((run_success_iff _ _ _ _).mpr hre)
      cases hdel : _applyChainDeltas t {ctx with oldShape := ctx.liveShape} xs first with
      | revert msg mid => simp [hdel] at hh
      | success a mid =>
        cases a
        simp only [hdel] at hh
        have hd := apply_deltas_effect t _ xs first mid hf.1 hn
          ((run_success_iff _ _ _ _).mpr hdel)
        cases hclose : closeChain0 t {ctx with oldShape := ctx.liveShape} total
            (allocationChainAmounts s t CHAIN0) mid with
        | revert msg fin => simp only [hclose] at hh; cases hh
        | success a fin =>
          cases a
          simp only [hclose] at hh
          have he := close_chain0_effect hd htotal (hf.2.2.2 t CHAIN0)
            hb
            ((run_success_iff _ _ _ _).mpr hclose)
          have hfin : ledgerInvariant fin := sum_frame_preserves he (allocation_frame_preserves hf hi)
          exact write_token_preserves (t := t)
            (st := { committed := ctx.prevCommitted, lastStakeEnd := ctx.liveShape.stakeEnd, lastAllocated := now % timeLimit, isPermanent := ctx.liveShape.isPermanent })
            hfin (by rw [he.2.1 t, hf.2.1 t]; exact hc)
            ((run_success_iff _ _ _ _).mpr hh)
  · simp [_applyAllocation, Verity.bind, Bind.bind, Verity.require, hb] at hh

theorem prepare_allocations_preserves (env : Environment) (t : Uint256) (xs : List ChainAllocation) :
    preservesLedger (prepareChainAllocations env t xs) := by
  intro s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  simp only [prepareChainAllocations, Verity.bind, Bind.bind] at hh
  cases he : _validateAllocations xs 0 0 s with
  | revert msg mid => simp [he] at hh
  | success total mid =>
    simp only [he] at hh
    obtain ⟨hmid, htotal, hn⟩ := validate_allocations_effect xs 0 0 s mid total
      ((run_success_iff _ _ _ _).mpr he)
    subst mid
    simp only [Nat.zero_add] at htotal
    exact apply_allocation_preserves t xs total _ _ htotal hn s out hi rfl
      ((run_success_iff _ _ _ _).mpr hh)

-- Polymorphic composition covers guards, pure reads, arbitrary finite batches,
-- and the wrappers without changing the operational model.
def Maintains {α : Type} (op : Contract α) : Prop :=
  ∀ s out a, ledgerInvariant s → op s = .success a out → ledgerInvariant out

theorem maintains_of_preserves (op : Contract Unit) (h : preservesLedger op) : Maintains op := by
  intro s out a hi hs
  cases a
  exact h s out hi ((run_success_iff _ _ _ _).mpr hs)

theorem preserves_of_maintains (op : Contract Unit) (h : Maintains op) : preservesLedger op := by
  intro s out hi hs
  exact h s out () hi ((run_success_iff _ _ _ _).mp hs)

theorem maintains_pure {α : Type} (a : α) : Maintains (Verity.pure a) := by
  intro s out x hi hs
  cases hs
  exact hi

theorem maintains_read {α : Type} (f : ContractState → α) :
    Maintains (fun s => .success (f s) s) := by
  intro s out a hi hs
  cases hs
  exact hi

theorem maintains_bind {α β : Type} (op : Contract α) (k : α → Contract β)
    (ho : Maintains op) (hk : ∀ a, Maintains (k a)) : Maintains (Verity.bind op k) := by
  intro s out b hi hs
  unfold Verity.bind at hs
  cases he : op s with
  | revert msg mid => simp [he] at hs
  | success a mid =>
    simp only [he] at hs
    exact hk a mid out b (ho s mid a hi he) hs

theorem maintains_require (b : Bool) (reason : String) : Maintains (Verity.require b reason) := by
  intro s out a hi hs
  by_cases hb : b = true
  · simp [Verity.require, hb] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact hi
  · simp [Verity.require, hb] at hs

theorem maintains_if {α : Type} (b : Bool) (yes no : Contract α)
    (hy : Maintains yes) (hn : Maintains no) : Maintains (if b then yes else no) := by
  cases b <;> assumption

theorem ledger_transient (s : ContractState) (slot : Nat) (n : Uint256) :
    ledgerInvariant (s.writeTransient slot n) ↔ ledgerInvariant s := by
  simp [ledgerInvariant, allocationConserved, allocationSum, supportValid, allocationRange,
    setRepresentationValid, allocationChainIds, allocationChainAmounts, allocationChainPositions,
    tokenStates, ContractState.readMapChain, ContractState.storageMapChain, ContractState.writeTransient, ContractState.readArray]

theorem maintains_transient (slot : Nat) (n : Nat) : Maintains (writeWord (.transient slot) n) := by
  intro s out a hi hs
  simp only [writeWord] at hs
  cases hs
  exact (ledger_transient _ _ _).mpr hi

theorem guarded_preserves (body : Contract Unit) (h : preservesLedger body) : preservesLedger (guarded body) := by
  apply preserves_of_maintains
  unfold guarded
  apply maintains_bind
  · exact maintains_read _
  · intro held
    apply maintains_bind
    · exact maintains_require _ _
    · intro _
      apply maintains_bind
      · exact maintains_transient _ _
      · intro _
        apply maintains_bind
        · exact maintains_of_preserves body h
        · intro _; exact maintains_transient _ _

-- This tactic only composes proved laws for existing program fragments; it
-- cannot assume a desired post-state or synthesize a conservation hypothesis.
syntax "ledger_pipeline" : tactic
macro_rules
  | `(tactic| ledger_pipeline) => `(tactic|
      first
      | exact maintains_pure _
      | exact maintains_read _
      | exact maintains_require _ _
      | exact maintains_of_preserves _ (add_chain0_preserves _)
      | exact maintains_of_preserves _ (remove_sources_preserves _)
      | exact maintains_of_preserves _ (add_destinations_preserves _)
      | exact maintains_of_preserves _ (reanchor_live_preserves _ _)
      | exact maintains_of_preserves _ (prepare_allocations_preserves _ _ _)
      | (apply maintains_bind
         · ledger_pipeline
         · intro x
           ledger_pipeline)
      | (apply maintains_if
         · ledger_pipeline
         · ledger_pipeline))

theorem rebalance_preserves (env : Environment) (src : List SourceDelta) (dst : List DestinationDelta) :
    preservesLedger (rebalanceChain0 env src dst) := by
  apply guarded_preserves
  apply preserves_of_maintains
  simp only [onlyVotingEscrow, msgSender, _settleChain0AndTotal, _refreshEmissionsPerVP, Bind.bind, Pure.pure]
  apply maintains_bind
  · apply maintains_bind
    · exact maintains_read _
    · intro caller; exact maintains_require _ _
  · intro x
    ledger_pipeline

def debitCell (t c : Uint256) (n : Nat) : Contract Unit :=
  Verity.bind (writeWord (amountKey t c) n) (fun _ =>
    if n == 0 then Verity.bind (setRemove t c) (fun _ => Verity.pure ()) else Verity.pure ())

theorem debit_cell_equiv (s : ContractState) (t c : Uint256) (n : Nat) (ctx : AllocationContext)
    (hp : allocationChainPositions s t c ≠ 0) (hn : n < amountLimit)
    (hd : allocationChainAmounts s t c ≠ n) :
    debitCell t c n s = _applyChainAllocation t c n ctx s := by
  by_cases hz : n = 0
  · subst n
    simp [debitCell, _applyChainAllocation, hd, hn, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.require, writeWord, amountKey, amountLimit]
  · have hp' : (s.readMapChain 2 [t.val, c.val] 1).val ≠ 0 := hp
    have hadd : setAdd t c (s.writeMapChain 3 [t.val,c.val] 0 (Verity.Core.Uint256.ofNat n)) =
        .success false (s.writeMapChain 3 [t.val,c.val] 0 (Verity.Core.Uint256.ofNat n)) := by
      simp [setAdd, setContains, allocationChainPositions, hp', Verity.bind, Bind.bind,
        Verity.pure, Pure.pure]
    simp [debitCell, _applyChainAllocation, hd, hz, hn, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.require, writeWord, amountKey, hadd]

theorem burn_normalize (n : Nat) (s : ContractState)
    (hn : n > 0 ∧ n < amountLimit)
    (hc : n ≤ (tokenStates s TOKEN0).committed)
    (ha : n ≤ allocationChainAmounts s TOKEN0 CHAIN0) :
    applyBurn n s =
      Verity.bind (setCommitted TOKEN0 ((tokenStates s TOKEN0).committed - n))
        (fun _ => debitCell TOKEN0 CHAIN0 (allocationChainAmounts s TOKEN0 CHAIN0 - n)) s := by
  by_cases hz : allocationChainAmounts s TOKEN0 CHAIN0 - n = 0 <;>
    simp [applyBurn, debitCell, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
      hn.1, hn.2, hc, ha, hz, _settleChain0AndTotal, _refreshEmissionsPerVP]

theorem burn_body_preserves (n : Nat) : preservesLedger (applyBurn n) := by
  intro s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases hn : n > 0 ∧ n < amountLimit
  · by_cases hc : n ≤ (tokenStates s TOKEN0).committed
    · by_cases ha : n ≤ allocationChainAmounts s TOKEN0 CHAIN0
      · rw [burn_normalize n s hn hc ha] at hh
        simp only [Verity.bind] at hh
        cases hce : setCommitted TOKEN0 ((tokenStates s TOKEN0).committed - n) s with
        | revert msg mid => simp [hce] at hh
        | success a mid =>
          cases a
          simp only [hce] at hh
          have ht := set_committed_effect s mid TOKEN0 _ ((run_success_iff _ _ _ _).mpr hce)
          have hq := bookkeeping_congr ht.1 ht.2.1 ht.2.2.1 (bookkeeping_of_ledger hi)
          have hpos : allocationChainPositions s TOKEN0 CHAIN0 ≠ 0 := by
            apply (set_contains_iff_mem (hi TOKEN0).2.2.2).mpr
            apply ((hi TOKEN0).2.1.2 CHAIN0).mpr
            omega
          have hbound : allocationChainAmounts s TOKEN0 CHAIN0 - n < amountLimit := by
            have h := (hi TOKEN0).2.2.1 CHAIN0; omega
          rw [debit_cell_equiv mid TOKEN0 CHAIN0
              (allocationChainAmounts s TOKEN0 CHAIN0 - n) (_sameShapeContext ⟨0, false⟩)
              (by rw [ht.2.2.1 TOKEN0 CHAIN0]; exact hpos) hbound
              (by rw [ht.2.1 TOKEN0 CHAIN0]; omega)] at hh
          have he := apply_chain_assignment_effect mid out TOKEN0 CHAIN0 _ _ hq
            ((run_success_iff _ _ _ _).mpr hh)
          intro u
          refine ⟨?_, (he.1 u).1, (he.1 u).2.1, (he.1 u).2.2⟩
          unfold allocationConserved
          have hsum := he.2.2.2 u
          have hsum0 := sum_of_commitment_effect ht u
          have hbase := (hi u).1
          unfold allocationConserved at hbase
          have hcommit := congrArg TokenState.committed (he.2.1 u)
          rw [ht.2.2.2 u] at hcommit
          rw [ht.2.1 TOKEN0 CHAIN0] at hsum
          by_cases hu : u = TOKEN0
          · subst u; simp only [ite_true] at *; omega
          · simp only [if_neg hu] at *; omega
      · simp [applyBurn, Verity.bind, Bind.bind, Verity.require, hn.1, hn.2, hc, ha] at hh
    · simp [applyBurn, Verity.bind, Bind.bind, Verity.require, hn.1, hn.2, hc] at hh
  · simp [applyBurn, Verity.bind, Bind.bind, Verity.require, hn] at hh

theorem burn_preserves (env : Environment) (n : Nat) : preservesLedger (burn env n) := by
  apply guarded_preserves
  apply preserves_of_maintains
  unfold onlyVotingEscrow
  apply maintains_bind
  · apply maintains_bind
    · exact maintains_read _
    · intro _; exact maintains_require _ _
  · intro _; exact maintains_of_preserves _ (burn_body_preserves n)

theorem park_preserves (env : Environment) (t : Uint256) : preservesLedger (parkOnChain0 env t) := by
  apply guarded_preserves
  apply preserves_of_maintains
  simp only [onlyVotingEscrow, requireLive, _settleChain0AndTotal, _refreshEmissionsPerVP, Bind.bind, Pure.pure]
  ledger_pipeline

-- Distinct origin and CHAIN0 transfer has zero net sum change; the credit is
-- clamped against the live booking. No historic-message identity is assumed.
theorem paired_transfer {s mid out : ContractState} {t origin : Uint256} {credit : Nat}
    (hi : ledgerInvariant s) (hne : origin ≠ CHAIN0)
    (hb : credit ≤ allocationChainAmounts s t origin)
    (hdebit : ChainAssignmentEffect s mid t origin (allocationChainAmounts s t origin - credit))
    (hcredit : ChainAssignmentEffect mid out t CHAIN0 (allocationChainAmounts mid t CHAIN0 + credit)) :
    ledgerInvariant out := by
  intro u
  refine ⟨?_, (hcredit.1 u).1, (hcredit.1 u).2.1, (hcredit.1 u).2.2⟩
  unfold allocationConserved
  have hd := hdebit.2.2.2 u
  have ha := hcredit.2.2.2 u
  have hc := (hi u).1
  unfold allocationConserved at hc
  rw [hcredit.2.1 u, hdebit.2.1 u]
  by_cases hut : u = t
  · subst u; simp only [ite_true] at *; omega
  · simp only [if_neg hut] at *; omega

theorem credit_deallocation_maintains (origin t : Uint256) (amount : Nat) (hne : origin ≠ CHAIN0) :
    Maintains (creditDeallocation origin t amount) := by
  intro s out result hi hs
  by_cases hr : amount < amountLimit
  · by_cases hz : min amount (allocationChainAmounts s t origin) = 0
    · simp [creditDeallocation, Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure, hr, hz] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact hi
    · simp only [creditDeallocation, Verity.bind, Bind.bind, Verity.require,
        hr, decide_true, ite_true, hz, beq_iff_eq, if_false, _settleChain0AndTotal,
        _settleChain, Verity.pure, Pure.pure] at hs
      cases hd : _applyChainAllocation t origin
          (allocationChainAmounts s t origin - min amount (allocationChainAmounts s t origin))
          (_sameShapeContext ⟨(tokenStates s t).lastStakeEnd, (tokenStates s t).isPermanent⟩) s with
      | revert msg mid => simp [hd] at hs
      | success a mid =>
        cases a
        simp only [hd] at hs
        have he := apply_chain_assignment_effect s mid _ _ _ _ (bookkeeping_of_ledger hi)
          ((run_success_iff _ _ _ _).mpr hd)
        cases hc : _applyChainAllocation t CHAIN0
            (allocationChainAmounts mid t CHAIN0 + min amount (allocationChainAmounts s t origin))
            (_sameShapeContext ⟨(tokenStates s t).lastStakeEnd, (tokenStates s t).isPermanent⟩) mid with
        | revert msg fin => simp [hc] at hs
        | success a fin =>
          cases a
          simp only [hc, _refreshEmissionsPerVP, Verity.pure] at hs
          obtain ⟨_, hout⟩ := ContractResult.success.inj hs
          subst out
          exact paired_transfer hi hne (Nat.min_le_right _ _) he
            (apply_chain_assignment_effect mid fin _ _ _ _ he.1 ((run_success_iff _ _ _ _).mpr hc))
  · simp [creditDeallocation, Verity.bind, Bind.bind, Verity.require, hr] at hs

theorem process_deallocation_preserves (env : Environment) (r : DeallocationReturn) :
    preservesLedger (processDeallocation env r) := by
  intro s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  by_cases ha : s.sender = env.orchestrator
  · by_cases hc : r.registered = true ∧ r.originChainId ≠ CHAIN0
    · simp only [processDeallocation, msgSender, Verity.bind, Bind.bind, Verity.require,
        ha, beq_iff_eq, decide_true, ite_true, hc.1, hc.2, bne_iff_ne, Bool.and_self] at hh
      simp [hc.2] at hh
      cases he : creditDeallocation r.originChainId r.tokenId r.amount s with
      | revert msg mid => simp [he] at hh
      | success n mid =>
        simp [he, Verity.pure, Pure.pure] at hh
        subst out
        exact credit_deallocation_maintains _ _ _ hc.2 s mid n hi he
    · simp [processDeallocation, msgSender, Verity.bind, Bind.bind, Verity.require, ha, hc] at hh
  · simp [processDeallocation, msgSender, Verity.bind, Bind.bind, Verity.require, ha] at hh

theorem ledger_sender (s : ContractState) (a : Address) :
    ledgerInvariant {s with sender := a} ↔ ledgerInvariant s := Iff.rfl

theorem authenticated_return_preserves (env : Environment) (r : DeallocationReturn) :
    preservesLedger (authenticatedReturn env r) := by
  intro s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  unfold authenticatedReturn at hh
  cases he : processDeallocation env r { s with sender := env.orchestrator } with
  | revert msg mid => simp [he] at hh
  | success a mid =>
    cases a
    simp only [he, ContractResult.success.injEq, true_and] at hh
    subst out
    apply (ledger_sender _ _).mpr
    exact process_deallocation_preserves env r _ mid ((ledger_sender _ _).mpr hi)
      ((run_success_iff _ _ _ _).mpr he)

theorem dispatch_returns_preserves (env : Environment) (xs : List DeallocationReturn) :
    preservesLedger (dispatchReturns env xs) := by
  induction xs with
  | nil => exact pure_preserves_ledger ()
  | cons r xs ih =>
    exact bind_preserves_ledger _ _ (authenticated_return_preserves env r) (fun _ => ih)

syntax "ledger_pipeline_full" : tactic
macro_rules
  | `(tactic| ledger_pipeline_full) => `(tactic|
      first
      | exact maintains_pure _
      | exact maintains_read _
      | exact maintains_require _ _
      | exact maintains_of_preserves _ (prepare_allocations_preserves _ _ _)
      | exact maintains_of_preserves _ (dispatch_returns_preserves _ _)
      | exact credit_deallocation_maintains _ _ _ (by assumption)
      | (apply maintains_bind
         · ledger_pipeline_full
         · intro x
           ledger_pipeline_full)
      | (apply maintains_if
         · ledger_pipeline_full
         · ledger_pipeline_full))

theorem allocate_chains_preserves (env : Environment) (t : Uint256) (xs : List ChainAllocation) :
    preservesLedger (allocateChains env t xs) := by
  apply guarded_preserves
  apply preserves_of_maintains
  simp only [requireLive, Bind.bind, Pure.pure]
  ledger_pipeline_full

theorem allocate_preserves (env : Environment) (t : Uint256) (xs : List ChainAllocation)
    (nonempty checks : Bool) : preservesLedger (allocate env t xs nonempty checks) := by
  apply guarded_preserves
  apply preserves_of_maintains
  simp only [requireLive, Bind.bind, Pure.pure]
  ledger_pipeline_full

theorem nonwriter_preserves (env : Environment) (rs : List DeallocationReturn) :
    preservesLedger (nonwriterWithReturns env rs) :=
  guarded_preserves _ (dispatch_returns_preserves env rs)

theorem emergency_preserves (env : Environment) (t c : Uint256) (suspended allowed gas : Bool) :
    preservesLedger (emergencyDeallocate env t c suspended allowed gas) := by
  by_cases hn : c ≠ CHAIN0
  · apply guarded_preserves
    apply preserves_of_maintains
    simp only [Bind.bind, Pure.pure]
    ledger_pipeline_full
  · have hz : c = CHAIN0 := by
      by_cases he : c = CHAIN0
      · exact he
      · exact False.elim (hn he)
    intro s out hi hs
    by_cases hg : (s.readTransient 0).val = 0 <;>
      by_cases ha : env.authorizedForToken = true <;>
      simp [emergencyDeallocate, guarded, hz, hg, ha, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Verity.require, Contract.run, writeWord] at hs


def clearedAmounts (t : Uint256) : List Uint256 → ContractState → ContractState
  | [], s => s
  | c :: xs, s => clearedAmounts t xs (s.writeMapChain 3 [t.val,c.val] 0 0)

def clearedPositions (t : Uint256) : List Uint256 → ContractState → ContractState
  | [], s => s
  | c :: xs, s => clearedPositions t xs (s.writeMapChain 2 [t.val,c.val] 1 0)

theorem clear_amounts_eval (t : Uint256) (xs : List Uint256) (s : ContractState) :
    clearAmounts t xs s = .success () (clearedAmounts t xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c xs ih => simpa [clearAmounts, clearedAmounts, Verity.bind, Bind.bind, writeWord, amountKey] using ih _

theorem clear_positions_eval (t : Uint256) (xs : List Uint256) (s : ContractState) :
    clearPositions t xs s = .success () (clearedPositions t xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c xs ih => simpa [clearPositions, clearedPositions, Verity.bind, Bind.bind, writeWord, positionKey] using ih _

theorem cleared_amounts_fields (t : Uint256) (xs : List Uint256) (s : ContractState) :
    (∀ u, allocationChainIds (clearedAmounts t xs s) u = allocationChainIds s u) ∧
    (∀ u, tokenStates (clearedAmounts t xs s) u = tokenStates s u) ∧
    (∀ u d, allocationChainPositions (clearedAmounts t xs s) u d = allocationChainPositions s u d) ∧
    (∀ u d, allocationChainAmounts (clearedAmounts t xs s) u d =
      if u = t ∧ d ∈ xs then 0 else allocationChainAmounts s u d) := by
  induction xs generalizing s with
  | nil => simp [clearedAmounts]
  | cons c xs ih =>
    obtain ⟨hi, ht, hp, ha⟩ := ih (s.writeMapChain 3 [t.val,c.val] 0 0)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u; simpa [clearedAmounts, allocationChainIds, ContractState.readArray, ContractState.writeMapChain, ContractState.withStorageWords] using hi u
    · intro u; simpa [clearedAmounts, tokenStates] using ht u
    · intro u d; simpa [clearedAmounts, allocationChainPositions] using hp u d
    · intro u d
      rw [clearedAmounts, ha]
      by_cases hu : u = t
      · subst u
        by_cases hd : d = c
        · subst d; simp [allocationChainAmounts]
        · have hd' := Ne.symm hd
          by_cases hm : d ∈ xs <;> simp [allocationChainAmounts, hd, hd', hm]
      · have hu' := Ne.symm hu
        simp [allocationChainAmounts, hu, hu']

theorem cleared_positions_fields (t : Uint256) (xs : List Uint256) (s : ContractState) :
    (∀ u, allocationChainIds (clearedPositions t xs s) u = allocationChainIds s u) ∧
    (∀ u, tokenStates (clearedPositions t xs s) u = tokenStates s u) ∧
    (∀ u d, allocationChainAmounts (clearedPositions t xs s) u d = allocationChainAmounts s u d) ∧
    (∀ u d, allocationChainPositions (clearedPositions t xs s) u d =
      if u = t ∧ d ∈ xs then 0 else allocationChainPositions s u d) := by
  induction xs generalizing s with
  | nil => simp [clearedPositions]
  | cons c xs ih =>
    obtain ⟨hi, ht, ha, hp⟩ := ih (s.writeMapChain 2 [t.val,c.val] 1 0)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u; simpa [clearedPositions, allocationChainIds, ContractState.readArray, ContractState.writeMapChain, ContractState.withStorageWords] using hi u
    · intro u; simpa [clearedPositions, tokenStates] using ht u
    · intro u d; simpa [clearedPositions, allocationChainAmounts] using ha u d
    · intro u d
      rw [clearedPositions, hp]
      by_cases hu : u = t
      · subst u
        by_cases hd : d = c
        · subst d; simp [allocationChainPositions]
        · have hd' := Ne.symm hd
          by_cases hm : d ∈ xs <;> simp [allocationChainPositions, hd, hd', hm]
      · have hu' := Ne.symm hu
        simp [allocationChainPositions, hu, hu']


def clearLedger (t : Uint256) : Contract Unit := do
  let ids ← (fun s => .success (allocationChainIds s t) s : Contract (List Uint256))
  clearAmounts t ids
  setClear t
  writeWord (tokenKey t) 0

def clearedLedger (s : ContractState) (t : Uint256) : ContractState :=
  ((clearedPositions t (allocationChainIds s t) (clearedAmounts t (allocationChainIds s t) s)).writeArray
    t.val []).writeMapChain 4 [t.val] 0 0

theorem clear_ledger_eval (s : ContractState) (t : Uint256) :
    clearLedger t s = .success () (clearedLedger s t) := by
  have hid := (cleared_amounts_fields t (allocationChainIds s t) s).1 t
  simp [clearLedger, clearedLedger, clear_amounts_eval, clear_positions_eval, setClear,
    setValues, Verity.bind, Bind.bind, writeIds, writeWord, tokenKey, hid]

theorem cleared_ledger_fields (s : ContractState) (t : Uint256) :
    (∀ u, allocationChainIds (clearedLedger s t) u = if u = t then [] else allocationChainIds s u) ∧
    (∀ u, (tokenStates (clearedLedger s t) u).committed = if u = t then 0 else (tokenStates s u).committed) ∧
    (∀ u d, allocationChainAmounts (clearedLedger s t) u d =
      if u = t ∧ d ∈ allocationChainIds s t then 0 else allocationChainAmounts s u d) ∧
    (∀ u d, allocationChainPositions (clearedLedger s t) u d =
      if u = t ∧ d ∈ allocationChainIds s t then 0 else allocationChainPositions s u d) := by
  obtain ⟨hi, ht, hp, ha⟩ := cleared_amounts_fields t (allocationChainIds s t) s
  obtain ⟨hi', ht', ha', hp'⟩ := cleared_positions_fields t (allocationChainIds s t)
    (clearedAmounts t (allocationChainIds s t) s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    simp only [clearedLedger, allocationChainIds, ContractState.readArray,
      ContractState.writeMapChain, ContractState.withStorageWords, ContractState.writeArray]
    change (if u.val == t.val then [] else allocationChainIds
      (clearedPositions t (allocationChainIds s t) (clearedAmounts t (allocationChainIds s t) s)) u) = _
    by_cases hu : u = t
    · subst u; simp
    · have hu' := Ne.symm hu
      simp [hu, hu', hi', hi]
      rfl
  · intro u
    by_cases hu : u = t
    · subst u; simp [clearedLedger, tokenStates]
    · have hu' := Ne.symm hu
      simp [clearedLedger, tokenStates, hu, hu']
      exact congrArg TokenState.committed ((ht' u).trans (ht u))
  · intro u d
    simpa [clearedLedger, allocationChainAmounts] using (ha' u d).trans (ha u d)
  · intro u d
    have hf := hp' u d
    rw [hp] at hf
    simpa [clearedLedger, allocationChainPositions] using hf

theorem clear_ledger_preserves (t : Uint256) : preservesLedger (clearLedger t) := by
  intro s out hi hs
  have hh := (run_success_iff _ _ _ _).mp hs
  rw [clear_ledger_eval] at hh
  have ho : clearedLedger s t = out := (ContractResult.success.inj hh).2
  subst out
  obtain ⟨hids, hc, ha, hp⟩ := cleared_ledger_fields s t
  intro u
  by_cases hu : u = t
  · subst u
    have ham : ∀ d, allocationChainAmounts (clearedLedger s t) t d = 0 := by
      intro d
      rw [ha]
      by_cases hd : d ∈ allocationChainIds s t
      · simp [hd]
      · have hn := (hi t).2.1.2 d
        have hnzero : ¬ allocationChainAmounts s t d > 0 := fun h => hd (hn.mpr h)
        have hz : allocationChainAmounts s t d = 0 := by omega
        simp [hd, hz]
    have hpos : ∀ d, allocationChainPositions (clearedLedger s t) t d = 0 := by
      intro d
      rw [hp]
      by_cases hd : d ∈ allocationChainIds s t
      · simp [hd]
      · rw [(hi t).2.2.2.2.2 d]
        have hz := (expected_position_zero_iff (allocationChainIds s t) d).mpr hd
        simp [hd, hz]
    simp [allocationConserved, allocationSum, supportValid, allocationRange,
      setRepresentationValid, expectedPosition, hids, hc, ham, hpos, amountLimit]
  · have hidsu : allocationChainIds (clearedLedger s t) u = allocationChainIds s u := by simp [hids, hu]
    have hcu : (tokenStates (clearedLedger s t) u).committed = (tokenStates s u).committed := by simp [hc, hu]
    have hau : ∀ d, allocationChainAmounts (clearedLedger s t) u d = allocationChainAmounts s u d := by simp [ha, hu]
    have hpu : ∀ d, allocationChainPositions (clearedLedger s t) u d = allocationChainPositions s u d := by simp [hp, hu]
    simpa [allocationConserved, allocationSum, supportValid, allocationRange,
      setRepresentationValid, hidsu, hcu, hau, hpu] using hi u

theorem clear_token_preserves (env : Environment) (t : Uint256) : preservesLedger (clearToken env t) := by
  change preservesLedger (guarded (Verity.bind (onlyVotingEscrow env)
    (fun _ => Verity.bind (Verity.require (t != TOKEN0) "Token0NotClearable") (fun _ => clearLedger t))))
  apply guarded_preserves
  apply bind_preserves_ledger
  · apply preserves_of_maintains
    unfold onlyVotingEscrow
    apply maintains_bind
    · exact maintains_read _
    · intro _; exact maintains_require _ _
  · intro _
    apply bind_preserves_ledger
    · exact preserves_of_maintains _ (maintains_require _ _)
    · intro _; exact clear_ledger_preserves t

theorem entry_preserves (env : Environment) (entry : RootEntry) : preservesLedger (entryProgram env entry) := by
  cases entry with
  | allocateChains t xs => exact allocate_chains_preserves env t xs
  | allocate t xs nonempty checks => exact allocate_preserves env t xs nonempty checks
  | burn n => exact burn_preserves env n
  | rebalanceChain0 src dst => exact rebalance_preserves env src dst
  | processDeallocation r => exact process_deallocation_preserves env r
  | emergencyDeallocate t c suspended allowed gas => exact emergency_preserves env t c suspended allowed gas
  | parkOnChain0 t => exact park_preserves env t
  | clearToken t => exact clear_token_preserves env t
  | nonwriterWithReturns rs => exact nonwriter_preserves env rs

theorem reachable_ledger (s : ContractState) (h : Reachable s) : ledgerInvariant s := by
  induction h with
  | init hi => exact initialized_ledger hi
  | step env entry hbefore hs ih => exact entry_preserves env entry _ _ ih hs

-- Mechanically checked over the executable symbolic ledger model.
-- Source, physical-storage, bytecode and deployment correspondence are not proved.
theorem transaction_conservation : transactionConservation := by
  intro s hr t
  exact all_chain_interpretation_of_ledger (reachable_ledger s hr) t

#print axioms transaction_conservation
#print axioms clear_token_preserves

end Benchmark.Cases.Dromos.AllocationConservation
