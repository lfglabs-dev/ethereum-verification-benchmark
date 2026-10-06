import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.Specs
import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.AccountingLemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- The finite part of the allocation ledger assigned to one one-based fulfillment ID. -/
def allocationSumByFulfillment (xs : List Allocation) (fid : Nat)
    (weight : Allocation → Nat) : Nat :=
  ((xs.filter (fun a => a.fulfillmentId = fid)).map weight).sum

/-- A finite allocation ledger partitions by its valid one-based fulfillment IDs.
    Neither the number of fulfillments nor the number of allocations is bounded. -/
theorem allocation_sum_partition (xs : List Allocation) (n : Nat)
    (weight : Allocation → Nat)
    (hids : ∀ a ∈ xs, 0 < a.fulfillmentId ∧ a.fulfillmentId ≤ n) :
    (xs.map weight).sum =
      ∑ fid ∈ Finset.Icc 1 n, allocationSumByFulfillment xs fid weight := by
  induction xs with
  | nil => simp [allocationSumByFulfillment]
  | cons a rest ih =>
    have ha := hids a (by simp)
    have hrest : ∀ b ∈ rest, 0 < b.fulfillmentId ∧ b.fulfillmentId ≤ n := by
      intro b hb
      exact hids b (by simp [hb])
    have hstep :
        (∑ fid ∈ Finset.Icc 1 n, allocationSumByFulfillment (a :: rest) fid weight) =
          (∑ fid ∈ Finset.Icc 1 n, if a.fulfillmentId = fid then weight a else 0) +
          (∑ fid ∈ Finset.Icc 1 n, allocationSumByFulfillment rest fid weight) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro fid _
      by_cases h : a.fulfillmentId = fid <;>
        simp [allocationSumByFulfillment, h]
    have hmem : a.fulfillmentId ∈ Finset.Icc 1 n := by
      exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr ha.1, ha.2⟩
    have hsel :
        (∑ fid ∈ Finset.Icc 1 n, if a.fulfillmentId = fid then weight a else 0) =
          weight a := by
      rw [Finset.sum_ite_eq]
      simp [hmem]
    rw [List.map_cons, List.sum_cons, hstep, hsel, ← ih hrest]

/-- The preexisting fold-based accounting equals the filtered length sum. -/
theorem allocatedLengthByFulfillment_eq (s : QueueState) (fid : Nat) :
    allocatedLengthByFulfillment s fid =
      allocationSumByFulfillment s.allocations.toList fid Allocation.length := by
  have hfold (xs : List Allocation) (acc : Nat) :
      xs.foldl (fun total a =>
          if a.fulfillmentId = fid then total + a.length else total) acc =
        acc + allocationSumByFulfillment xs fid Allocation.length := by
    induction xs generalizing acc with
    | nil => simp [allocationSumByFulfillment]
    | cons a rest ih =>
      by_cases h : a.fulfillmentId = fid
      · simp only [List.foldl_cons, h, ↓reduceIte]
        rw [ih]
        simp [allocationSumByFulfillment, h]
        omega
      · simp only [List.foldl_cons, h, ↓reduceIte]
        rw [ih]
        simp [allocationSumByFulfillment, h]
  simpa only [allocatedLengthByFulfillment, Nat.zero_add] using
    hfold s.allocations.toList 0

/-- Explicit finite ledger conditions. These are AUXILIARY mathematical premises,
    not guards of `Contract.lean` or assumptions of the headline history theorem.
    Source-transition preservation must derive every clause. -/
def LedgerValid (s : QueueState) : Prop :=
  (∀ a ∈ s.allocations.toList,
    0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size ∧
      a.nominalPayout ≤ a.length *
        (s.fulfillments[a.fulfillmentId - 1]!).amountOut /
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn) ∧
  (∀ fid, 0 < fid → fid ≤ s.fulfillments.size →
    0 < (s.fulfillments[fid - 1]!).filledAmountIn ∧
      allocatedLengthByFulfillment s fid ≤
        (s.fulfillments[fid - 1]!).filledAmountIn)

/-- Each fulfillment's associated payouts fit within its nominal amountOut. -/
theorem allocation_sum_by_fulfillment_le (s : QueueState) (h : LedgerValid s)
    (fid : Nat) (hfid : 0 < fid) (hfid' : fid ≤ s.fulfillments.size) :
    allocationSumByFulfillment s.allocations.toList fid Allocation.nominalPayout ≤
      (s.fulfillments[fid - 1]!).amountOut := by
  let xs := s.allocations.toList.filter (fun a => a.fulfillmentId = fid)
  let A := (s.fulfillments[fid - 1]!).amountOut
  let L := (s.fulfillments[fid - 1]!).filledAmountIn
  have hf := h.2 fid hfid hfid'
  have hxs : (xs.map Allocation.length).sum ≤ L := by
    change allocationSumByFulfillment s.allocations.toList fid Allocation.length ≤ L
    rw [← allocatedLengthByFulfillment_eq]
    exact hf.2
  have hentry : ∀ a ∈ xs, a.nominalPayout ≤ a.length * A / L := by
    intro a ha
    have ha' : a ∈ s.allocations.toList := List.mem_of_mem_filter ha
    have hid : a.fulfillmentId = fid := by
      simpa using (List.mem_filter.mp ha).2
    simpa only [A, L, hid] using (h.1 a ha').2.2
  calc
    allocationSumByFulfillment s.allocations.toList fid Allocation.nominalPayout =
        (xs.map Allocation.nominalPayout).sum := rfl
    _ ≤ (xs.map (fun a => a.length * A / L)).sum := List.sum_le_sum hentry
    _ ≤ A := by
      simpa only [List.map_map, Function.comp_def] using
        AccountingLemmas.floor_list_sum_le (xs.map Allocation.length) A L hf.1 hxs

/-- Reindex the immutable fulfillment array from zero-based storage indices to IDs. -/
theorem fulfillment_sum_one_based (fs : Array Fulfillment) :
    (∑ fid ∈ Finset.Icc 1 fs.size, (fs[fid - 1]!).amountOut) =
      (fs.toList.map Fulfillment.amountOut).sum := by
  have hshift (n : Nat) (f : Nat → Nat) :
      (∑ fid ∈ Finset.Icc 1 n, f (fid - 1)) = ∑ i ∈ Finset.range n, f i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      simp
  have hlist (ys : List Fulfillment) :
      (∑ i ∈ Finset.range ys.length, (ys[i]!).amountOut) =
        (ys.map Fulfillment.amountOut).sum := by
    induction ys using List.reverseRecOn with
    | nil => simp
    | append_singleton ys y ih =>
      have hpre :
          (∑ i ∈ Finset.range ys.length, ((ys ++ [y])[i]!).amountOut) =
            ∑ i ∈ Finset.range ys.length, (ys[i]!).amountOut := by
        apply Finset.sum_congr rfl
        intro i hi
        have hlt := Finset.mem_range.mp hi
        have hget : (ys ++ [y])[i]! = ys[i]! := by
          simp only [List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left hlt]
        exact congrArg Fulfillment.amountOut hget
      have hlast : (ys ++ [y])[ys.length]! = y := by simp
      simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
      rw [hpre, hlast, ih]
      simp [List.map_append, List.sum_append]
  have hreindex := hshift fs.size (fun i => (fs[i]!).amountOut)
  change (∑ fid ∈ Finset.Icc 1 fs.size, (fs[fid - 1]!).amountOut) =
    ∑ i ∈ Finset.range fs.size, (fs[i]!).amountOut at hreindex
  rw [hreindex]
  have hsize : fs.toList.length = fs.size := by simp
  rw [← hsize]
  calc
    (∑ i ∈ Finset.range fs.toList.length, (fs[i]!).amountOut) =
        ∑ i ∈ Finset.range fs.toList.length, (fs.toList[i]!).amountOut := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg Fulfillment.amountOut
        (Array.getElem!_toList (xs := fs) (i := i)).symm
    _ = (fs.toList.map Fulfillment.amountOut).sum := hlist fs.toList

/-- Conditional arithmetic ledger theorem, not the reachable-queue theorem. -/
theorem ledger_valid_nominalConservation (s : QueueState) (h : LedgerValid s) :
    nominalConservation s := by
  have hids : ∀ a ∈ s.allocations.toList,
      0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size := by
    intro a ha
    exact ⟨(h.1 a ha).1, (h.1 a ha).2.1⟩
  have hg :
      (∑ fid ∈ Finset.Icc 1 s.fulfillments.size,
        allocationSumByFulfillment s.allocations.toList fid Allocation.nominalPayout) ≤
      ∑ fid ∈ Finset.Icc 1 s.fulfillments.size,
        (s.fulfillments[fid - 1]!).amountOut := by
    apply Finset.sum_le_sum
    intro fid hfid
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hfid
    exact allocation_sum_by_fulfillment_le s h fid (by omega) hhi
  have hredeem : cumulativeNominalRedeem s =
      (s.allocations.toList.map Allocation.nominalPayout).sum := by
    simp only [cumulativeNominalRedeem, List.sum_eq_foldl, List.foldl_map]
  have hfulfill : cumulativeNominalFulfill s =
      (s.fulfillments.toList.map Fulfillment.amountOut).sum := by
    simp only [cumulativeNominalFulfill, List.sum_eq_foldl, List.foldl_map]
  unfold nominalConservation
  rw [hredeem, hfulfill,
    allocation_sum_partition s.allocations.toList s.fulfillments.size
      Allocation.nominalPayout hids, ← fulfillment_sum_one_based]
  exact hg

/-- Unpack the source prover's obligations into the conditional ledger premise.
    In particular, `fulfillmentIntervalsNotDoubleSpent` must itself be derived
    from source updates; it is not a condition on calls or finite histories. -/
theorem ledgerValid_of_source_obligations (s : QueueState)
    (hids : ∀ a ∈ s.allocations.toList,
      0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size)
    (hpayout : ∀ a ∈ s.allocations.toList,
      a.nominalPayout ≤ a.length *
        (s.fulfillments[a.fulfillmentId - 1]!).amountOut /
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn)
    (hpositive : ∀ fid, 0 < fid → fid ≤ s.fulfillments.size →
      0 < (s.fulfillments[fid - 1]!).filledAmountIn)
    (hcapacity : fulfillmentIntervalsNotDoubleSpent s) : LedgerValid s := by
  constructor
  · intro a ha
    exact ⟨(hids a ha).1, (hids a ha).2, hpayout a ha⟩
  · intro fid hlo hhi
    exact ⟨hpositive fid hlo hhi, hcapacity fid hlo hhi⟩

/-- Appending a ghost allocation increments the nominal redeem ledger exactly. -/
theorem cumulativeNominalRedeem_push (s : QueueState) (a : Allocation) :
    cumulativeNominalRedeem {s with allocations := s.allocations.push a} =
      cumulativeNominalRedeem s + a.nominalPayout := by
  simp [cumulativeNominalRedeem, List.foldl_append]

/-- Appending a fulfillment increments the nominal fulfillment ledger exactly. -/
theorem cumulativeNominalFulfill_push (s : QueueState) (f : Fulfillment) :
    cumulativeNominalFulfill {s with fulfillments := s.fulfillments.push f} =
      cumulativeNominalFulfill s + f.amountOut := by
  simp [cumulativeNominalFulfill, List.foldl_append]

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
