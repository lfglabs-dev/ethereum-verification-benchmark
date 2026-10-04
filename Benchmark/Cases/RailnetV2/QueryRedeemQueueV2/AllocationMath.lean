import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.IntervalLemmas
import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.LedgerLemmas
import Mathlib.Tactic

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Pure geometry: a pairwise-disjoint subset of allocations contained in a
single fulfillment interval consumes at most that interval's width. Both
premises remain source-transition proof obligations, not execution guards. -/
theorem filtered_allocation_width_le (xs : List Allocation)
    (fid p L : Nat)
    (hsep : xs.Pairwise (fun a b : Allocation =>
      a.start + a.length ≤ b.start ∨ b.start + b.length ≤ a.start))
    (hinside : ∀ a ∈ xs, a.fulfillmentId = fid →
      p ≤ a.start ∧ a.start + a.length ≤ p + L) :
    allocationSumByFulfillment xs fid Allocation.length ≤ L := by
  let selected := xs.filter (fun a => a.fulfillmentId = fid)
  let intervals := selected.map (fun a => (a.start, a.length))
  have hselected : selected.Pairwise (fun a b : Allocation =>
      a.start + a.length ≤ b.start ∨ b.start + b.length ≤ a.start) :=
    hsep.filter _
  have hsep' : intervals.Pairwise IntervalLemmas.separated := by
    apply List.Pairwise.map (fun a : Allocation => (a.start, a.length))
      (fun a b hab => ?_) hselected
    exact hab
  have hstart : ∀ z ∈ intervals, p ≤ z.1 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact (hinside a (List.mem_of_mem_filter ha)
      (by simpa using (List.mem_filter.mp ha).2)).1
  have hend : ∀ z ∈ intervals, z.1 + z.2 ≤ p + L := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact (hinside a (List.mem_of_mem_filter ha)
      (by simpa using (List.mem_filter.mp ha).2)).2
  have h := IntervalLemmas.sum_widths_le_offset intervals p L hsep' hstart hend
  simpa only [allocationSumByFulfillment, intervals, selected, List.map_map,
    Function.comp_def] using h

/-- Derive the source-shaped per-fulfillment no-double-spend predicate once
actual transition induction establishes disjointness and containment. -/
theorem noDoubleSpend_of_disjoint_contained (s : QueueState)
    (hsep : disjointAllocations s)
    (hinside : ∀ a ∈ s.allocations.toList,
      0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size ∧
      (s.fulfillments[a.fulfillmentId - 1]!).position ≤ a.start ∧
      a.start + a.length ≤ (s.fulfillments[a.fulfillmentId - 1]!).position +
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn) :
    fulfillmentIntervalsNotDoubleSpent s := by
  intro fid hfid hvalid
  rw [allocatedLengthByFulfillment_eq]
  apply filtered_allocation_width_le _ _ _ _ hsep
  intro a ha hid
  obtain ⟨_, _, hstart, hend⟩ := hinside a ha
  simpa only [hid] using And.intro hstart hend

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
