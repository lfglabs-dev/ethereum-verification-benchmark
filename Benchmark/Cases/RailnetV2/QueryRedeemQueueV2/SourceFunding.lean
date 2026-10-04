import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.SourceTransitionBasics
import Mathlib.Tactic

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Each funding interval is nonempty and each ghost entry lies inside its
immutable source fulfillment and respects its per-piece Math.mulDiv floor. -/
def SourceFundingSafe (s : QueueState) : Prop :=
  (∀ fid : Nat, 0 < fid → fid ≤ s.fulfillments.size →
    0 < (s.fulfillments[fid - 1]!).filledAmountIn) ∧
  (∀ a ∈ s.allocations.toList,
    0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size ∧
    (s.fulfillments[a.fulfillmentId - 1]!).position ≤ a.start ∧
    a.start + a.length ≤
      (s.fulfillments[a.fulfillmentId - 1]!).position +
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn ∧
    a.nominalPayout ≤ a.length *
      (s.fulfillments[a.fulfillmentId - 1]!).amountOut /
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn)

/-- Assembling the ALREADY-PROVED finite ledger theorem needs no extra
history condition once the actual source induction has established geometry
and funding. The antecedent is an internal inductive proof invariant, not a
premise of the requested headline theorem. -/
theorem conservation_of_geometry_and_funding (s : QueueState)
    (hgeometry : SourceGeometrySafe s) (hfunding : SourceFundingSafe s) :
    nominalConservation s := by
  obtain ⟨_, _, hpairwise⟩ := hgeometry
  obtain ⟨hpositive, hentry⟩ := hfunding
  have hinside : ∀ a ∈ s.allocations.toList,
      0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size ∧
      (s.fulfillments[a.fulfillmentId - 1]!).position ≤ a.start ∧
      a.start + a.length ≤ (s.fulfillments[a.fulfillmentId - 1]!).position +
        (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn := by
    intro a ha
    obtain ⟨hid, hsize, hstart, hend, _⟩ := hentry a ha
    exact ⟨hid, hsize, hstart, hend⟩
  have hcapacity := noDoubleSpend_of_disjoint_contained s hpairwise hinside
  apply ledger_valid_nominalConservation s
  apply ledgerValid_of_source_obligations s
  · intro a ha
    exact ⟨(hentry a ha).1, (hentry a ha).2.1⟩
  · intro a ha
    exact (hentry a ha).2.2.2.2
  · exact hpositive
  · exact hcapacity

/-- Empty initialized ledgers have the funding invariant. -/
theorem empty_funding (s : QueueState) (hf : s.fulfillments = #[])
    (ha : s.allocations = #[]) : SourceFundingSafe s := by
  constructor
  · intro fid hlo hhi
    simp [hf] at hhi
    omega
  · intro a ha'
    simp [ha] at ha'

/-- A source fulfillment append keeps all earlier funding intervals immutable.
Its only new arithmetic requirement is the source's nonzero input check. -/
theorem funding_push_fulfillment (s : QueueState) (h : SourceFundingSafe s)
    (f : Fulfillment) (hf : 0 < f.filledAmountIn) :
    SourceFundingSafe {s with fulfillments := s.fulfillments.push f} := by
  rcases h with ⟨hpositive, hentry⟩
  constructor
  · intro fid hlo hhi
    have hhi' : fid ≤ s.fulfillments.size + 1 := by
      simpa only [Array.size_push] using hhi
    have hidx : fid - 1 < s.fulfillments.size + 1 :=
      (Nat.sub_lt hlo (by decide)).trans_le hhi'
    by_cases hlast : fid - 1 = s.fulfillments.size
    · simpa only [hlast, get_push_new s.fulfillments f] using hf
    · have hbefore : fid ≤ s.fulfillments.size := by omega
      have hi : fid - 1 < s.fulfillments.size :=
        (Nat.sub_lt hlo (by decide)).trans_le hbefore
      simpa only [get_push_old s.fulfillments (fid - 1) f hi] using
        hpositive fid hlo hbefore
  · intro a ha
    obtain ⟨hlo, hhi, hstart, hend, hpayout⟩ := hentry a ha
    have hi : a.fulfillmentId - 1 < s.fulfillments.size :=
      (Nat.sub_lt hlo (by decide)).trans_le hhi
    refine ⟨hlo, ?_, ?_, ?_, ?_⟩
    · simpa only [Array.size_push] using (Nat.le_succ_of_le hhi)
    · simpa only [get_push_old s.fulfillments (a.fulfillmentId - 1) f hi] using hstart
    · simpa only [get_push_old s.fulfillments (a.fulfillmentId - 1) f hi] using hend
    · simpa only [get_push_old s.fulfillments (a.fulfillmentId - 1) f hi] using hpayout

/-- Source's single checked allocation append preserves every earlier payout
and containment record; its NEW record must be checked against the selected
real fulfillment. This theorem does not assume a payout budget or sum bound. -/
theorem funding_push_allocation (s : QueueState) (h : SourceFundingSafe s)
    (a : Allocation)
    (hnew : 0 < a.fulfillmentId ∧ a.fulfillmentId ≤ s.fulfillments.size ∧
      (s.fulfillments[a.fulfillmentId - 1]!).position ≤ a.start ∧
      a.start + a.length ≤
        (s.fulfillments[a.fulfillmentId - 1]!).position +
          (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn ∧
      a.nominalPayout ≤ a.length *
        (s.fulfillments[a.fulfillmentId - 1]!).amountOut /
          (s.fulfillments[a.fulfillmentId - 1]!).filledAmountIn) :
    SourceFundingSafe {s with allocations := s.allocations.push a} := by
  rcases h with ⟨hpositive, hentry⟩
  constructor
  · exact hpositive
  · intro b hb
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hentry b hb
    · exact hnew

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
