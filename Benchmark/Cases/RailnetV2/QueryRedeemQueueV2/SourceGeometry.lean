import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.AllocationMath
import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.SourceArrays

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Existing demands' current ends stay before later demands' current starts.
The source append and consumption steps must establish/preserve this predicate. -/
def OrderedDemandEnds (s : QueueState) : Prop :=
  ∀ i j : Nat, i < j → j < s.demands.size →
    (s.demands[i]!).position + (s.demands[i]!).amountIn ≤
      (s.demands[j]!).position

/-- Logical provenance of every already consumed interval. This is a ghost
proof predicate, not a source guard: the recorded demand is valid, its
allocation finishes before the demand's current cursor, and earlier demands'
ends precede this allocation's start. -/
def AllocationHistoryBounds (s : QueueState) : Prop :=
  ∀ b ∈ s.allocations.toList,
    0 < b.demandId ∧ b.demandId ≤ s.demands.size ∧
    b.start + b.length ≤ (s.demands[b.demandId - 1]!).position ∧
    ∀ i : Nat, i < b.demandId - 1 →
      (s.demands[i]!).position + (s.demands[i]!).amountIn ≤ b.start

/-- A freshly consumed prefix of demand `j` is separated from every old
allocation, regardless of the order in which demands were redeemed. Its
endpoint need only fit in its CURRENT demand interval, not uint256 globally. -/
theorem fresh_prefix_separated (s : QueueState)
    (horder : OrderedDemandEnds s)
    (hledger : AllocationHistoryBounds s)
    (j : Nat) (hj : j < s.demands.size)
    (width : Nat) (hwidth : width ≤ (s.demands[j]!).amountIn)
    (old : Allocation) (hold : old ∈ s.allocations.toList) :
    old.start + old.length ≤ (s.demands[j]!).position ∨
      (s.demands[j]!).position + width ≤ old.start := by
  obtain ⟨hpositive, hvalid, hconsumed, hbefore⟩ := hledger old hold
  have hminus : old.demandId - 1 + 1 = old.demandId :=
    Nat.sub_add_cancel hpositive
  by_cases hlow : old.demandId ≤ j
  · have hi : old.demandId - 1 < j :=
      (Nat.sub_lt hpositive (by decide)).trans_le hlow
    have ho := horder (old.demandId - 1) j hi hj
    left
    have hle : (s.demands[old.demandId - 1]!).position ≤
        (s.demands[old.demandId - 1]!).position +
          (s.demands[old.demandId - 1]!).amountIn := Nat.le_add_right _ _
    exact hconsumed.trans (hle.trans ho)
  · by_cases heq : old.demandId = j + 1
    · left
      have hidx : old.demandId - 1 = j := by simp [heq]
      simpa only [hidx] using hconsumed
    · right
      have hp : j < old.demandId := Nat.lt_of_not_ge hlow
      have hle : j + 1 ≤ old.demandId := Nat.succ_le_iff.mpr hp
      have hgt : j + 1 < old.demandId :=
        Nat.lt_of_le_of_ne hle (Ne.symm heq)
      have hle' : j + 1 + 1 ≤ old.demandId := Nat.succ_le_iff.mpr hgt
      have hji : j < old.demandId - 1 := by
        apply Nat.lt_of_succ_le
        exact Nat.le_sub_of_add_le (by simpa [Nat.succ_eq_add_one, add_assoc] using hle')
      have hbefore' := hbefore j hji
      exact (Nat.add_le_add_left hwidth _).trans hbefore'

/-- The global pairwise ledger extends by the newly consumed prefix. Nothing
about one particular last redeemer, limited history, or funded asset budget
is assumed. The source iteration must produce `hwidth`. -/
theorem pairwise_push_fresh_prefix (s : QueueState)
    (horder : OrderedDemandEnds s)
    (hledger : AllocationHistoryBounds s)
    (hsep : disjointAllocations s)
    (j : Nat) (hj : j < s.demands.size)
    (width fid payout : Nat)
    (hwidth : width ≤ (s.demands[j]!).amountIn) :
    (s.allocations.push ⟨j + 1, fid, (s.demands[j]!).position,
        width, payout⟩).toList.Pairwise
      (fun a b : Allocation =>
        a.start + a.length ≤ b.start ∨ b.start + b.length ≤ a.start) := by
  rw [Array.toList_push, List.pairwise_append]
  refine ⟨hsep, ?_, ?_⟩
  · simp
  · intro old hold new hnew
    simp only [List.mem_singleton] at hnew
    subst new
    exact fresh_prefix_separated s horder hledger j hj width hwidth old hold

/-- A source redeem step preserves the demand endpoint, even if that
endpoint is larger than maxWord (creation does not check the new endpoint). -/
theorem consumed_demand_end (d : Demand) (width : Nat)
    (hwidth : width ≤ d.amountIn) :
    (d.position + width) + (d.amountIn - width) = d.position + d.amountIn := by
  calc
    d.position + width + (d.amountIn - width) =
        d.position + ((d.amountIn - width) + width) := by ac_rfl
    _ = d.position + d.amountIn := by rw [Nat.sub_add_cancel hwidth]

/-- Updating one demand's cursor and remaining amount leaves the ordering of
ALL current demand intervals intact. No bound on the array size is involved. -/
theorem ordered_ends_consume (s : QueueState) (horder : OrderedDemandEnds s)
    (j : Nat) (hj : j < s.demands.size) (width cap hint : Nat)
    (hw : width ≤ (s.demands[j]!).amountIn) :
    OrderedDemandEnds { s with demands := (s.demands.set! j
      ({ position := (s.demands[j]!).position + width,
         amountIn := (s.demands[j]!).amountIn - width,
         maxAmountOut := cap, highestFulfillmentId := hint } : Demand)) } := by
  let d := s.demands[j]!
  let d' : Demand := ⟨d.position + width, d.amountIn - width, cap, hint⟩
  have hend : d'.position + d'.amountIn = d.position + d.amountIn :=
    consumed_demand_end d width hw
  change OrderedDemandEnds {s with demands := s.demands.set! j d'}
  intro i k hik hk
  have hk' : k < s.demands.size := by simpa only [size_set_bang] using hk
  have hi' : i < s.demands.size := hik.trans hk'
  have hprev := horder i k hik hk'
  by_cases hij : i = j
  · have hkj : k ≠ j := by omega
    simpa only [hij, get_set_bang_self s.demands j d' hj,
      get_set_bang_ne s.demands j k d' (Ne.symm hkj), hend] using hprev
  · by_cases hkj : k = j
    · have hpos : d.position ≤ d'.position := Nat.le_add_right _ _
      have hprev' : (s.demands[i]!).position + (s.demands[i]!).amountIn ≤
        d.position := by simpa only [hkj] using hprev
      simpa only [get_set_bang_ne s.demands j i d' (Ne.symm hij),
        hkj, get_set_bang_self s.demands j d' hj] using hprev'.trans hpos
    · simpa only [get_set_bang_ne s.demands j i d' (Ne.symm hij),
        get_set_bang_ne s.demands j k d' (Ne.symm hkj)] using hprev

/-- The ghost provenance clauses survive one prefix consumption, including
when other demands have already been redeemed in arbitrary order. -/
theorem history_bounds_consume (s : QueueState)
    (horder : OrderedDemandEnds s)
    (hledger : AllocationHistoryBounds s)
    (j : Nat) (hj : j < s.demands.size) (width fid payout cap hint : Nat)
    (hw : width ≤ (s.demands[j]!).amountIn) :
    AllocationHistoryBounds
      { s with
        demands := s.demands.set! j
          ({ position := (s.demands[j]!).position + width,
             amountIn := (s.demands[j]!).amountIn - width,
             maxAmountOut := cap, highestFulfillmentId := hint } : Demand),
        allocations := s.allocations.push
          ⟨j + 1, fid, (s.demands[j]!).position, width, payout⟩ } := by
  let d := s.demands[j]!
  let d' : Demand := ⟨d.position + width, d.amountIn - width, cap, hint⟩
  let a : Allocation := ⟨j + 1, fid, d.position, width, payout⟩
  have hend : d'.position + d'.amountIn = d.position + d.amountIn :=
    consumed_demand_end d width hw
  change AllocationHistoryBounds
    {s with demands := s.demands.set! j d', allocations := s.allocations.push a}
  intro b hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hold | rfl
  · obtain ⟨hpos, hvalid, hconsumed, hbefore⟩ := hledger b hold
    have hsize : (s.demands.set! j d').size = s.demands.size := size_set_bang _ _ _
    refine ⟨hpos, by simpa only [hsize] using hvalid, ?_, ?_⟩
    · by_cases hindex : b.demandId - 1 = j
      · have hle : d.position ≤ d'.position := Nat.le_add_right _ _
        have hprev : b.start + b.length ≤ d.position := by
          simpa only [hindex] using hconsumed
        simpa only [hindex, get_set_bang_self s.demands j d' hj] using
          hprev.trans hle
      · simpa only [get_set_bang_ne s.demands j (b.demandId - 1) d'
          (Ne.symm hindex)] using hconsumed
    · intro i hi
      by_cases hij : i = j
      · have hprev := hbefore i hi
        simpa only [hij, get_set_bang_self s.demands j d' hj, hend] using hprev
      · simpa only [get_set_bang_ne s.demands j i d' (Ne.symm hij)] using
          hbefore i hi
  · have hindex : a.demandId - 1 = j := by simp [a]
    refine ⟨by simp [a], ?_, ?_, ?_⟩
    · simpa only [a, size_set_bang] using (Nat.succ_le_iff.mpr hj)
    · rw [hindex, get_set_bang_self s.demands j d' hj]
    · intro i hi
      rw [hindex] at hi
      have hn : j ≠ i := Ne.symm (Nat.ne_of_lt hi)
      have hp := horder i j hi hj
      rw [get_set_bang_ne s.demands j i d' hn]
      change (s.demands[i]!).position + (s.demands[i]!).amountIn ≤ d.position
      exact hp

/-- The source's next demand position dominates all earlier demand ends,
not just the immediately previous one. -/
theorem end_le_append_position (s : QueueState) (horder : OrderedDemandEnds s)
    (i : Nat) (hi : i < s.demands.size) :
    (s.demands[i]!).position + (s.demands[i]!).amountIn ≤
      (if s.demands.isEmpty then 0 else
        s.demands.back!.position + s.demands.back!.amountIn) := by
  have hpos : 0 < s.demands.size := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hne : s.demands.isEmpty = false := by
    cases h : s.demands.isEmpty
    · rfl
    · have hempty : s.demands = #[] := Array.isEmpty_iff.mp h
      simp [hempty] at hpos
  simp only [hne, Bool.false_eq_true, ↓reduceIte, back_bang_eq_get s.demands hpos]
  by_cases hlast : i = s.demands.size - 1
  · rw [hlast]
  · have hilast : i < s.demands.size - 1 := by omega
    have hlastBound : s.demands.size - 1 < s.demands.size := by omega
    have hprev := horder i (s.demands.size - 1) hilast hlastBound
    exact hprev.trans (Nat.le_add_right _ _)

/-- The source demand append maintains the global ordered endpoint relation
for arbitrary demand-count histories; freshly appended endpoints need not fit
a word until they are used by a checked source operation. -/
theorem ordered_ends_push (s : QueueState) (horder : OrderedDemandEnds s)
    (position amount cap hint : Nat)
    (hposition : position = if s.demands.isEmpty then 0 else
      s.demands.back!.position + s.demands.back!.amountIn) :
    OrderedDemandEnds {s with demands :=
      (s.demands.push (Demand.mk position amount cap hint))} := by
  let d : Demand := ⟨position, amount, cap, hint⟩
  change OrderedDemandEnds {s with demands := s.demands.push d}
  intro i j hij hj
  have hj' : j < s.demands.size + 1 := by
    simpa only [Array.size_push] using hj
  by_cases hjnew : j = s.demands.size
  · have hi : i < s.demands.size := by omega
    rw [hjnew, get_push_new s.demands d, get_push_old s.demands i d hi]
    exact (end_le_append_position s horder i hi).trans_eq hposition.symm
  · have hi : i < s.demands.size := by omega
    have hjold : j < s.demands.size := by omega
    simpa only [get_push_old s.demands i d hi,
      get_push_old s.demands j d hjold] using horder i j hij hjold

/-- Appending a new demand at the preceding endpoint cannot invalidate
already-consumed provenance; no earlier demand is rewritten. -/
theorem history_bounds_push (s : QueueState)
    (hledger : AllocationHistoryBounds s)
    (position amount cap hint : Nat) :
    AllocationHistoryBounds {s with demands :=
      (s.demands.push (Demand.mk position amount cap hint))} := by
  let d : Demand := ⟨position, amount, cap, hint⟩
  change AllocationHistoryBounds {s with demands := s.demands.push d}
  intro b hb
  obtain ⟨hpos, hvalid, hconsumed, hbefore⟩ := hledger b hb
  have hidx : b.demandId - 1 < s.demands.size :=
    (Nat.sub_lt hpos (by decide)).trans_le hvalid
  refine ⟨hpos, ?_, ?_, ?_⟩
  · simpa only [Array.size_push] using hvalid.trans (Nat.le_add_right _ _)
  · simpa only [get_push_old s.demands (b.demandId - 1) d hidx] using hconsumed
  · intro i hi
    have hsmall : i < s.demands.size := hi.trans hidx
    simpa only [get_push_old s.demands i d hsmall] using hbefore i hi

/-- No geometric invariant is necessary before the successful one-time
initializer: all three arrays are empty. -/
theorem initialized_empty_geometry (s : QueueState)
    (hd : s.demands = #[]) (ha : s.allocations = #[]) :
    OrderedDemandEnds s ∧ AllocationHistoryBounds s ∧ disjointAllocations s := by
  constructor
  · intro i j hij hj
    simp [hd] at hj
  constructor
  · intro b hb
    simp [ha] at hb
  · simp [disjointAllocations, ha]

/-- The strengthened geometry sufficient for arbitrary-order source-prefix
allocations. It is a poststate proof predicate, never checked by execution. -/
def SourceGeometrySafe (s : QueueState) : Prop :=
  OrderedDemandEnds s ∧ AllocationHistoryBounds s ∧ disjointAllocations s

/-- Proof-only definitional extraction of the two source array writes; it
adds no check and is not called by the executable implementation. -/
def geometryStep (s : QueueState) (j width fid payout cap hint : Nat) : QueueState :=
  let d := s.demands[j]!
  let d' : Demand := ⟨d.position + width, d.amountIn - width, cap, hint⟩
  let a : Allocation := ⟨j + 1, fid, d.position, width, payout⟩
  {s with demands := s.demands.set! j d', allocations := s.allocations.push a}

/-- Abstract local form of the exact source write in one successful matching
loop iteration. All its premises concern the PRESTATE geometry and the width
computed by the source checks, not a funded-payout budget. -/
theorem source_geometry_consumption (s : QueueState)
    (h : SourceGeometrySafe s) (j : Nat) (hj : j < s.demands.size)
    (width fid payout cap hint : Nat)
    (hw : width ≤ (s.demands[j]!).amountIn) :
    SourceGeometrySafe (geometryStep s j width fid payout cap hint) := by
  rcases h with ⟨horder, hledger, hsep⟩
  exact ⟨ordered_ends_consume s horder j hj width cap hint hw,
    history_bounds_consume s horder hledger j hj width fid payout cap hint hw,
    pairwise_push_fresh_prefix s horder hledger hsep j hj width fid payout hw⟩

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
