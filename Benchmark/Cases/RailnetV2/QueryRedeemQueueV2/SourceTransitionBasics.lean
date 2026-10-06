import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.SourceGeometry
import Mathlib.Tactic

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- A successful array dereference carries the real checked one-based ID. -/
theorem valid_demand_ok {s : QueueState} {id : Nat} {d : Demand}
    (h : validDemand s id = .ok d) :
    0 < id ∧ id ≤ s.demands.size ∧ d = s.demands[id - 1]! := by
  cases hv : _isValidDemandId s id with
  | false =>
    simp only [validDemand, hv, Bool.not_false, ↓reduceIte] at h
    change Except.error "InvalidDemandId" = Except.ok d at h
    cases h
  | true =>
    have hids : 0 < id ∧ id ≤ s.demands.size := by
      simpa [_isValidDemandId] using hv
    simp only [validDemand, hv, Bool.not_true, ↓reduceIte] at h
    change Except.ok s.demands[id - 1]! = Except.ok d at h
    exact ⟨hids.1, hids.2, (Except.ok.inj h).symm⟩

theorem valid_fulfillment_ok {s : QueueState} {id : Nat} {f : Fulfillment}
    (h : validFulfillment s id = .ok f) :
    0 < id ∧ id ≤ s.fulfillments.size ∧ f = s.fulfillments[id - 1]! := by
  cases hv : (id > 0 && id ≤ s.fulfillments.size) with
  | false =>
    simp only [validFulfillment, hv, Bool.not_false, ↓reduceIte] at h
    change Except.error "InvalidFulfillmentId" = Except.ok f at h
    cases h
  | true =>
    have hids : 0 < id ∧ id ≤ s.fulfillments.size := by
      simpa using hv
    simp only [validFulfillment, hv, Bool.not_true, ↓reduceIte] at h
    change Except.ok s.fulfillments[id - 1]! = Except.ok f at h
    exact ⟨hids.1, hids.2, (Except.ok.inj h).symm⟩

/-- Checked source arithmetic turns success into equalities and inequalities,
with no global endpoint bound added to the invariant. -/
theorem checked_add_ok {x y z : Nat} (h : checkedAdd x y = .ok z) :
    z = x + y ∧ z ≤ maxWord := by
  unfold checkedAdd checkedWord at h
  split at h
  · rename_i hb
    simp at h
    exact ⟨h.symm, by simpa only [h] using hb⟩
  · simp at h

theorem checked_sub_ok {x y z : Nat} (h : checkedSub x y = .ok z) :
    y ≤ x ∧ z = x - y := by
  unfold checkedSub at h
  split at h
  · rename_i hb
    simp at h
    exact ⟨hb, h.symm⟩
  · simp at h

theorem mul_div_floor_ok {x A L z : Nat}
    (h : mulDivFloor x A L = .ok z) :
    0 < L ∧ z = x * A / L := by
  unfold mulDivFloor at h
  by_cases hz : L = 0
  · simp [hz] at h
  · simp only [hz, ↓reduceIte] at h
    unfold checkedWord at h
    split at h
    · simp at h
      exact ⟨Nat.pos_of_ne_zero hz, h.symm⟩
    · simp at h

/-- The checked matching test entails membership of the demand cursor in
the actual immutable fulfillment interval, not an assumed budget condition. -/
theorem matching_ok {p : Nat} {f : Fulfillment}
    (h : _isMatchingFulfillment p f = .ok true) :
    f.position ≤ p ∧ p < f.position + f.filledAmountIn := by
  unfold _isMatchingFulfillment at h
  cases hend : checkedAdd f.position f.filledAmountIn
  next msg => simp [hend] at h
  next endpoint =>
    simp [hend] at h
    have heq := (checked_add_ok hend).1
    simpa only [heq] using h

/-- The literal, explicitly unrolled source iteration either stops without
allocating or appends exactly one checked nominal ledger event. This is a
transition theorem, not an assertion that the event is funded yet. -/
theorem redeem_one_allocation_shape (id len : Nat) (c out : RedeemCursor)
    (h : _redeemOne id len c = .ok out) :
    out.state.allocations = c.state.allocations ∨
      ∃ a : Allocation, out.state.allocations = c.state.allocations.push a := by
  simp only [_redeemOne] at h
  split_ifs at h <;> simp_all [bind, Except.bind, pure, Except.pure]
  · subst out
    exact Or.inl rfl
  · repeat' (all_goals (split at h <;> try simp_all))
    all_goals
      subst out
      simp

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
