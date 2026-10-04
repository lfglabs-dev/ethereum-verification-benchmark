import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.SourceFunding
import Mathlib.Tactic

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Consequences of the actual successful source checks, without any ledger budget
or global uint256 bound on a demand's as-yet-unchecked end. -/
theorem redeem_iteration_arithmetic (d : Demand) (f : Fulfillment)
    (dEnd fEnd overlap demandAssets fulfillmentAssets : Nat)
    (hmatch : _isMatchingFulfillment d.position f = .ok true)
    (hdEnd : checkedAdd d.position d.amountIn = .ok dEnd)
    (hfEnd : checkedAdd f.position f.filledAmountIn = .ok fEnd)
    (hoverlap : checkedSub (min dEnd fEnd) (max d.position f.position) = .ok overlap)
    (_hdAssets : mulDivFloor overlap d.maxAmountOut d.amountIn = .ok demandAssets)
    (hfAssets : mulDivFloor overlap f.amountOut f.filledAmountIn = .ok fulfillmentAssets) :
    overlap ≤ d.amountIn ∧
    max d.position f.position = d.position ∧
    f.position ≤ d.position ∧
    d.position + overlap ≤ f.position + f.filledAmountIn ∧
    min demandAssets fulfillmentAssets ≤ overlap * f.amountOut / f.filledAmountIn := by
  obtain ⟨hstart, _⟩ := matching_ok hmatch
  have hmax : max d.position f.position = d.position := Nat.max_eq_left hstart
  have hd := (checked_add_ok hdEnd).1
  have hf := (checked_add_ok hfEnd).1
  obtain ⟨hle, heq⟩ := checked_sub_ok hoverlap
  rw [hmax] at hle heq
  have hminD : min dEnd fEnd ≤ dEnd := min_le_left _ _
  have hminF : min dEnd fEnd ≤ fEnd := min_le_right _ _
  have hwidth : overlap ≤ d.amountIn := by omega
  have hendpoint : d.position + overlap = min dEnd fEnd := by
    rw [heq]
    exact Nat.add_sub_of_le hle
  have hlast : d.position + overlap ≤ f.position + f.filledAmountIn := by
    rw [hendpoint, ← hf]
    exact hminF
  have hpayout : min demandAssets fulfillmentAssets ≤
      overlap * f.amountOut / f.filledAmountIn := by
    rw [(mul_div_floor_ok hfAssets).2]
    exact min_le_right _ _
  exact ⟨hwidth, hmax, hstart, hlast, hpayout⟩

/-- Source-level iteration: the nonmatching/finished path leaves funding unchanged;
the matching path's newly pushed ghost allocation is contained in the actual
fulfillment and bounded by its exact per-piece floor. -/
theorem redeem_one_funding_and_facts (id len : Nat) (c out : RedeemCursor)
    (hsafe : SourceFundingSafe c.state)
    (h : _redeemOne id len c = .ok out) :
    SourceFundingSafe out.state ∧
    (out.state.allocations = c.state.allocations ∨
      ∃ (d : Demand) (f : Fulfillment) (overlap payout : Nat),
        validDemand c.state id = .ok d ∧
        validFulfillment c.state c.fulfillmentId = .ok f ∧
        out.state.allocations = c.state.allocations.push
          ⟨id, c.fulfillmentId, d.position, overlap, payout⟩ ∧
        overlap ≤ d.amountIn ∧
        max d.position f.position = d.position ∧
        f.position ≤ d.position ∧
        d.position + overlap ≤ f.position + f.filledAmountIn ∧
        payout ≤ overlap * f.amountOut / f.filledAmountIn) := by
  by_cases hstop : c.stop || c.fulfillmentId > len
  · simp only [_redeemOne, hstop, ↓reduceIte, pure, Except.pure] at h
    cases h
    exact ⟨hsafe, Or.inl rfl⟩
  · simp only [_redeemOne, hstop, Bool.false_eq_true, ↓reduceIte] at h
    cases hf : validFulfillment c.state c.fulfillmentId
    next msg => simp [hf, bind, Except.bind, pure, Except.pure] at h
    next f =>
      simp only [hf, bind, Except.bind, pure, Except.pure] at h
      cases hd : validDemand c.state id
      next msg => simp [hd] at h
      next d =>
        simp only [hd] at h
        cases hm : _isMatchingFulfillment d.position f
        next msg => simp [hm] at h
        next matched =>
          cases matched
          · simp [hm] at h
            cases h
            exact ⟨hsafe, Or.inl rfl⟩
          · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hdEnd : checkedAdd d.position d.amountIn
            next err => simp [hdEnd] at h
            next dEnd =>
              simp only [hdEnd] at h
              cases hfEnd : checkedAdd f.position f.filledAmountIn
              next err => simp [hfEnd] at h
              next fEnd =>
                simp only [hfEnd] at h
                cases hoverlap : checkedSub (min dEnd fEnd) (max d.position f.position)
                next err => simp [hoverlap] at h
                next overlap =>
                  simp only [hoverlap] at h
                  cases hdAssets : mulDivFloor overlap d.maxAmountOut d.amountIn
                  next err => simp [hdAssets] at h
                  next demandAssets =>
                    simp only [hdAssets] at h
                    cases hfAssets : mulDivFloor overlap f.amountOut f.filledAmountIn
                    next err => simp [hfAssets] at h
                    next fulfillmentAssets =>
                      simp only [hfAssets] at h
                      cases hredeemed : checkedAdd c.redeemedAmount (min demandAssets fulfillmentAssets)
                      next err => simp [hredeemed] at h
                      next redeemedAmount =>
                        simp only [hredeemed] at h
                        cases hposition : checkedAdd d.position overlap
                        next err => simp [hposition] at h
                        next newPosition =>
                          simp only [hposition] at h
                          cases hamount : checkedSub d.amountIn overlap
                          next err => simp [hamount] at h
                          next newAmountIn =>
                            simp only [hamount] at h
                            cases hcap : checkedSub d.maxAmountOut (min demandAssets fulfillmentAssets)
                            next err => simp [hcap] at h
                            next newMaxAmountOut =>
                              simp only [hcap] at h
                              cases hnext : checkedAdd c.fulfillmentId 1
                              next err => simp [hnext] at h
                              next nextFulfillmentId =>
                                simp only [hnext] at h
                                cases hthreshold : checkedAdd demandAssets 1
                                next err => simp [hthreshold] at h
                                next threshold =>
                                  simp only [hthreshold] at h
                                  obtain ⟨hwidth, hmax, hstart, hend, hpayout⟩ :=
                                    redeem_iteration_arithmetic d f dEnd fEnd overlap
                                      demandAssets fulfillmentAssets hm hdEnd hfEnd
                                      hoverlap hdAssets hfAssets
                                  let a : Allocation :=
                                    ⟨id, c.fulfillmentId, d.position, overlap,
                                      min demandAssets fulfillmentAssets⟩
                                  have hnew :
                                      0 < a.fulfillmentId ∧
                                      a.fulfillmentId ≤ c.state.fulfillments.size ∧
                                      (c.state.fulfillments[a.fulfillmentId - 1]!).position ≤ a.start ∧
                                      a.start + a.length ≤
                                        (c.state.fulfillments[a.fulfillmentId - 1]!).position +
                                          (c.state.fulfillments[a.fulfillmentId - 1]!).filledAmountIn ∧
                                      a.nominalPayout ≤ a.length *
                                        (c.state.fulfillments[a.fulfillmentId - 1]!).amountOut /
                                          (c.state.fulfillments[a.fulfillmentId - 1]!).filledAmountIn := by
                                    obtain ⟨hfid, hsize, hreal⟩ := valid_fulfillment_ok hf
                                    rw [hreal] at hstart hend hpayout
                                    exact ⟨hfid, hsize, hstart, hend, hpayout⟩
                                  have hpush := funding_push_allocation c.state hsafe a hnew
                                  by_cases hmore : fulfillmentAssets > threshold
                                  · simp only [hmore, ↓reduceIte] at h
                                    cases hexcess : checkedSub fulfillmentAssets threshold
                                    next err => simp [hexcess] at h
                                    next excess =>
                                      simp only [hexcess] at h
                                      cases hupdated : checkedAdd c.state.retrievable excess
                                      next err => simp [hupdated] at h
                                      next updated =>
                                        simp only [hupdated] at h
                                        cases h
                                        refine ⟨?_, Or.inr ?_⟩
                                        · simpa only [SourceFundingSafe, a] using hpush
                                        · exact ⟨d, f, overlap, min demandAssets fulfillmentAssets,
                                            rfl, rfl, rfl, hwidth, hmax, hstart, hend, hpayout⟩
                                  · simp only [hmore, ↓reduceIte] at h
                                    cases h
                                    refine ⟨?_, Or.inr ?_⟩
                                    · simpa only [SourceFundingSafe, a] using hpush
                                    · exact ⟨d, f, overlap, min demandAssets fulfillmentAssets,
                                        rfl, rfl, rfl, hwidth, hmax, hstart, hend, hpayout⟩

/-- A successful source iteration preserves fulfillment containment and
per-piece payout funding, including the branch that only sets `stop`. -/
theorem source_funding_redeem_one (id len : Nat) (c out : RedeemCursor)
    (hsafe : SourceFundingSafe c.state)
    (h : _redeemOne id len c = .ok out) :
    SourceFundingSafe out.state :=
  (redeem_one_funding_and_facts id len c out hsafe h).1

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
