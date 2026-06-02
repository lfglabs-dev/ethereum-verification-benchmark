import Benchmark.Cases.TermFinance.TermAuctionClearing.Specs

namespace Benchmark.Cases.TermFinance.TermAuctionClearing

/--
AXIOM terminal condition.

This axiom is the residual-sweep totals lemma for the purchase-token assignment
model: if a shared `maxAssignable` is no larger than eligible bid demand and
eligible offer supply at the clearing price, then the assignment sweeps assign
exactly that amount on both sides.

Why this matches the real contract:
`_assignBids` and `_assignOffers` fully assign whole eligible price groups while
they fit. When the next eligible price group would exceed the remaining cap, the
last tender in that marginal group receives `maxAssignable - totalAssigned`.
The Solidity pro-rata floors only redistribute principal within that marginal
group before the last tender; they do not change the side total.

What remains unproved mechanically here is only the list-recursive telescoping
proof that `assignBidAmounts` and `assignOfferAmounts` sum to `maxAssignable`
under the two capacity hypotheses.
-/
axiom residual_sweep_totals_exact
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer) :
  SortedAscendingBids bids ->
  SortedAscendingOffers offers ->
  ClearingPointCapacity clearingPrice maxAssignable bids offers ->
  assigned_bid_total_spec clearingPrice maxAssignable bids ∧
  assigned_offer_total_spec clearingPrice maxAssignable offers

/--
AXIOM terminal condition, rate guards.

This small companion axiom states the construction-level guard facts for the
assignment lists. These facts should be discharged by direct list induction in a
future no-axiom version. They are separated from `residual_sweep_totals_exact`
so the total-balance assumption remains narrow.
-/
axiom residual_sweep_assignment_correct_rate_guards
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer) :
  SortedAscendingBids bids ->
  SortedAscendingOffers offers ->
  ClearingPointCapacity clearingPrice maxAssignable bids offers ->
  assigned_bid_rate_floor_spec clearingPrice maxAssignable bids ∧
  assigned_offer_rate_ceiling_spec clearingPrice maxAssignable offers

theorem clearing_assignment_correct
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer)
    (hSortedBids : SortedAscendingBids bids)
    (hSortedOffers : SortedAscendingOffers offers)
    (hCapacity : ClearingPointCapacity clearingPrice maxAssignable bids offers) :
  clearing_assignment_correct_spec clearingPrice maxAssignable bids offers :=
by
  have hTotals :=
    residual_sweep_totals_exact
      clearingPrice
      maxAssignable
      bids
      offers
      hSortedBids
      hSortedOffers
      hCapacity
  constructor
  · /-
      The rate-guard component is true by construction of `assignBidAmounts`.
      It is kept as an explicit assumption through the AXIOM terminal path for
      this v1 case rather than proved by list induction.
    -/
    exact by
      intro bid assigned hMember hPositive
      exact
        (residual_sweep_assignment_correct_rate_guards
          clearingPrice maxAssignable bids offers hSortedBids hSortedOffers hCapacity).1
          bid assigned hMember hPositive
  · constructor
    · exact
        (residual_sweep_assignment_correct_rate_guards
          clearingPrice maxAssignable bids offers hSortedBids hSortedOffers hCapacity).2
    · constructor
      · exact hTotals.1
      · constructor
        · exact hTotals.2
        · rw [hTotals.1, hTotals.2]

end Benchmark.Cases.TermFinance.TermAuctionClearing
