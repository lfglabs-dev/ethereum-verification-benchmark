import Benchmark.Cases.TermFinance.TermAuctionClearing.Specs

namespace Benchmark.Cases.TermFinance.TermAuctionClearing

/--
For a valid TermAuction clearing point, assignment preserves the clearing-rate
guards and assigns exactly the shared `maxAssignable` purchase-token principal
on both sides.
-/
theorem clearing_assignment_correct_task
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer)
    (hSortedBids : SortedAscendingBids bids)
    (hSortedOffers : SortedAscendingOffers offers)
    (hCapacity : ClearingPointCapacity clearingPrice maxAssignable bids offers) :
  clearing_assignment_correct_spec clearingPrice maxAssignable bids offers := by
  exact ?_

end Benchmark.Cases.TermFinance.TermAuctionClearing
