import Benchmark.Cases.TermFinance.TermAuctionClearing.Contract

namespace Benchmark.Cases.TermFinance.TermAuctionClearing

def assigned_bid_rate_floor_spec
    (clearingPrice maxAssignable : Nat) (bids : List Bid) : Prop :=
  bidAssignmentRatesRespectClearing clearingPrice maxAssignable bids

def assigned_offer_rate_ceiling_spec
    (clearingPrice maxAssignable : Nat) (offers : List Offer) : Prop :=
  offerAssignmentRatesRespectClearing clearingPrice maxAssignable offers

def assigned_bid_total_spec
    (clearingPrice maxAssignable : Nat) (bids : List Bid) : Prop :=
  assignedBidPrincipal clearingPrice maxAssignable bids = maxAssignable

def assigned_offer_total_spec
    (clearingPrice maxAssignable : Nat) (offers : List Offer) : Prop :=
  assignedOfferPrincipal clearingPrice maxAssignable offers = maxAssignable

def clearing_assignment_correct_spec
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer) : Prop :=
  assigned_bid_rate_floor_spec clearingPrice maxAssignable bids ∧
  assigned_offer_rate_ceiling_spec clearingPrice maxAssignable offers ∧
  assigned_bid_total_spec clearingPrice maxAssignable bids ∧
  assigned_offer_total_spec clearingPrice maxAssignable offers ∧
  assignedBidPrincipal clearingPrice maxAssignable bids =
    assignedOfferPrincipal clearingPrice maxAssignable offers

end Benchmark.Cases.TermFinance.TermAuctionClearing
