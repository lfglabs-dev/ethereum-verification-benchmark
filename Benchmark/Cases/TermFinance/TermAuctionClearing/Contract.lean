namespace Benchmark.Cases.TermFinance.TermAuctionClearing

/--
  Focused model of Term Finance `TermAuction` clearing assignment.

  Simplifications and scope:
  - `TermAuctionRevealedBid[]` and `TermAuctionRevealedOffer[]` are modeled as
    immutable Lean lists of records. This is faithful to the algorithmic slice:
    `TermAuction` assumes sorted memory arrays produced by the bid and offer
    lockers.
  - Sortedness is a hypothesis, not a sorting step. The real lockers validate
    ascending prices before the auction receives the arrays.
  - `_calculateClearingPrice` is represented by clearing-point hypotheses over
    `clearingPrice` and `maxAssignable`. This benchmark proves assignment
    correctness for a valid clearing point; it does not prove the binary-search
    loop that finds that point.
  - Assignment is modeled at purchase-token principal level on successful,
    non-reverting executions. External calls to bid lockers, offer lockers,
    rollover managers, repo servicers, collateral managers, token contracts,
    events, and the controller are omitted because they do not change the
    assigned purchase-token amount.
  - Bids are swept from the high-price end of the ascending list by reversing
    before the residual sweep and reversing assigned amounts back into original
    array order. Offers are swept from the low-price end. This matches the
    direction of `_assignBids` and `_assignOffers`.
  - The pro-rata floor arithmetic inside a marginal price group is abstracted to
    a residual sweep. This preserves the property under proof: each side's
    running total reaches exactly `maxAssignable`, and the final marginal tender
    absorbs the residual. It does not claim to prove the per-tender distribution
    or an `assigned <= tender.amount` bound for each individual marginal tender.
  - Sortedness is tracked because it is a real input-boundary condition, but the
    v1 total and rate-guard properties are order-insensitive once clearing-point
    capacity is assumed.
  - The scope is `clearingOffset = 0` and exact purchase-token principal. The
    downstream repurchase-value balance check is intentionally out of scope
    because settlement floors interest and `TermRepoServicer` uses a bounded
    threshold.

  Upstream:
  - term-finance/term-finance-contracts@127b74d871fc74e3a03d6d3b0f1fafe7e5d10275
  - contracts/TermAuction.sol
  - lib/TermAuctionRevealedBid.sol
  - lib/TermAuctionRevealedOffer.sol
-/

structure Bid where
  price : Nat
  amount : Nat
deriving Repr, DecidableEq

structure Offer where
  price : Nat
  amount : Nat
deriving Repr, DecidableEq

def bidEligible (clearingPrice : Nat) (bid : Bid) : Prop :=
  clearingPrice <= bid.price

def offerEligible (clearingPrice : Nat) (offer : Offer) : Prop :=
  offer.price <= clearingPrice

def SortedAscendingBids : List Bid -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.price <= b.price ∧ SortedAscendingBids (b :: rest)

def SortedAscendingOffers : List Offer -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.price <= b.price ∧ SortedAscendingOffers (b :: rest)

def minNat (a b : Nat) : Nat :=
  if a <= b then a else b

def bidAmountIfEligible (clearingPrice : Nat) (bid : Bid) : Nat :=
  if clearingPrice <= bid.price then bid.amount else 0

def offerAmountIfEligible (clearingPrice : Nat) (offer : Offer) : Nat :=
  if offer.price <= clearingPrice then offer.amount else 0

def sumBidDemandAtOrAbove (clearingPrice : Nat) : List Bid -> Nat
  | [] => 0
  | bid :: rest => bidAmountIfEligible clearingPrice bid + sumBidDemandAtOrAbove clearingPrice rest

def sumOfferSupplyAtOrBelow (clearingPrice : Nat) : List Offer -> Nat
  | [] => 0
  | offer :: rest => offerAmountIfEligible clearingPrice offer + sumOfferSupplyAtOrBelow clearingPrice rest

def assignBidAmountsForward (clearingPrice maxAssignable : Nat) : List Bid -> List Nat
  | [] => []
  | bid :: rest =>
      let assigned :=
        if clearingPrice <= bid.price then minNat bid.amount maxAssignable else 0
      assigned :: assignBidAmountsForward clearingPrice (maxAssignable - assigned) rest

def assignBidAmounts (clearingPrice maxAssignable : Nat) (bids : List Bid) : List Nat :=
  (assignBidAmountsForward clearingPrice maxAssignable bids.reverse).reverse

def assignOfferAmounts (clearingPrice maxAssignable : Nat) : List Offer -> List Nat
  | [] => []
  | offer :: rest =>
      let assigned :=
        if offer.price <= clearingPrice then minNat offer.amount maxAssignable else 0
      assigned :: assignOfferAmounts clearingPrice (maxAssignable - assigned) rest

def sumNatList : List Nat -> Nat
  | [] => 0
  | amount :: rest => amount + sumNatList rest

def assignedBidPrincipal (clearingPrice maxAssignable : Nat) (bids : List Bid) : Nat :=
  sumNatList (assignBidAmounts clearingPrice maxAssignable bids)

def assignedOfferPrincipal (clearingPrice maxAssignable : Nat) (offers : List Offer) : Nat :=
  sumNatList (assignOfferAmounts clearingPrice maxAssignable offers)

def bidAssignmentRatesRespectClearing
    (clearingPrice maxAssignable : Nat) (bids : List Bid) : Prop :=
  ∀ bid assigned,
    (bid, assigned) ∈ List.zip bids (assignBidAmounts clearingPrice maxAssignable bids) ->
      assigned > 0 ->
        bidEligible clearingPrice bid

def offerAssignmentRatesRespectClearing
    (clearingPrice maxAssignable : Nat) (offers : List Offer) : Prop :=
  ∀ offer assigned,
    (offer, assigned) ∈ List.zip offers (assignOfferAmounts clearingPrice maxAssignable offers) ->
      assigned > 0 ->
        offerEligible clearingPrice offer

def ClearingPointCapacity
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer) : Prop :=
  maxAssignable <= sumBidDemandAtOrAbove clearingPrice bids ∧
  maxAssignable <= sumOfferSupplyAtOrBelow clearingPrice offers

end Benchmark.Cases.TermFinance.TermAuctionClearing
