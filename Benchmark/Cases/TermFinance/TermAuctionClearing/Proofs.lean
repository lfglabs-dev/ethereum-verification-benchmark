import Benchmark.Cases.TermFinance.TermAuctionClearing.Specs

namespace Benchmark.Cases.TermFinance.TermAuctionClearing

private theorem minNat_eq_right_of_le {a b : Nat} (h : b <= a) :
    minNat a b = b := by
  unfold minNat
  by_cases hle : a <= b
  · have heq : a = b := by omega
    simp [heq]
  · simp [hle]

private theorem greedy_step (eligible rest remaining : Nat) :
    minNat eligible remaining +
      minNat rest (remaining - minNat eligible remaining) =
        minNat (eligible + rest) remaining := by
  unfold minNat
  by_cases hEligible : eligible <= remaining
  · simp [hEligible]
    by_cases hRest : rest <= remaining - eligible
    · have hsum : eligible + rest <= remaining := by omega
      simp [hRest, hsum]
    · have hsum : ¬ eligible + rest <= remaining := by omega
      have hsub : eligible + (remaining - eligible) = remaining :=
        Nat.add_sub_of_le hEligible
      simp [hRest, hsum, hsub]
  · have hsum : ¬ eligible + rest <= remaining := by omega
    simp [hEligible, hsum]

private theorem sumNatList_append (xs ys : List Nat) :
    sumNatList (xs ++ ys) = sumNatList xs + sumNatList ys := by
  induction xs with
  | nil => simp [sumNatList]
  | cons x xs ih => simp [sumNatList, ih, Nat.add_assoc]

private theorem sumNatList_reverse (xs : List Nat) :
    sumNatList xs.reverse = sumNatList xs := by
  induction xs with
  | nil => simp [sumNatList]
  | cons x xs ih =>
      simp [List.reverse_cons, sumNatList_append, sumNatList, ih, Nat.add_comm]

private theorem assignBidAmountsForward_length
    (clearingPrice remaining : Nat) (bids : List Bid) :
    (assignBidAmountsForward clearingPrice remaining bids).length = bids.length := by
  induction bids generalizing remaining with
  | nil => simp [assignBidAmountsForward]
  | cons bid rest ih =>
      unfold assignBidAmountsForward
      by_cases hEligible : clearingPrice <= bid.price
      · simp [hEligible, ih]
      · simp [hEligible, ih]

private theorem zip_reverse_eq {α β : Type} (xs : List α) (ys : List β)
    (hLen : xs.length = ys.length) :
    xs.reverse.zip ys.reverse = (xs.zip ys).reverse := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp
      | cons _ _ => simp at hLen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hLen
      | cons y ys =>
          simp at hLen
          rw [List.reverse_cons, List.reverse_cons]
          rw [List.zip_append]
          · simp [ih ys hLen]
          · simp [hLen]

private theorem sumBidDemand_append (clearingPrice : Nat) (xs ys : List Bid) :
    sumBidDemandAtOrAbove clearingPrice (xs ++ ys) =
      sumBidDemandAtOrAbove clearingPrice xs +
        sumBidDemandAtOrAbove clearingPrice ys := by
  induction xs with
  | nil => simp [sumBidDemandAtOrAbove]
  | cons x xs ih => simp [sumBidDemandAtOrAbove, ih, Nat.add_assoc]

private theorem sumBidDemand_reverse (clearingPrice : Nat) (xs : List Bid) :
    sumBidDemandAtOrAbove clearingPrice xs.reverse =
      sumBidDemandAtOrAbove clearingPrice xs := by
  induction xs with
  | nil => simp [sumBidDemandAtOrAbove]
  | cons x xs ih =>
      simp [List.reverse_cons, sumBidDemand_append, sumBidDemandAtOrAbove, ih,
        Nat.add_comm]

private theorem sumOfferSupply_append (clearingPrice : Nat) (xs ys : List Offer) :
    sumOfferSupplyAtOrBelow clearingPrice (xs ++ ys) =
      sumOfferSupplyAtOrBelow clearingPrice xs +
        sumOfferSupplyAtOrBelow clearingPrice ys := by
  induction xs with
  | nil => simp [sumOfferSupplyAtOrBelow]
  | cons x xs ih => simp [sumOfferSupplyAtOrBelow, ih, Nat.add_assoc]

private theorem bid_forward_sum_min
    (clearingPrice remaining : Nat) (bids : List Bid) :
    sumNatList (assignBidAmountsForward clearingPrice remaining bids) =
      minNat (sumBidDemandAtOrAbove clearingPrice bids) remaining := by
  induction bids generalizing remaining with
  | nil =>
      unfold assignBidAmountsForward sumNatList sumBidDemandAtOrAbove minNat
      simp
  | cons bid rest ih =>
      unfold assignBidAmountsForward sumNatList sumBidDemandAtOrAbove
        bidAmountIfEligible
      by_cases hEligible : clearingPrice <= bid.price
      · simp [hEligible]
        rw [ih]
        exact greedy_step bid.amount
          (sumBidDemandAtOrAbove clearingPrice rest)
          remaining
      · simp [hEligible]
        rw [ih]

private theorem offer_forward_sum_min
    (clearingPrice remaining : Nat) (offers : List Offer) :
    sumNatList (assignOfferAmounts clearingPrice remaining offers) =
      minNat (sumOfferSupplyAtOrBelow clearingPrice offers) remaining := by
  induction offers generalizing remaining with
  | nil =>
      unfold assignOfferAmounts sumNatList sumOfferSupplyAtOrBelow minNat
      simp
  | cons offer rest ih =>
      unfold assignOfferAmounts sumNatList sumOfferSupplyAtOrBelow
        offerAmountIfEligible
      by_cases hEligible : offer.price <= clearingPrice
      · simp [hEligible]
        rw [ih]
        exact greedy_step offer.amount
          (sumOfferSupplyAtOrBelow clearingPrice rest)
          remaining
      · simp [hEligible]
        rw [ih]

private theorem assigned_bid_total_exact
    (clearingPrice maxAssignable : Nat) (bids : List Bid)
    (hCapacity : maxAssignable <= sumBidDemandAtOrAbove clearingPrice bids) :
    assigned_bid_total_spec clearingPrice maxAssignable bids := by
  unfold assigned_bid_total_spec assignedBidPrincipal assignBidAmounts
  rw [sumNatList_reverse]
  rw [bid_forward_sum_min]
  rw [sumBidDemand_reverse]
  exact minNat_eq_right_of_le hCapacity

private theorem assigned_offer_total_exact
    (clearingPrice maxAssignable : Nat) (offers : List Offer)
    (hCapacity : maxAssignable <= sumOfferSupplyAtOrBelow clearingPrice offers) :
    assigned_offer_total_spec clearingPrice maxAssignable offers := by
  unfold assigned_offer_total_spec assignedOfferPrincipal
  rw [offer_forward_sum_min]
  exact minNat_eq_right_of_le hCapacity

private theorem bid_forward_rate_guards
    (clearingPrice remaining : Nat) (bids : List Bid) :
    ∀ bid assigned,
      (bid, assigned) ∈
        List.zip bids (assignBidAmountsForward clearingPrice remaining bids) ->
        assigned > 0 ->
          bidEligible clearingPrice bid := by
  induction bids generalizing remaining with
  | nil =>
      intro bid assigned hMember _
      simp at hMember
  | cons head rest ih =>
      intro bid assigned hMember hPositive
      unfold assignBidAmountsForward at hMember
      by_cases hEligible : clearingPrice <= head.price
      · simp [hEligible] at hMember
        cases hMember with
        | inl hHead =>
            rcases hHead with ⟨rfl, rfl⟩
            exact hEligible
        | inr hTail =>
            exact ih (remaining - minNat head.amount remaining)
              bid assigned hTail hPositive
      · simp [hEligible] at hMember
        cases hMember with
        | inl hHead =>
            rcases hHead with ⟨rfl, rfl⟩
            omega
        | inr hTail =>
            exact ih remaining bid assigned hTail hPositive

private theorem offer_forward_rate_guards
    (clearingPrice remaining : Nat) (offers : List Offer) :
    ∀ offer assigned,
      (offer, assigned) ∈
        List.zip offers (assignOfferAmounts clearingPrice remaining offers) ->
        assigned > 0 ->
          offerEligible clearingPrice offer := by
  induction offers generalizing remaining with
  | nil =>
      intro offer assigned hMember _
      simp at hMember
  | cons head rest ih =>
      intro offer assigned hMember hPositive
      unfold assignOfferAmounts at hMember
      by_cases hEligible : head.price <= clearingPrice
      · simp [hEligible] at hMember
        cases hMember with
        | inl hHead =>
            rcases hHead with ⟨rfl, rfl⟩
            exact hEligible
        | inr hTail =>
            exact ih (remaining - minNat head.amount remaining)
              offer assigned hTail hPositive
      · simp [hEligible] at hMember
        cases hMember with
        | inl hHead =>
            rcases hHead with ⟨rfl, rfl⟩
            omega
        | inr hTail =>
            exact ih remaining offer assigned hTail hPositive

private theorem assigned_bid_rate_floor_exact
    (clearingPrice maxAssignable : Nat) (bids : List Bid) :
    assigned_bid_rate_floor_spec clearingPrice maxAssignable bids := by
  unfold assigned_bid_rate_floor_spec bidAssignmentRatesRespectClearing
  intro bid assigned hMember hPositive
  unfold assignBidAmounts at hMember
  let forward := assignBidAmountsForward clearingPrice maxAssignable bids.reverse
  have hLen : bids.reverse.length = forward.length := by
    dsimp [forward]
    rw [assignBidAmountsForward_length]
  have hZip :
      List.zip bids forward.reverse = (List.zip bids.reverse forward).reverse := by
    simpa using zip_reverse_eq bids.reverse forward hLen
  change (bid, assigned) ∈ List.zip bids forward.reverse at hMember
  rw [hZip] at hMember
  have hForward : (bid, assigned) ∈ List.zip bids.reverse forward :=
    (List.mem_reverse).1 hMember
  exact bid_forward_rate_guards clearingPrice maxAssignable bids.reverse
    bid assigned hForward hPositive

private theorem assigned_offer_rate_ceiling_exact
    (clearingPrice maxAssignable : Nat) (offers : List Offer) :
    assigned_offer_rate_ceiling_spec clearingPrice maxAssignable offers := by
  unfold assigned_offer_rate_ceiling_spec offerAssignmentRatesRespectClearing
  exact offer_forward_rate_guards clearingPrice maxAssignable offers

theorem clearing_assignment_correct
    (clearingPrice maxAssignable : Nat) (bids : List Bid) (offers : List Offer)
    (_hSortedBids : SortedAscendingBids bids)
    (_hSortedOffers : SortedAscendingOffers offers)
    (hCapacity : ClearingPointCapacity clearingPrice maxAssignable bids offers) :
    clearing_assignment_correct_spec clearingPrice maxAssignable bids offers := by
  have hBidTotal :=
    assigned_bid_total_exact clearingPrice maxAssignable bids hCapacity.1
  have hOfferTotal :=
    assigned_offer_total_exact clearingPrice maxAssignable offers hCapacity.2
  constructor
  · exact assigned_bid_rate_floor_exact clearingPrice maxAssignable bids
  · constructor
    · exact assigned_offer_rate_ceiling_exact clearingPrice maxAssignable offers
    · constructor
      · exact hBidTotal
      · constructor
        · exact hOfferTotal
        · rw [hBidTotal, hOfferTotal]

end Benchmark.Cases.TermFinance.TermAuctionClearing
