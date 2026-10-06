import Benchmark.Cases.KPK.SharesSettlementAccounting.Handlers

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

-- The frame is weaker than WellFormed: no empty-trace or escrow claim.
def HandlerData (s t : State) (id : Nat) (status : RequestStatus) (isSub : Bool) : Prop :=
  t.config = s.config ∧ t.requests = (statusState s id status).requests ∧
  t.subscriptionAssets = (bookkeepingState s id status isSub).subscriptionAssets ∧
  t.pendingRequestsCount = (bookkeepingState s id status isSub).pendingRequestsCount ∧
  t.lastSettledPrice = s.lastSettledPrice ∧
  t.managementFeeLastUpdate = s.managementFeeLastUpdate ∧
  t.performanceFeeLastUpdate = s.performanceFeeLastUpdate

-- Non-allowance transfer effects also cover the zero-fee identity branch.
theorem optionalTransfer_integer (env : Environment) (s t : State)
    (fromAddr toAddr : Address) (amount : Nat) (hi : FeeInvariant env s)
    (h : optionalTransfer fromAddr toAddr amount s = .ok ((),t)) :
    totalSupply t = totalSupply s ∧
    (∀ x, (shareBalance t x : Int) - shareBalance s x =
      indicator x toAddr amount - indicator x fromAddr amount) := by
  by_cases ha : amount > 0
  · simp only [optionalTransfer,ha,if_true] at h
    exact ⟨(transfer_effects s t fromAddr toAddr amount hi.1 h).1,
      (transfer_effects s t fromAddr toAddr amount hi.1 h).2.1⟩
  · have hz : amount = 0 := by omega
    simp only [optionalTransfer,ha,if_false] at h
    have ht := (tx_pure_state _ _ _ _ h).2
    rw [ht,hz]
    simp [indicator]

-- Same operation with exact settlement roles, hence the independent world replay.
theorem redemptionPayment_shape (env : Environment) (s t : State) (r : UserRequest)
    (payout : Nat) (hi : FeeInvariant env s)
    (hreg : (s.config.assets r.asset).asset = r.asset) (hnz : r.asset ≠ 0)
    (ha : payout < wordLimit)
    (h : safeTransferFrom env r.asset s.config.self s.config.portfolioSafe r.receiver payout s = .ok ((),t)) :
    ∃ tr, t = {s with external := expectedWorldStep s.config s.external (.redemption 0 r 0 0 payout), trace := tr} := by
  have hs := safeTransferFrom_success env r.asset s.config.self s.config.portfolioSafe r.receiver payout s t ha
    (registered_asset_balance_bounded s env hi.2.1 r.asset s.config.portfolioSafe hreg hnz)
    (hi.2.2 r.asset s.config.portfolioSafe s.config.self hreg hnz) h
  by_cases hal : assetAllowance s r.asset s.config.portfolioSafe s.config.self = wordLimit-1
  · rw [if_pos hal] at hs
    refine ⟨s.trace ++ [.assetTransfer r.asset s.config.portfolioSafe r.receiver payout],?_⟩
    simpa only [expectedWorldStep,show s.external.accountState r.asset.val (aslot s.config.portfolioSafe s.config.self) = wordLimit-1 from hal,if_true] using hs.2.2.2.2
  · rw [if_neg hal] at hs
    refine ⟨s.trace ++ [.allowanceSpent r.asset s.config.portfolioSafe s.config.self payout, .assetTransfer r.asset s.config.portfolioSafe r.receiver payout],?_⟩
    simpa only [expectedWorldStep,show s.external.accountState r.asset.val (aslot s.config.portfolioSafe s.config.self) ≠ wordLimit-1 from hal,if_false,assetAllowance] using hs.2.2.2.2.2


-- Integer vector and finite/infinite allowance accounting from the actual payment.
theorem redemptionPayment_vector (env : Environment) (s t : State) (r : UserRequest)
    (payout : Nat) (hi : FeeInvariant env s)
    (hreg : (s.config.assets r.asset).asset = r.asset) (hnz : r.asset ≠ 0)
    (ha : payout < wordLimit)
    (h : safeTransferFrom env r.asset s.config.self s.config.portfolioSafe r.receiver payout s = .ok ((),t)) :
    (∀ token x, (assetBalance t token x : Int) - assetBalance s token x =
      if token = r.asset then indicator x r.receiver payout - indicator x s.config.portfolioSafe payout else 0) ∧
    (∀ token owner spender,
      if assetAllowance s token owner spender = wordLimit-1 then assetAllowance t token owner spender = wordLimit-1
      else (assetAllowance t token owner spender : Int) - assetAllowance s token owner spender =
        -(if token = r.asset ∧ owner = s.config.portfolioSafe ∧ spender = s.config.self then (payout : Int) else 0)) := by
  have hc := safeTransferFrom_accounting s t env hi.2.1 r.asset s.config.self s.config.portfolioSafe r.receiver hreg hnz payout ha
    (hi.2.2 r.asset s.config.portfolioSafe s.config.self hreg hnz) h
  constructor
  · intro token x
    by_cases he : token = r.asset
    · subst token; simpa only [if_pos rfl,if_true] using hc.2.1 x
    · have hs := safeTransferFrom_success env r.asset s.config.self s.config.portfolioSafe r.receiver payout s t ha
        (registered_asset_balance_bounded s env hi.2.1 r.asset s.config.portfolioSafe hreg hnz)
        (hi.2.2 r.asset s.config.portfolioSafe s.config.self hreg hnz) h
      rw [if_neg he]
      by_cases hal : assetAllowance s r.asset s.config.portfolioSafe s.config.self = wordLimit-1
      · rw [if_pos hal] at hs
        rw [hs.2.2.2.2]
        have hh := token_transfer_other_target s r.asset token s.config.portfolioSafe r.receiver payout he
        simp only [assetBalance,hh,Int.sub_self]
      · rw [if_neg hal] at hs
        rw [hs.2.2.2.2.2]
        let m : State := {s with external := (writeExternal s.external r.asset.val (aslot s.config.portfolioSafe s.config.self) (assetAllowance s r.asset s.config.portfolioSafe s.config.self - payout))}
        have hmt := token_transfer_other_target m r.asset token s.config.portfolioSafe r.receiver payout he
        have hm := allowance_write_other_target s r.asset token s.config.portfolioSafe s.config.self
          (assetAllowance s r.asset s.config.portfolioSafe s.config.self - payout) he
        change ((tokenWordTransfer m.external r.asset s.config.portfolioSafe r.receiver payout).accountState token.val (bslot x) : Int) -
          (s.external.accountState token.val (bslot x) : Int) = 0
        rw [hmt]
        change (assetBalance m token x : Int) - assetBalance s token x = 0
        have hx : assetBalance m token x = assetBalance s token x := congrFun hm (bslot x)
        rw [hx]; omega
  · exact safeTransferFrom_allowance_integer s t env hi.2.1 r.asset s.config.self s.config.portfolioSafe r.receiver
      hreg hnz payout ha (hi.2.2 r.asset s.config.portfolioSafe s.config.self hreg hnz) h

theorem rejectSubscription_data (env : Environment) (s t : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hs : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hap : ExternalApplicability env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) :
    HandlerData s t id .rejected true ∧ (∀ asset, CallerFrame s t asset) ∧
    t.external = expectedWorldStep s.config s.external (.rejection id (s.requests id)) ∧
    totalSupply t = totalSupply s ∧ shareBalance t = shareBalance s := by
  have ht := (rejectSubscription_success env s t n id hn hv hk hc ha hs hp hap hreg htoken h).1
  rw [ht]
  refine ⟨by simp [HandlerData,bookkeepingState,statusState],
    by intro asset; simp [CallerFrame,bookkeepingState,statusState],?_,rfl,by funext x; rfl⟩
  simp only [expectedWorldStep,hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true]

theorem rejectRedemption_data (s t : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit) (hl : LedgerCoherent s)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) :
    HandlerData s t id .rejected false ∧
    t.external = expectedWorldStep s.config s.external (.rejection id (s.requests id)) := by
  obtain ⟨z,hpay,ht,_⟩ := rejectRedemption_success s t n id hn hv hk hc hp hl h
  have hz := (transfer_success _ _ _ _ _ hpay).2.2.2
  rw [ht,hz]
  simp [HandlerData,expectedWorldStep,hk,bookkeepingState,statusState,shareWrite,show (RequestType.redemption == RequestType.subscription) = false from rfl]

theorem approveSubscription_data (env : Environment) (s t : State) (n id price : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hs : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hprice : price < wordLimit) (hd : (s.config.assets (s.requests id).asset).decimals ≤ 36)
    (hi : FeeInvariant env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) :
    HandlerData s t id .processed true ∧
    t.external = expectedWorldStep s.config s.external (.subscription id (s.requests id) (Mint (s.requests id).assetAmount price (s.config.assets (s.requests id).asset).decimals)) := by
  obtain ⟨q,_,_,_,ht,_⟩ := approveSubscription_success env s t n id price hn hv hk hc ha hs hp hprice hd hi hreg htoken h
  rw [ht]
  simp [HandlerData,expectedWorldStep,bookkeepingState,statusState,mintedState,shareWrite,supplyWrite]

theorem approveRedemption_data (env : Environment) (s t : State) (n id price : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n)
    (hs : (s.requests id).sharesAmount < wordLimit) (hr : s.config.redemptionFeeRate < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hprice : price < wordLimit) (hd : (s.config.assets (s.requests id).asset).decimals ≤ 36)
    (hi : FeeInvariant env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) :
    ∃ fee net payout, fee = RedeemFee (s.requests id).sharesAmount s.config.redemptionFeeRate ∧
      net = (s.requests id).sharesAmount - fee ∧
      payout = Out net price (s.config.assets (s.requests id).asset).decimals ∧
      HandlerData s t id .processed false ∧ (∀ asset, CallerFrame s t asset) ∧
      t.external = expectedWorldStep s.config s.external (.redemption id (s.requests id) fee net payout) ∧
      (totalSupply t : Int) - totalSupply s = -(net : Int) ∧
      (∀ x, (shareBalance t x : Int) - shareBalance s x =
        indicator x s.config.feeReceiver fee - indicator x s.config.self fee - indicator x s.config.self net) := by
  obtain ⟨fee,net,payout,f,b,z,paid,hfee,_,hnet,hpayout,_,hpayB,hf,hb,hburn,hpay,ht,_,_,_⟩ :=
    approveRedemption_execution env s t n id price hn hv hk hc hs hr hp hprice hd hi hreg htoken h
  have fc := optionalTransfer_closure env s f s.config.self s.config.feeReceiver fee hi hf
  have fi := optionalTransfer_integer env s f s.config.self s.config.feeReceiver fee hi hf
  have fb : b.config = s.config := by rw [hb]; exact fc.2.1.1
  have fx : b.external = s.external := by rw [hb]; exact fc.2.2.1
  have bl : LedgerCoherent b := by rw [hb]; exact fc.1.1
  have bz := (burn_success b z s.config.self net hburn).2.2
  have zcfg : z.config = s.config := by rw [bz]; exact fb
  have zx : z.external = s.external := by rw [bz]; exact fx
  have zi : FeeInvariant env z := by
    refine ⟨(burn_effects b z s.config.self net bl hburn).2.2.2,?_,?_⟩
    · rw [bz,hb]; exact fc.1.2.1
    · rw [bz,hb]; exact fc.1.2.2
  have hpay' : safeTransferFrom env (s.requests id).asset z.config.self z.config.portfolioSafe (s.requests id).receiver payout z = .ok ((),paid) := by simpa only [zcfg] using hpay
  obtain ⟨tr,hpaid⟩ := redemptionPayment_shape env z paid (s.requests id) payout zi (by rwa [zcfg]) htoken hpayB hpay'
  have bi := burn_integer_effect b z s.config.self net bl hburn
  refine ⟨fee,net,payout,hfee,hnet,hpayout,?_,?_,?_,?_,?_⟩
  · rw [ht,hpaid,bz,hb]
    rcases fc.2.1 with ⟨hcfg,hreq,hsub,hcount,hprice⟩
    simp only [HandlerData,bookkeepingState,statusState,shareWrite,supplyWrite]
    simpa only [hcfg,hreq,hsub,hcount,hprice] using
      (show f.config = s.config ∧
        (fun j => if j == id then {f.requests id with requestStatus := .processed} else f.requests j) =
          (fun j => if j == id then {s.requests id with requestStatus := .processed} else s.requests j) ∧
        f.subscriptionAssets = s.subscriptionAssets ∧
        (fun a => if a == (f.requests id).asset then f.pendingRequestsCount a - 1 else f.pendingRequestsCount a) =
          (fun a => if a == (s.requests id).asset then s.pendingRequestsCount a - 1 else s.pendingRequestsCount a) ∧
        f.lastSettledPrice = s.lastSettledPrice ∧
        f.managementFeeLastUpdate = s.managementFeeLastUpdate ∧ f.performanceFeeLastUpdate = s.performanceFeeLastUpdate
        from ⟨hcfg,by rw [hreq],hsub,by rw [hreq,hcount],hprice,fc.2.2.2.1,fc.2.2.2.2.1⟩)
  · intro asset
    rw [ht,hpaid]
    have bf := burn_frame b z s.config.self net asset hburn
    have ff := fc.2.2.2.2.2.1 asset
    have bframe : CallerFrame f b asset := by rw [hb]; simp [CallerFrame,bookkeepingState,statusState]
    exact callerFrame_trans s b z asset (callerFrame_trans s f b asset ff bframe) bf
  · rw [ht,hpaid,zcfg,zx]; rfl
  · rw [ht,hpaid]
    change (totalSupply z : Int) - totalSupply s = -(net : Int)
    have btot : totalSupply b = totalSupply f := by rw [hb]; rfl
    rw [btot] at bi
    have fis := fi.1
    omega
  · intro x
    rw [ht,hpaid]
    change (shareBalance z x : Int) - shareBalance s x = _
    have bbal : shareBalance b x = shareBalance f x := by rw [hb]; rfl
    have hh := bi.2 x
    rw [bbal] at hh
    have ff := fi.2 x
    omega


theorem approveRedemption_vector (env : Environment) (s t : State) (n id price : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n)
    (hs : (s.requests id).sharesAmount < wordLimit) (hr : s.config.redemptionFeeRate < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hprice : price < wordLimit) (hd : (s.config.assets (s.requests id).asset).decimals ≤ 36)
    (hi : FeeInvariant env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) :
    ∃ payout, payout = Out ((s.requests id).sharesAmount - RedeemFee (s.requests id).sharesAmount s.config.redemptionFeeRate)
        price (s.config.assets (s.requests id).asset).decimals ∧
      (∀ token x, (assetBalance t token x : Int) - assetBalance s token x =
        if token = (s.requests id).asset then indicator x (s.requests id).receiver payout - indicator x s.config.portfolioSafe payout else 0) ∧
      (∀ token owner spender,
        if assetAllowance s token owner spender = wordLimit-1 then assetAllowance t token owner spender = wordLimit-1
        else (assetAllowance t token owner spender : Int) - assetAllowance s token owner spender =
          -(if token = (s.requests id).asset ∧ owner = s.config.portfolioSafe ∧ spender = s.config.self then (payout : Int) else 0)) := by
  obtain ⟨fee,net,payout,f,b,z,paid,hfee,_,hnet,hpayout,_,hpayB,hf,hb,hburn,hpay,ht,_,_,_⟩ :=
    approveRedemption_execution env s t n id price hn hv hk hc hs hr hp hprice hd hi hreg htoken h
  have fc := optionalTransfer_closure env s f s.config.self s.config.feeReceiver fee hi hf
  have fb : b.config = s.config := by rw [hb]; exact fc.2.1.1
  have fx : b.external = s.external := by rw [hb]; exact fc.2.2.1
  have bl : LedgerCoherent b := by rw [hb]; exact fc.1.1
  have bz := (burn_success b z s.config.self net hburn).2.2
  have zcfg : z.config = s.config := by rw [bz]; exact fb
  have zx : z.external = s.external := by rw [bz]; exact fx
  have zi : FeeInvariant env z := by
    refine ⟨(burn_effects b z s.config.self net bl hburn).2.2.2,?_,?_⟩
    · rw [bz,hb]; exact fc.1.2.1
    · rw [bz,hb]; exact fc.1.2.2
  have hpay' : safeTransferFrom env (s.requests id).asset z.config.self z.config.portfolioSafe (s.requests id).receiver payout z = .ok ((),paid) := by simpa only [zcfg] using hpay
  have vp := redemptionPayment_vector env z paid (s.requests id) payout zi (by rwa [zcfg]) htoken hpayB hpay'
  refine ⟨payout,by rwa [hnet,hfee] at hpayout,?_,?_⟩
  · intro token x
    rw [ht]
    simpa only [assetBalance,zx,zcfg] using vp.1 token x
  · intro token owner spender
    rw [ht]
    simpa only [assetAllowance,zx,zcfg] using vp.2 token owner spender

#print axioms approveRedemption_data
#print axioms approveRedemption_vector
#print axioms approveSubscription_data
#print axioms rejectSubscription_data
#print axioms rejectRedemption_data
#print axioms redemptionPayment_shape
#print axioms redemptionPayment_vector
#print axioms optionalTransfer_integer

-- The integer balance vector includes every untouched token, not merely the paid
-- asset. Full ExternalWorld replay is a separate stronger frame already exposed.
theorem rejectSubscription_vector (env : Environment) (s t : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hs : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hap : ExternalApplicability env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) :
    ∀ token x, (assetBalance t token x : Int) - assetBalance s token x =
      if token = (s.requests id).asset then
        indicator x (s.requests id).investor (s.requests id).assetAmount - indicator x s.config.self (s.requests id).assetAmount else 0 := by
  have hr := rejectSubscription_success env s t n id hn hv hk hc ha hs hp hap hreg htoken h
  intro token x
  by_cases he : token = (s.requests id).asset
  · subst token; simpa only [if_pos rfl,if_true] using hr.2.2.2.1 x
  · rw [hr.1,if_neg he]
    have hh := token_transfer_other_target s (s.requests id).asset token s.config.self (s.requests id).investor (s.requests id).assetAmount he
    simp only [assetBalance,hh,Int.sub_self]

theorem approveSubscription_vector (env : Environment) (s t : State) (n id price : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hs : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hprice : price < wordLimit) (hd : (s.config.assets (s.requests id).asset).decimals ≤ 36)
    (hi : FeeInvariant env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) :
    ∀ token x, (assetBalance t token x : Int) - assetBalance s token x =
      if token = (s.requests id).asset then
        indicator x s.config.portfolioSafe (s.requests id).assetAmount - indicator x s.config.self (s.requests id).assetAmount else 0 := by
  obtain ⟨q,_,_,_,ht,_,_,_,_,_,hvector,_⟩ := approveSubscription_success env s t n id price hn hv hk hc ha hs hp hprice hd hi hreg htoken h
  intro token x
  by_cases he : token = (s.requests id).asset
  · subst token; simpa only [if_pos rfl,if_true] using hvector x
  · rw [ht,if_neg he]
    have hh := token_transfer_other_target s (s.requests id).asset token s.config.self s.config.portfolioSafe (s.requests id).assetAmount he
    simp only [assetBalance,hh,Int.sub_self]

theorem rejectRedemption_vector (s t : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit) (hl : LedgerCoherent s)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) :
    (∀ token x, assetBalance t token x = assetBalance s token x) ∧
    (∀ token owner spender, assetAllowance t token owner spender = assetAllowance s token owner spender) := by
  obtain ⟨_,_,_,_,_,_,_,_,hext,_⟩ := rejectRedemption_success s t n id hn hv hk hc hp hl h
  exact ⟨by intro token x; simp only [assetBalance,hext],by intro token owner spender; simp only [assetAllowance,hext]⟩

#print axioms rejectSubscription_vector
#print axioms approveSubscription_vector
#print axioms rejectRedemption_vector
end Benchmark.Cases.KPK.SharesSettlementAccounting
