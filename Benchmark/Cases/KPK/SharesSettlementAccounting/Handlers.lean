import Benchmark.Cases.KPK.SharesSettlementAccounting.Fees

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def subscriptionBookkeeping (id : Nat) (r : UserRequest) (status : RequestStatus) : Tx Unit := do
  setStatus id status
  debitSubscription r.asset r.assetAmount
  decrementCount r.asset

def redemptionBookkeeping (id : Nat) (r : UserRequest) (status : RequestStatus) : Tx Unit := do
  setStatus id status
  decrementCount r.asset

theorem subscriptionBookkeeping_eq (env : Environment) (id : Nat) (r : UserRequest) :
    _rejectSubscriptionRequest env id r = (do
      subscriptionBookkeeping id r .rejected
      let cfg := (← get).config
      safeTransfer env r.asset cfg.self r.investor r.assetAmount
      record (.rejection id r)) := by
  simp only [_rejectSubscriptionRequest,subscriptionBookkeeping,bind_assoc]

theorem redemptionBookkeeping_eq (id : Nat) (r : UserRequest) :
    _rejectRedeemRequest id r = (do
      redemptionBookkeeping id r .rejected
      let cfg := (← get).config
      _transfer cfg.self r.investor r.sharesAmount
      record (.rejection id r)) := by
  simp only [_rejectRedeemRequest,redemptionBookkeeping,bind_assoc]

theorem approveSubscriptionBookkeeping_eq (env : Environment) (id : Nat) (r : UserRequest) (price : Nat) :
    _approveSubscriptionRequest env id r price = (do
      let q ← assetsToShares r.assetAmount price r.asset
      guard (q >= r.sharesAmount) "RequestPriceLowerThanOperatorPrice"
      subscriptionBookkeeping id r .processed
      _mint r.receiver q
      let cfg := (← get).config
      safeTransfer env r.asset cfg.self cfg.portfolioSafe r.assetAmount
      record (.subscription id r q)) := by
  simp only [_approveSubscriptionRequest,subscriptionBookkeeping,bind_assoc]

-- Local counter affordability follows from the finite record sums; it is not
-- substituted as a new top-level settlement premise.
theorem subscriptionBookkeeping_actual (s : State) (n id : Nat) (status : RequestStatus)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hs : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit) :
    subscriptionBookkeeping id (s.requests id) status s = .ok ((),bookkeepingState s id status true) := by
  have hb := valid_subscription_reserved s n id hn hv hk hc
  exact subscription_bookkeeping_run s id status hs ha hb.1 hp hb.2

theorem redemptionBookkeeping_actual (s : State) (n id : Nat) (status : RequestStatus)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true) (hc : RecordsConsistent s n)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit) :
    redemptionBookkeeping id (s.requests id) status s = .ok ((),bookkeepingState s id status false) :=
  redemption_bookkeeping_run s id status hp (valid_pending_count_positive s n id hn hv hc)

-- Complete refund trace and resulting request/counter world, connected to actual
-- conventional-token execution. Neither global roles nor recipients are distinct.
theorem rejectSubscription_success (env : Environment) (s t : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hs : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hap : ExternalApplicability env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) :
    t = {bookkeepingState s id .rejected true with
      external := tokenWordTransfer s.external (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount
      trace := s.trace ++ [.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,
        .rejection id (s.requests id)]} ∧ RecordsConsistent t n ∧
    ExternalApplicability env t ∧
    (∀ x, (assetBalance t (s.requests id).asset x : Int) - assetBalance s (s.requests id).asset x =
      indicator x (s.requests id).investor (s.requests id).assetAmount - indicator x s.config.self (s.requests id).assetAmount) ∧
    (∀ token owner spender, assetAllowance t token owner spender = assetAllowance s token owner spender) := by
  rw [subscriptionBookkeeping_eq] at h
  obtain ⟨u,m,hb,h1⟩ := tx_bind_ok _ _ _ _ _ h
  rw [subscriptionBookkeeping_actual s n id .rejected hn hv hk hc ha hs hp] at hb
  have hm : m = bookkeepingState s id .rejected true := (congrArg Prod.snd (Except.ok.inj hb)).symm
  rw [hm] at h1
  obtain ⟨st,m0,hget,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h2
  obtain ⟨u,z,hpay,h3⟩ := tx_bind_ok _ _ _ _ _ h2
  let b := bookkeepingState s id .rejected true
  have hapb : ExternalApplicability env b := hap
  have hpb := safeTransfer_applicability b z env hapb (s.requests id).asset s.config.self
    (s.requests id).investor hreg htoken (s.requests id).assetAmount ha hpay
  have hpayExact := safeTransfer_success env (s.requests id).asset s.config.self (s.requests id).investor
    (s.requests id).assetAmount b z ha (registered_asset_balance_bounded b env hapb _ _ hreg htoken) hpay
  have ht : t = {z with trace := z.trace ++ [.rejection id (s.requests id)]} := by
    rw [record_run] at h3
    exact (congrArg Prod.snd (Except.ok.inj h3)).symm
  have htExact : t = {bookkeepingState s id .rejected true with
      external := tokenWordTransfer s.external (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount
      trace := s.trace ++ [.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,
        .rejection id (s.requests id)]} := by
    rw [ht,hpayExact.2.2.2.2]
    simp only [b,bookkeepingState,statusState,List.append_assoc,List.cons_append,List.nil_append]
  refine ⟨htExact,?_,?_,?_,?_⟩
  · rw [htExact]
    exact bookkeeping_subscription_consistent s n id .rejected hn (by decide) hv hk hc
  · rw [ht]; exact hpb.1
  · rw [ht]; exact hpb.2.1
  · rw [ht]; exact hpb.2.2

theorem rejectRedemption_success (s t : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hl : LedgerCoherent s)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) :
    ∃ z, _transfer s.config.self (s.requests id).investor (s.requests id).sharesAmount
        (bookkeepingState s id .rejected false) = .ok ((),z) ∧
      t = {z with trace := z.trace ++ [.rejection id (s.requests id)]} ∧
      t.trace = s.trace ++ [.shareTransfer s.config.self (s.requests id).investor (s.requests id).sharesAmount,
        .rejection id (s.requests id)] ∧
      t.requests = (statusState s id .rejected).requests ∧
      RecordsConsistent t n ∧ LedgerCoherent t ∧
      (∀ asset, CallerFrame s t asset) ∧
      t.external = s.external ∧ t.config = s.config ∧
      totalSupply t = totalSupply s ∧
      (∀ x, (shareBalance t x : Int) - shareBalance s x =
        indicator x (s.requests id).investor (s.requests id).sharesAmount - indicator x s.config.self (s.requests id).sharesAmount) := by
  rw [redemptionBookkeeping_eq] at h
  obtain ⟨u,m,hb,h1⟩ := tx_bind_ok _ _ _ _ _ h
  rw [redemptionBookkeeping_actual s n id .rejected hn hv hc hp] at hb
  have hm : m = bookkeepingState s id .rejected false := (congrArg Prod.snd (Except.ok.inj hb)).symm
  rw [hm] at h1
  obtain ⟨st,m0,hget,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h2
  obtain ⟨u,z,hpay,h3⟩ := tx_bind_ok _ _ _ _ _ h2
  let b := bookkeepingState s id .rejected false
  have hpay' : _transfer s.config.self (s.requests id).investor (s.requests id).sharesAmount b = .ok ((),z) := hpay
  have he := transfer_effects b z s.config.self (s.requests id).investor (s.requests id).sharesAmount hl hpay'
  have hx := (transfer_success b z s.config.self (s.requests id).investor (s.requests id).sharesAmount hpay').2.2.2
  have ht : t = {z with trace := z.trace ++ [.rejection id (s.requests id)]} := by
    rw [record_run] at h3
    exact (congrArg Prod.snd (Except.ok.inj h3)).symm
  refine ⟨z,hpay',ht,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht,hx]
    simp [b,bookkeepingState,statusState,shareWrite,List.append_assoc]
  · rw [ht,hx]; rfl
  · rw [ht,hx]
    exact bookkeeping_redemption_consistent s n id .rejected hn (by decide) hv hk hc
  · rw [ht]; exact he.2.2
  · intro asset
    rw [ht]
    have hf := transfer_frame b z s.config.self (s.requests id).investor (s.requests id).sharesAmount asset hpay'
    simpa only [CallerFrame,b,bookkeepingState,statusState] using hf
  · rw [ht,hx]; rfl
  · rw [ht,hx]; rfl
  · rw [ht]; exact he.1
  · rw [ht]; exact he.2.1

theorem approveSubscription_success (env : Environment) (s t : State) (n id price : Nat)
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
    ∃ q, q = Mint (s.requests id).assetAmount price (s.config.assets (s.requests id).asset).decimals ∧
      q ≥ (s.requests id).sharesAmount ∧ q < wordLimit ∧
      t = {mintedState (bookkeepingState s id .processed true) (s.requests id).receiver q with
        external := tokenWordTransfer s.external (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount
        trace := s.trace ++ [.mint (s.requests id).receiver q,
          .assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,
          .subscription id (s.requests id) q]} ∧
      RecordsConsistent t n ∧ FeeInvariant env t ∧ (∀ asset, CallerFrame s t asset) ∧
      (totalSupply t : Int) - totalSupply s = q ∧
      (∀ x, (shareBalance t x : Int) - shareBalance s x = indicator x (s.requests id).receiver q) ∧
      (∀ x, (assetBalance t (s.requests id).asset x : Int) - assetBalance s (s.requests id).asset x =
        indicator x s.config.portfolioSafe (s.requests id).assetAmount - indicator x s.config.self (s.requests id).assetAmount) ∧
      (∀ token owner spender, assetAllowance t token owner spender = assetAllowance s token owner spender) := by
  rw [approveSubscriptionBookkeeping_eq] at h
  obtain ⟨q,m0,hquote,h1⟩ := tx_bind_ok _ _ _ _ _ h
  obtain ⟨hq,hqB,hm0⟩ := assetsToShares_success _ _ _ _ _ _ ha hprice hd hquote
  rw [hm0] at h1
  obtain ⟨u,m1,hguard,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  obtain ⟨hmin,hm1⟩ := guard_success _ _ _ _ _ hguard
  have hminimum : q ≥ (s.requests id).sharesAmount := by simpa using hmin
  rw [hm1] at h2
  obtain ⟨u,b,hbook,h3⟩ := tx_bind_ok _ _ _ _ _ h2
  rw [subscriptionBookkeeping_actual s n id .processed hn hv hk hc ha hs hp] at hbook
  have hb : b = bookkeepingState s id .processed true := (congrArg Prod.snd (Except.ok.inj hbook)).symm
  rw [hb] at h3
  obtain ⟨u,m,hmintRun,h4⟩ := tx_bind_ok _ _ _ _ _ h3
  have hmint : _mint (s.requests id).receiver q (bookkeepingState s id .processed true) = .ok ((),m) := hmintRun
  have hm : m = mintedState (bookkeepingState s id .processed true) (s.requests id).receiver q :=
    (mint_success _ _ _ _ hqB hmint).2.2
  obtain ⟨st,m2,hget,h5⟩ := tx_bind_ok _ _ _ _ _ h4
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h5
  have hmCfg : m.config = s.config := by rw [hm]; rfl
  have hmExt : m.external = s.external := by rw [hm]; rfl
  rw [hmCfg] at h5
  obtain ⟨u,z,hpay,h6⟩ := tx_bind_ok _ _ _ _ _ h5
  have hapm : ExternalApplicability env m := by
    unfold ExternalApplicability
    rw [hmCfg]
    have hbal : assetBalance m = assetBalance s := by funext a x; simp only [assetBalance,hmExt]
    rw [hbal]; exact hi.2.1
  have hregM : (m.config.assets (s.requests id).asset).asset = (s.requests id).asset := by rwa [hmCfg]
  have hpc := safeTransfer_applicability m z env hapm (s.requests id).asset s.config.self s.config.portfolioSafe
    hregM htoken (s.requests id).assetAmount ha hpay
  have hx := (safeTransfer_success env (s.requests id).asset s.config.self s.config.portfolioSafe
    (s.requests id).assetAmount m z ha (registered_asset_balance_bounded m env hapm _ _ hregM htoken) hpay).2.2.2.2
  have ht : t = {z with trace := z.trace ++ [.subscription id (s.requests id) q]} := by
    rw [record_run] at h6
    exact (congrArg Prod.snd (Except.ok.inj h6)).symm
  have htExact : t = {mintedState (bookkeepingState s id .processed true) (s.requests id).receiver q with
      external := tokenWordTransfer s.external (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount
      trace := s.trace ++ [.mint (s.requests id).receiver q,
        .assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,
        .subscription id (s.requests id) q]} := by
    rw [ht,hx,hmExt,hm]
    simp only [mintedState,shareWrite,supplyWrite,bookkeepingState,statusState,List.append_assoc,List.cons_append,List.nil_append]
  have hmEffects := mint_effects (bookkeepingState s id .processed true) m (s.requests id).receiver q hi.1 hqB hmint
  have hmInt := mint_integer_effect (bookkeepingState s id .processed true) m (s.requests id).receiver q hi.1 hqB hmint
  refine ⟨q,hq,hminimum,hqB,htExact,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htExact]
    exact bookkeeping_subscription_consistent s n id .processed hn (by decide) hv hk hc
  · refine ⟨?_,?_,?_⟩
    · rw [ht,hx]; exact hmEffects.2.2
    · rw [ht]; exact hpc.1
    · intro token owner sp hregistered hnonzero
      have hcfgT : t.config = s.config := by rw [htExact]; rfl
      rw [hcfgT] at hregistered
      rw [ht]
      change assetAllowance z token owner sp < wordLimit
      rw [hpc.2.2]
      simpa only [assetAllowance,hmExt] using hi.2.2 token owner sp hregistered hnonzero
  · intro asset
    rw [ht,hx]
    have hf := mint_frame (bookkeepingState s id .processed true) m (s.requests id).receiver q asset hqB hmint
    simpa only [CallerFrame,bookkeepingState,statusState] using hf
  · rw [ht,hx]; exact hmInt.1
  · rw [ht,hx]; exact hmInt.2
  · rw [ht]; simpa only [assetBalance,hmExt] using hpc.2.1
  · rw [ht]; simpa only [assetAllowance,hmExt] using hpc.2.2

def optionalTransfer (fromAddr toAddr : Address) (amount : Nat) : Tx Unit := do
  if amount > 0 then _transfer fromAddr toAddr amount

theorem redemptionFee_success (s t : State) (r : UserRequest) (fee : Nat)
    (ha : r.sharesAmount < wordLimit) (hr : s.config.redemptionFeeRate < wordLimit)
    (h : _chargeRedemptionFee r s = .ok (fee,t)) :
    fee = RedeemFee r.sharesAmount s.config.redemptionFeeRate ∧ fee < wordLimit ∧
    optionalTransfer s.config.self s.config.feeReceiver fee s = .ok ((),t) := by
  simp only [_chargeRedemptionFee] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h1
  obtain ⟨prod,m1,hprod,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  obtain ⟨hbound,hprodEq,hm1⟩ := checkedMul_success _ _ _ _ _ ha hr hprod
  rw [hm1] at h2
  rw [← tx_if_bind] at h2
  obtain ⟨u,m2,htransfer,hpure⟩ := tx_bind_ok _ _ _ _ _ h2
  have heq := tx_pure_state _ _ _ _ hpure
  have hf : fee = prod / bps := heq.1
  have ht : t = m2 := heq.2
  refine ⟨?_,?_,?_⟩
  · rw [hf,hprodEq]; rfl
  · have hh := Nat.div_le_self prod bps; omega
  · rw [ht,hf]
    exact htransfer

theorem optionalTransfer_closure (env : Environment) (s t : State) (fromAddr toAddr : Address) (amount : Nat)
    (hi : FeeInvariant env s)
    (h : optionalTransfer fromAddr toAddr amount s = .ok ((),t)) :
    FeeInvariant env t ∧ FeeDataFrame s t ∧ t.external = s.external ∧
      t.managementFeeLastUpdate = s.managementFeeLastUpdate ∧
      t.performanceFeeLastUpdate = s.performanceFeeLastUpdate ∧
      (∀ asset, CallerFrame s t asset) ∧
      t.trace = s.trace ++ (if amount > 0 then [.shareTransfer fromAddr toAddr amount] else []) := by
  by_cases ha : amount > 0
  · simp only [optionalTransfer,ha,if_true] at h
    have hx := (transfer_success s t fromAddr toAddr amount h).2.2.2
    have he := transfer_effects s t fromAddr toAddr amount hi.1 h
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · refine ⟨he.2.2,?_⟩
      rw [hx]; exact hi.2
    · rw [hx]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    · rw [hx]; rfl
    · rw [hx]; rfl
    · rw [hx]; rfl
    · intro asset; exact transfer_frame s t fromAddr toAddr amount asset h
    · rw [hx]; simp only [ha,if_true]
  · simp only [optionalTransfer,ha,if_false] at h
    have ht := (tx_pure_state _ _ _ _ h).2
    rw [ht]
    exact ⟨hi,by simp [FeeDataFrame],rfl,rfl,rfl,by intro a; simp [CallerFrame],by simp [ha]⟩

-- The witnesses are extracted from actual successful source binds, not new
-- premises. Fee transfer, burn, allowance spending and token payment are linked.
theorem approveRedemption_execution (env : Environment) (s t : State) (n id price : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n)
    (hs : (s.requests id).sharesAmount < wordLimit)
    (hr : s.config.redemptionFeeRate < wordLimit)
    (hp : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hprice : price < wordLimit) (hd : (s.config.assets (s.requests id).asset).decimals ≤ 36)
    (hi : FeeInvariant env s)
    (hreg : (s.config.assets (s.requests id).asset).asset = (s.requests id).asset)
    (htoken : (s.requests id).asset ≠ 0)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) :
    ∃ fee net payout f b z paid,
      fee = RedeemFee (s.requests id).sharesAmount s.config.redemptionFeeRate ∧
      fee ≤ (s.requests id).sharesAmount ∧ net = (s.requests id).sharesAmount - fee ∧
      payout = Out net price (s.config.assets (s.requests id).asset).decimals ∧
      payout ≥ (s.requests id).assetAmount ∧ payout < wordLimit ∧
      optionalTransfer s.config.self s.config.feeReceiver fee s = .ok ((),f) ∧
      b = bookkeepingState f id .processed false ∧
      _burn s.config.self net b = .ok ((),z) ∧
      safeTransferFrom env (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).receiver payout z = .ok ((),paid) ∧
      t = {paid with trace := paid.trace ++ [.redemption id (s.requests id) fee net payout]} ∧
      RecordsConsistent t n ∧ FeeInvariant env t ∧
      t.trace = s.trace ++ (if fee > 0 then [.shareTransfer s.config.self s.config.feeReceiver fee] else []) ++
        [.burn s.config.self net] ++
        (if assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit - 1 then []
          else [.allowanceSpent (s.requests id).asset s.config.portfolioSafe s.config.self payout]) ++
        [.assetTransfer (s.requests id).asset s.config.portfolioSafe (s.requests id).receiver payout,
          .redemption id (s.requests id) fee net payout] := by
  simp only [_approveRedeemRequest] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h1
  rw [← tx_if_bind] at h1
  obtain ⟨fee,f,hfee,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  have hfeeInfo : fee = RedeemFee (s.requests id).sharesAmount s.config.redemptionFeeRate ∧ fee < wordLimit ∧
      optionalTransfer s.config.self s.config.feeReceiver fee s = .ok ((),f) := by
    by_cases hrp : s.config.redemptionFeeRate > 0
    · simp only [hrp,if_true] at hfee
      exact redemptionFee_success s f (s.requests id) fee hs hr hfee
    · simp only [hrp,if_false] at hfee
      have he := tx_pure_state _ _ _ _ hfee
      have hz : s.config.redemptionFeeRate = 0 := by omega
      rw [he.1,he.2]
      exact ⟨by simp [RedeemFee,hz],word_val_lt 0,by simp [optionalTransfer,Pure.pure,StateT.pure,Except.pure]⟩
  have hf := optionalTransfer_closure env s f s.config.self s.config.feeReceiver fee hi hfeeInfo.2.2
  have hcfg : f.config = s.config := hf.2.1.1
  have hreq : f.requests = s.requests := hf.2.1.2.1
  have hcount : f.pendingRequestsCount = s.pendingRequestsCount := hf.2.1.2.2.2.1
  have hfc : RecordsConsistent f n := by simpa only [RecordsConsistent,SubLiability,PendingCount,hreq,hcount,hf.2.1.2.2.1] using hc
  obtain ⟨net,m1,hnet,h3⟩ := tx_bind_ok _ _ _ _ _ h2
  obtain ⟨hfeele,hnetEq,hm1⟩ := checkedSub_success _ _ _ _ _ hs hfeeInfo.2.1 hnet
  rw [hm1] at h3
  have hnB : net < wordLimit := by omega
  obtain ⟨payout,m2,hquote,h4⟩ := tx_bind_ok _ _ _ _ _ h3
  obtain ⟨hpayout,hpayoutB,hm2⟩ := sharesToAssets_success _ _ _ _ _ _ hnB hprice (by rwa [hcfg]) hquote
  rw [hm2] at h4
  obtain ⟨u,m3,hguard,h5⟩ := tx_bind_ok _ _ _ _ _ h4
  obtain ⟨hminimum,hm3⟩ := guard_success _ _ _ _ _ hguard
  rw [hm3] at h5
  obtain ⟨u,b,hstatus,h6⟩ := tx_bind_ok _ _ _ _ _ h5
  obtain ⟨u,b2,hcountRun,h7⟩ := tx_bind_ok _ _ _ _ _ h6
  have hbook : redemptionBookkeeping id (s.requests id) .processed f = .ok ((),b2) :=
    by
      cases u
      simp only [redemptionBookkeeping,Bind.bind,StateT.bind,Except.bind,hstatus]
      exact hcountRun
  have hbookEq : b2 = bookkeepingState f id .processed false := by
    have hh := redemptionBookkeeping_actual f n id .processed hn (by rwa [hreq]) hfc (by rwa [hreq,hcount])
    rw [hreq] at hh
    rw [hh] at hbook
    exact (congrArg Prod.snd (Except.ok.inj hbook)).symm
  obtain ⟨u,z,hburn,h8⟩ := tx_bind_ok _ _ _ _ _ h7
  obtain ⟨u,paid,hpay,h9⟩ := tx_bind_ok _ _ _ _ _ h8
  have ht : t = {paid with trace := paid.trace ++ [.redemption id (s.requests id) fee net payout]} := by
    rw [record_run] at h9
    exact (congrArg Prod.snd (Except.ok.inj h9)).symm
  have hbCfg : b2.config = s.config := by rw [hbookEq]; exact hcfg
  have hbExt : b2.external = s.external := by rw [hbookEq]; exact hf.2.2.1
  have hbLedger : LedgerCoherent b2 := by rw [hbookEq]; exact hf.1.1
  have hxBurn := (burn_success b2 z s.config.self net hburn).2.2
  have hzCfg : z.config = s.config := by rw [hxBurn]; exact hbCfg
  have hzExt : z.external = s.external := by rw [hxBurn]; exact hbExt
  have hzLedger := (burn_effects b2 z s.config.self net hbLedger hburn).2.2.2
  have hzAp : ExternalApplicability env z := by rw [hxBurn,hbookEq]; exact hf.1.2.1
  have hzRanges : RegisteredAllowanceRanges z := by rw [hxBurn,hbookEq]; exact hf.1.2.2
  have hregZ : (z.config.assets (s.requests id).asset).asset = (s.requests id).asset := by rwa [hzCfg]
  have hpayAcc := safeTransferFrom_accounting z paid env hzAp (s.requests id).asset s.config.self s.config.portfolioSafe
    (s.requests id).receiver hregZ htoken payout hpayoutB (hzRanges _ _ _ hregZ htoken) hpay
  have hpayExact := safeTransferFrom_success env (s.requests id).asset s.config.self s.config.portfolioSafe
    (s.requests id).receiver payout z paid hpayoutB
    (registered_asset_balance_bounded z env hzAp _ _ hregZ htoken) (hzRanges _ _ _ hregZ htoken) hpay
  have hpaidShape : ∃ w tr, paid = {z with external := w,trace := tr} := by
    by_cases hal : assetAllowance z (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1
    · rw [if_pos hal] at hpayExact
      exact ⟨_,_,hpayExact.2.2.2.2⟩
    · rw [if_neg hal] at hpayExact
      exact ⟨_,_,hpayExact.2.2.2.2.2⟩
  obtain ⟨w,tr,hpaid⟩ := hpaidShape
  refine ⟨fee,net,payout,f,b2,z,paid,hfeeInfo.1,hfeele,hnetEq,?_,?_,hpayoutB,hfeeInfo.2.2,hbookEq,hburn,hpay,ht,?_,?_,?_⟩
  · simpa only [hcfg] using hpayout
  · simpa using hminimum
  · rw [ht,hpaid,hxBurn,hbookEq]
    have hkind : (f.requests id).requestType = .redemption := by rwa [hreq]
    exact bookkeeping_redemption_consistent f n id .processed hn (by decide) (by rwa [hreq]) hkind hfc
  · refine ⟨?_,?_,?_⟩
    · rw [ht,hpaid]; exact hzLedger
    · rw [ht]; exact hpayAcc.1
    · have hranges := transferFrom_registered_ranges z paid env hzAp (s.requests id).asset s.config.self s.config.portfolioSafe
        (s.requests id).receiver hregZ htoken payout hpayoutB hzRanges hpay
      rw [ht]
      unfold RegisteredAllowanceRanges
      have hconfig : paid.config = z.config := by rw [hpaid]
      rw [hconfig]
      exact hranges
  · rw [ht]
    by_cases hal : assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1
    · have halZ : assetAllowance z (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1 := by
        simpa only [assetAllowance,hzExt] using hal
      rw [if_pos halZ] at hpayExact
      rw [hpayExact.2.2.2.2,hxBurn,hbookEq]
      simp only [bookkeepingState,statusState,hf.2.2.2.2.2.2,hal,if_true,List.append_assoc,List.cons_append,List.nil_append]
    · have halZ : assetAllowance z (s.requests id).asset s.config.portfolioSafe s.config.self ≠ wordLimit-1 := by
        simpa only [assetAllowance,hzExt] using hal
      rw [if_neg halZ] at hpayExact
      rw [hpayExact.2.2.2.2.2,hxBurn,hbookEq]
      simp only [bookkeepingState,statusState,hf.2.2.2.2.2.2,hal,if_false,List.append_assoc,List.cons_append,List.nil_append]

#print axioms approveRedemption_execution
#print axioms approveSubscription_success
#print axioms rejectSubscription_success
#print axioms rejectRedemption_success
end Benchmark.Cases.KPK.SharesSettlementAccounting
