import Benchmark.Cases.KPK.SharesSettlementAccounting.HandlerFrames

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

-- Only still-live records need registered-domain/range facts. Successful handlers
-- remove records; no claim that global external Nat cells or escrow are inductive.
def LiveDomain (s : State) (n : Nat) : Prop :=
  ∀ id, _checkValidRequest (s.requests id) = true →
    id < n ∧ (s.requests id).assetAmount < wordLimit ∧ (s.requests id).sharesAmount < wordLimit ∧
    (s.config.assets (s.requests id).asset).asset = (s.requests id).asset ∧
    (s.requests id).asset ≠ 0 ∧ (s.config.assets (s.requests id).asset).decimals ≤ 36

def CounterRanges (s : State) : Prop :=
  ∀ asset, s.subscriptionAssets asset < wordLimit ∧ s.pendingRequestsCount asset < wordLimit

def Structural (env : Environment) (s : State) (n : Nat) : Prop :=
  FeeInvariant env s ∧ RecordsConsistent s n ∧ CounterRanges s ∧ LiveDomain s n ∧
  s.config.redemptionFeeRate < wordLimit

theorem valid_pending (r : UserRequest) (hv : _checkValidRequest r = true) :
    r.requestStatus = .pending := by
  have hs : (r.requestStatus == RequestStatus.pending) = true := by
    simp only [_checkValidRequest,Bool.and_eq_true] at hv
    exact hv.2
  cases h : r.requestStatus
  · rfl
  · rw [h] at hs; change false = true at hs; cases hs
  · rw [h] at hs; change false = true at hs; cases hs
  · rw [h] at hs; change false = true at hs; cases hs

theorem terminal_invalid (r : UserRequest) (ht : r.requestStatus ≠ .pending) :
    _checkValidRequest r = false := by
  cases h : r.requestStatus
  · exact False.elim (ht h)
  · simp only [_checkValidRequest,h,show (RequestStatus.processed == RequestStatus.pending) = false from rfl,Bool.and_false]
  · simp only [_checkValidRequest,h,show (RequestStatus.rejected == RequestStatus.pending) = false from rfl,Bool.and_false]
  · simp only [_checkValidRequest,h,show (RequestStatus.cancelled == RequestStatus.pending) = false from rfl,Bool.and_false]

theorem wellFormed_structural (env : Environment) (s : State) (n : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) : Structural env s n := by
  rcases hw with ⟨_,hl,hrecords,_,_,_,_,_,_,_,hrrate,_,_,_,_,hcounters,hassets,_,hallowances,houtside,hrequests,_,_⟩
  refine ⟨⟨hl,hap,by intro a o sp _ _; exact hallowances a o sp⟩,hrecords,hcounters,?_,?_⟩
  · intro id hv
    have hn : id < n := by
      by_contra hn
      have hh := houtside id (by omega)
      rw [hh] at hv
      change false = true at hv
      cases hv
    have hr := hrequests id hn
    have hnotdefault : s.requests id ≠ default := by
      intro hh; rw [hh] at hv; change false = true at hv; cases hv
    rcases hr.2.2.2.2 with hdefault | hreal
    · exact False.elim (hnotdefault hdefault)
    · rcases hreal with ⟨_,_,_,_,hasset,_,hregistered⟩
      exact ⟨hn,hr.1,hr.2.1,hregistered (valid_pending _ hv),hasset,(hassets _).1⟩
  · have hbig : 2000 < wordLimit := by norm_num [wordLimit]
    omega

theorem handlerData_structural (env : Environment) (s t : State) (n id : Nat)
    (status : RequestStatus) (isSub : Bool) (ht : status ≠ .pending)
    (hi : Structural env s n) (hd : HandlerData s t id status isSub)
    (hfi : FeeInvariant env t) (hrc : RecordsConsistent t n) : Structural env t n := by
  rcases hd with ⟨hcfg,hreq,hsub,hcount,_,_,_⟩
  refine ⟨hfi,hrc,?_,?_,by rw [hcfg]; exact hi.2.2.2.2⟩
  · intro a
    rw [hsub,hcount]
    dsimp only [bookkeepingState,statusState]
    have hb := hi.2.2.1 a
    split <;> split <;> omega
  · intro j hv
    have hj : j ≠ id := by
      intro hh; subst j
      rw [hreq] at hv
      have hs : ((statusState s id status).requests id).requestStatus = status := by simp [statusState]
      have hp := valid_pending _ hv
      rw [hs] at hp
      exact ht hp
    have hjr : t.requests j = s.requests j := by rw [hreq]; exact statusState_other s id j status hj
    rw [hjr] at hv
    rw [hjr,hcfg]
    exact hi.2.2.2.1 j hv

-- A record-only transition includes real execution frames and the exact suffix
-- decision. It is not assumed by the central theorem: branch lemmas derive it.
structure RecordTransition (env : Environment) (s t : State) (n id : Nat) : Prop where
  closed : Structural env t n
  config : t.config = s.config
  price : t.lastSettledPrice = s.lastSettledPrice
  management : t.managementFeeLastUpdate = s.managementFeeLastUpdate
  performance : t.performanceFeeLastUpdate = s.performanceFeeLastUpdate
  caller : ∀ asset, CallerFrame s t asset
  outcome : t = s ∨ ∃ status isSub suffix,
    status ≠ .pending ∧ (s.requests id).requestStatus = .pending ∧ HandlerData s t id status isSub ∧
    t.trace = s.trace ++ suffix ∧ actualDecisions suffix = [⟨id,status⟩] ∧ consumed suffix = [id] ∧
    (∀ e, e ∈ suffix → isFeeMarker e = false)

theorem recordTransition_noop (env : Environment) (s : State) (n id : Nat)
    (hi : Structural env s n) : RecordTransition env s s n id :=
  ⟨hi,rfl,rfl,rfl,rfl,by intro a; simp [CallerFrame],Or.inl rfl⟩

theorem recordTransition_handled (env : Environment) (s t : State) (n id : Nat)
    (status : RequestStatus) (isSub : Bool) (suffix : List Effect)
    (hi : Structural env s n) (ht : status ≠ .pending) (hv : _checkValidRequest (s.requests id) = true)
    (hd : HandlerData s t id status isSub) (hfi : FeeInvariant env t) (hrc : RecordsConsistent t n)
    (hf : ∀ asset, CallerFrame s t asset)
    (htrace : t.trace = s.trace ++ suffix) (hdec : actualDecisions suffix = [⟨id,status⟩])
    (hcons : consumed suffix = [id]) (hmarker : ∀ e, e ∈ suffix → isFeeMarker e = false) :
    RecordTransition env s t n id :=
  ⟨handlerData_structural env s t n id status isSub ht hi hd hfi hrc,
    hd.1,hd.2.2.2.2.1,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2,hf,
    Or.inr ⟨status,isSub,suffix,ht,valid_pending _ hv,hd,htrace,hdec,hcons,hmarker⟩⟩

theorem rejectedSubscription_transition (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) : RecordTransition env s t n id := by
  obtain ⟨hn,ha,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  have hc := hi.2.2.1 (s.requests id).asset
  have hr := rejectSubscription_success env s t n id hn hv hk hi.2.1 ha hc.1 hc.2 hi.1.2.1 hreg htoken h
  have hf := rejectSubscription_data env s t n id hn hv hk hi.2.1 ha hc.1 hc.2 hi.1.2.1 hreg htoken h
  have hfi : FeeInvariant env t := by
    refine ⟨?_,hr.2.2.1,?_⟩
    · rw [hr.1]; exact hi.1.1
    · intro token owner sp hregistered hnonzero
      rw [hf.1.1] at hregistered
      rw [hr.2.2.2.2]
      exact hi.1.2.2 token owner sp hregistered hnonzero
  refine recordTransition_handled env s t n id .rejected true
    [.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,
      .rejection id (s.requests id)] hi (by decide) hv hf.1 hfi hr.2.1 hf.2.1 ?_ rfl rfl ?_
  · exact congrArg State.trace hr.1
  · intro e he; simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> rfl

theorem rejectedRedemption_transition (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) : RecordTransition env s t n id := by
  obtain ⟨hn,_,_,_,_,_⟩ := hi.2.2.2.1 id hv
  obtain ⟨z,hpay,ht,htrace,hreq,hrc,hl,hframe,hext,hcfg,_⟩ :=
    rejectRedemption_success s t n id hn hv hk hi.2.1 (hi.2.2.1 _).2 hi.1.1 h
  have hd := (rejectRedemption_data s t n id hn hv hk hi.2.1 (hi.2.2.1 _).2 hi.1.1 h).1
  have hfi : FeeInvariant env t := by
    refine ⟨hl,?_,?_⟩
    · unfold ExternalApplicability
      rw [hcfg]
      have hb : assetBalance t = assetBalance s := by funext a x; simp only [assetBalance,hext]
      rw [hb]; exact hi.1.2.1
    · unfold RegisteredAllowanceRanges
      rw [hcfg]
      have ha : assetAllowance t = assetAllowance s := by funext a o sp; simp only [assetAllowance,hext]
      rw [ha]; exact hi.1.2.2
  apply recordTransition_handled env s t n id .rejected false
    [.shareTransfer s.config.self (s.requests id).investor (s.requests id).sharesAmount,
      .rejection id (s.requests id)] hi (by decide) hv hd hfi hrc hframe htrace
  · rfl
  · rfl
  · intro e he; simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at he
    rcases he with rfl | rfl <;> rfl

theorem approvedSubscription_transition (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hprice : price < wordLimit)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) : RecordTransition env s t n id := by
  obtain ⟨hn,ha,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  have hc := hi.2.2.1 (s.requests id).asset
  obtain ⟨q,_,_,_,ht,hrc,hfi,hframe,_⟩ :=
    approveSubscription_success env s t n id price hn hv hk hi.2.1 ha hc.1 hc.2 hprice hd hi.1 hreg htoken h
  have hf := (approveSubscription_data env s t n id price hn hv hk hi.2.1 ha hc.1 hc.2 hprice hd hi.1 hreg htoken h).1
  apply recordTransition_handled env s t n id .processed true
    [.mint (s.requests id).receiver q,
      .assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,
      .subscription id (s.requests id) q] hi (by decide) hv hf hfi hrc hframe
  · exact congrArg State.trace ht
  · rfl
  · rfl
  · intro e he; simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at he
    rcases he with rfl | rfl | rfl <;> rfl

theorem approvedRedemption_transition (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hprice : price < wordLimit)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) : RecordTransition env s t n id := by
  obtain ⟨hn,ha,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨fee,net,payout,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hrc,hfi,htrace⟩ :=
    approveRedemption_execution env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hprice hd hi.1 hreg htoken h
  obtain ⟨fee',net',payout',_,_,_,hf,hframe,_⟩ :=
    approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hprice hd hi.1 hreg htoken h
  apply recordTransition_handled env s t n id .processed false
    ((if fee > 0 then [.shareTransfer s.config.self s.config.feeReceiver fee] else []) ++
      [.burn s.config.self net] ++
      (if assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1 then []
        else [.allowanceSpent (s.requests id).asset s.config.portfolioSafe s.config.self payout]) ++
      [.assetTransfer (s.requests id).asset s.config.portfolioSafe (s.requests id).receiver payout,
        .redemption id (s.requests id) fee net payout]) hi (by decide) hv hf hfi hrc hframe
  · simpa only [List.append_assoc] using htrace
  · split_ifs <;> rfl
  · split_ifs <;> rfl
  · intro e he
    split_ifs at he <;> simp only [List.mem_append,List.mem_cons,List.not_mem_nil,false_or,or_false,or_assoc] at he
    all_goals rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl


theorem approveOne_record (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n) (hp : price < wordLimit)
    (h : approveOne env asset price id s = .ok ((),t)) : RecordTransition env s t n id := by
  rw [approveOne_dispatch] at h
  by_cases hv : _checkValidRequest (s.requests id) = true
  · simp only [hv,Bool.not_true,Bool.false_eq_true,if_false] at h
    by_cases ha : (s.requests id).asset = asset
    · simp only [show ((s.requests id).asset != asset) = false by simpa using ha,Bool.false_eq_true,if_false] at h
      by_cases hex : env.now > (s.requests id).expiryAt
      · rw [if_pos hex] at h
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact rejectedSubscription_transition env s t n id hi hv hk h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact rejectedRedemption_transition env s t n id hi hv hk h
      · rw [if_neg hex] at h
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact approvedSubscription_transition env s t n id price hi hv hk hp h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact approvedRedemption_transition env s t n id price hi hv hk hp h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using ha,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]; exact recordTransition_noop env s n id hi
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact recordTransition_noop env s n id hi

theorem rejectOne_record (env : Environment) (s t : State) (n id : Nat) (asset : Address)
    (hi : Structural env s n)
    (h : rejectOne env asset id s = .ok ((),t)) : RecordTransition env s t n id := by
  rw [rejectOne_dispatch] at h
  by_cases hv : _checkValidRequest (s.requests id) = true
  · simp only [hv,Bool.not_true,Bool.false_eq_true,if_false] at h
    by_cases ha : (s.requests id).asset = asset
    · simp only [show ((s.requests id).asset != asset) = false by simpa using ha,Bool.false_eq_true,if_false] at h
      cases hk : (s.requests id).requestType
      · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
        exact rejectedSubscription_transition env s t n id hi hv hk h
      · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
        exact rejectedRedemption_transition env s t n id hi hv hk h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using ha,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]; exact recordTransition_noop env s n id hi
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact recordTransition_noop env s n id hi

theorem payload_refl (r : UserRequest) : Payload r r := by simp [Payload]

theorem payload_trans (r q u : UserRequest) (h1 : Payload r q) (h2 : Payload q u) : Payload r u := by
  rcases h1 with ⟨a,b,c,d,e,f,g,h⟩
  rcases h2 with ⟨i,j,k,l,m,n,o,p⟩
  exact ⟨a.trans i,b.trans j,c.trans k,d.trans l,e.trans m,f.trans n,g.trans o,h.trans p⟩

theorem recordTransition_requests (env : Environment) (s t : State) (n id : Nat)
    (h : RecordTransition env s t n id) :
    (∀ j, Payload (s.requests j) (t.requests j)) ∧
    (∀ j, (s.requests j).requestStatus ≠ .pending → t.requests j = s.requests j) ∧
    (∀ j, j ≠ id → t.requests j = s.requests j) := by
  rcases h.outcome with ht | ⟨status,isSub,suffix,ht,hpending,hd,_⟩
  · rw [ht]; exact ⟨by intro j; exact payload_refl _,by intros; rfl,by intros; rfl⟩
  · have hreq := hd.2.1
    refine ⟨?_,?_,?_⟩
    · intro j; rw [hreq]; exact statusState_payload s id j status
    · intro j hj; rw [hreq]; exact statusState_terminal_untouched s id j status hpending hj
    · intro j hj; rw [hreq]; exact statusState_other s id j status hj

-- Full original record equality is now derived from current-pending dispatch,
-- payload stability AND preservation of originally terminal statuses.
theorem current_pending_original (s t : State) (id : Nat)
    (hpayload : Payload (s.requests id) (t.requests id))
    (hterminal : (s.requests id).requestStatus ≠ .pending → t.requests id = s.requests id)
    (hpending : (t.requests id).requestStatus = .pending) : t.requests id = s.requests id := by
  have hs : (s.requests id).requestStatus = .pending := by
    by_contra hs
    rw [hterminal hs] at hpending
    exact hs hpending
  exact (payload_pending_full _ _ hpayload hs hpending).symm


theorem consumed_append (xs ys : List Effect) : consumed (xs ++ ys) = consumed xs ++ consumed ys := by
  induction xs with
  | nil => rfl
  | cons e xs ih => cases e <;> simp [consumed,ih,List.append_assoc]

theorem actualDecisions_append (xs ys : List Effect) :
    actualDecisions (xs ++ ys) = actualDecisions xs ++ actualDecisions ys := by
  induction xs with
  | nil => rfl
  | cons e xs ih => cases e <;> simp [actualDecisions,ih,List.append_assoc]

theorem consumed_decisions (xs : List Effect) : consumed xs = (actualDecisions xs).map Decision.id := by
  induction xs with
  | nil => rfl
  | cons e xs ih => cases e <;> simp [consumed,actualDecisions,ih]

structure RecordRun (env : Environment) (s t : State) (n : Nat) (ids : List Nat) : Prop where
  closed : Structural env t n
  config : t.config = s.config
  price : t.lastSettledPrice = s.lastSettledPrice
  management : t.managementFeeLastUpdate = s.managementFeeLastUpdate
  performance : t.performanceFeeLastUpdate = s.performanceFeeLastUpdate
  caller : ∀ asset, CallerFrame s t asset
  suffix : ∃ suffix, t.trace = s.trace ++ suffix ∧
    (∀ e, e ∈ suffix → isFeeMarker e = false) ∧
    (consumed suffix).Nodup ∧
    (∀ j, j ∈ consumed suffix → j ∈ ids) ∧
    (∀ j, Payload (s.requests j) (t.requests j)) ∧
    (∀ j, (s.requests j).requestStatus ≠ .pending → t.requests j = s.requests j) ∧
    (∀ j, j ∈ consumed suffix → (s.requests j).requestStatus = .pending) ∧
    (∀ j, j ∈ consumed suffix → (t.requests j).requestStatus ≠ .pending) ∧
    (∀ j, j ∉ consumed suffix → t.requests j = s.requests j)

theorem recordRun_nil (env : Environment) (s : State) (n : Nat) (hi : Structural env s n) :
    RecordRun env s s n [] := by
  refine ⟨hi,rfl,rfl,rfl,rfl,by intro a; simp [CallerFrame],?_⟩
  refine ⟨[],?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> simp [consumed,Payload]

theorem recordRun_cons (env : Environment) (s m t : State) (n id : Nat) (ids : List Nat)
    (hstep : RecordTransition env s m n id) (hrest : RecordRun env m t n ids) :
    RecordRun env s t n (id::ids) := by
  refine ⟨hrest.closed,hrest.config.trans hstep.config,hrest.price.trans hstep.price,
    hrest.management.trans hstep.management,hrest.performance.trans hstep.performance,
    by intro a; exact callerFrame_trans s m t a (hstep.caller a) (hrest.caller a),?_⟩
  obtain ⟨rest,htrace,hmarker,hnodup,hsubset,hpayload,hterminal,hpending,hfinal,huntouched⟩ := hrest.suffix
  have hrequest := recordTransition_requests env s m n id hstep
  rcases hstep.outcome with heq | ⟨status,isSub,first,ht,hspending,hdata,hfirst,hdec,hcons,hmark⟩
  · subst m
    exact ⟨rest,htrace,hmarker,hnodup,by intro j hj; exact List.mem_cons_of_mem id (hsubset j hj),
      hpayload,hterminal,hpending,hfinal,huntouched⟩
  · have hmStatus : (m.requests id).requestStatus = status := by rw [hdata.2.1]; simp [statusState]
    have hid : id ∉ consumed rest := by
      intro hh
      have hp := hpending id hh
      rw [hmStatus] at hp
      exact ht hp
    refine ⟨first ++ rest,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [htrace,hfirst,List.append_assoc]
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hmark e he
      · exact hmarker e he
    · rw [consumed_append,hcons]
      exact List.nodup_cons.mpr ⟨hid,hnodup⟩
    · intro j hj
      rw [consumed_append,hcons] at hj
      rcases List.mem_cons.mp hj with he | he
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem id (hsubset j he)
    · intro j
      exact payload_trans _ _ _ (hrequest.1 j) (hpayload j)
    · intro j hj
      have hm := hrequest.2.1 j hj
      have hmj : (m.requests j).requestStatus ≠ .pending := by rw [hm]; exact hj
      exact (hterminal j hmj).trans hm
    · intro j hj
      rw [consumed_append,hcons] at hj
      rcases List.mem_cons.mp hj with he | he
      · subst j; exact hspending
      · have hp := hpending j he
        have horig := current_pending_original s m j (hrequest.1 j) (hrequest.2.1 j) hp
        rw [horig] at hp; exact hp
    · intro j hj
      rw [consumed_append,hcons] at hj
      rcases List.mem_cons.mp hj with he | he
      · subst j
        have hmj : (m.requests id).requestStatus ≠ .pending := by rw [hmStatus]; exact ht
        rw [hterminal id hmj]; exact hmj
      · exact hfinal j he
    · intro j hj
      have hnotfirst : j ≠ id := by
        intro he; subst j; exact hj (by simp [consumed_append,hcons])
      have hnotrest : j ∉ consumed rest := by
        intro he; exact hj (by simp [consumed_append,hcons,he])
      exact (huntouched j hnotrest).trans (hrequest.2.2 j hnotfirst)

-- Real recursive execution, not an assumed step result or finite unrolling.
theorem iterate_recordRun (env : Environment) (body : Nat → Tx Unit) (n : Nat)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : iterate body ids s = .ok ((),t)) : RecordRun env s t n ids := by
  induction ids generalizing s with
  | nil =>
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact recordRun_nil env s n hi
  | cons id ids ih =>
    simp only [iterate] at h
    obtain ⟨u,m,hstep,hrest⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    have hs := step id s m hi hstep
    exact recordRun_cons env s m t n id ids hs (ih m hs.closed hrest)

theorem approved_recordRun (env : Environment) (s t : State) (n price : Nat) (asset : Address)
    (ids : List Nat) (hi : Structural env s n) (hp : price < wordLimit)
    (h : _processApproved env ids asset price s = .ok ((),t)) : RecordRun env s t n ids :=
  iterate_recordRun env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h) ids s t hi h

theorem rejected_recordRun (env : Environment) (s t : State) (n : Nat) (asset : Address)
    (ids : List Nat) (hi : Structural env s n)
    (h : _processRejected env ids asset s = .ok ((),t)) : RecordRun env s t n ids :=
  iterate_recordRun env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h) ids s t hi h


theorem recordRun_trans (env : Environment) (s m t : State) (n : Nat) (xs ys : List Nat)
    (hfirst : RecordRun env s m n xs) (hsecond : RecordRun env m t n ys) :
    RecordRun env s t n (xs ++ ys) := by
  refine ⟨hsecond.closed,hsecond.config.trans hfirst.config,hsecond.price.trans hfirst.price,
    hsecond.management.trans hfirst.management,hsecond.performance.trans hfirst.performance,
    by intro a; exact callerFrame_trans s m t a (hfirst.caller a) (hsecond.caller a),?_⟩
  obtain ⟨first,htrace1,hmarker1,hnodup1,hsubset1,hpayload1,hterminal1,hpending1,hfinal1,huntouched1⟩ := hfirst.suffix
  obtain ⟨second,htrace2,hmarker2,hnodup2,hsubset2,hpayload2,hterminal2,hpending2,hfinal2,huntouched2⟩ := hsecond.suffix
  have hdisjoint : List.Disjoint (consumed first) (consumed second) := by
    intro id hf hs
    exact hfinal1 id hf (hpending2 id hs)
  refine ⟨first ++ second,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htrace2,htrace1,List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hmarker1 e he
    · exact hmarker2 e he
  · rw [consumed_append]
    exact List.nodup_append.mpr ⟨hnodup1,hnodup2,by intro a ha b hb he; subst b; exact hdisjoint ha hb⟩
  · intro j hj
    rw [consumed_append] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact List.mem_append.mpr (Or.inl (hsubset1 j hj))
    · exact List.mem_append.mpr (Or.inr (hsubset2 j hj))
  · intro j; exact payload_trans _ _ _ (hpayload1 j) (hpayload2 j)
  · intro j hj
    have hm := hterminal1 j hj
    have hmj : (m.requests j).requestStatus ≠ .pending := by rw [hm]; exact hj
    exact (hterminal2 j hmj).trans hm
  · intro j hj
    rw [consumed_append] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hpending1 j hj
    · have hp := hpending2 j hj
      have horig := current_pending_original s m j (hpayload1 j) (hterminal1 j) hp
      rw [horig] at hp; exact hp
  · intro j hj
    rw [consumed_append] at hj
    rcases List.mem_append.mp hj with hj | hj
    · have hm := hfinal1 j hj
      rw [hterminal2 j hm]; exact hm
    · exact hfinal2 j hj
  · intro j hj
    have hn1 : j ∉ consumed first := by intro hh; exact hj (by simp [consumed_append,hh])
    have hn2 : j ∉ consumed second := by intro hh; exact hj (by simp [consumed_append,hh])
    exact (huntouched2 j hn2).trans (huntouched1 j hn1)

theorem feeData_structural (env : Environment) (s t : State) (n : Nat)
    (hi : Structural env s n) (hd : FeeDataFrame s t) (hf : FeeInvariant env t) : Structural env t n := by
  rcases hd with ⟨hcfg,hreq,hsub,hcount,_⟩
  refine ⟨hf,?_,?_,?_,?_⟩
  · simpa only [RecordsConsistent,SubLiability,PendingCount,hreq,hsub,hcount] using hi.2.1
  · simpa only [CounterRanges,hsub,hcount] using hi.2.2.1
  · simpa only [LiveDomain,hreq,hcfg] using hi.2.2.2.1
  · rw [hcfg]; exact hi.2.2.2.2

#print axioms wellFormed_structural
#print axioms handlerData_structural
#print axioms approveOne_record
#print axioms rejectOne_record
#print axioms current_pending_original
#print axioms approved_recordRun
#print axioms rejected_recordRun
#print axioms recordRun_trans
#print axioms feeData_structural
end Benchmark.Cases.KPK.SharesSettlementAccounting
