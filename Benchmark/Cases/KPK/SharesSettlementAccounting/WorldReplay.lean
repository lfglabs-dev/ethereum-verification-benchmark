import Benchmark.Cases.KPK.SharesSettlementAccounting.Decisions

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def WorldRun (s t : State) : Prop :=
  ∃ suffix, t.trace = s.trace ++ suffix ∧
    t.external = suffix.foldl (expectedWorldStep s.config) s.external

theorem worldRun_nil (s : State) : WorldRun s s := ⟨[],by simp,rfl⟩

theorem rejectedSubscription_world (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) : WorldRun s t := by
  obtain ⟨hn,ha,_,hreg,htoken,_⟩ := hi.2.2.2.1 id hv
  have ht := (rejectSubscription_success env s t n id hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hi.1.2.1 hreg htoken h).1
  refine ⟨[.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,.rejection id (s.requests id)],congrArg State.trace ht,?_⟩
  rw [ht]
  simp [expectedWorldStep,hk,show (RequestType.subscription == RequestType.subscription) = true from rfl]

theorem rejectedRedemption_world (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) : WorldRun s t := by
  obtain ⟨hn,_,_,_,_,_⟩ := hi.2.2.2.1 id hv
  obtain ⟨_,_,_,htrace,_,_,_,_,hext,_⟩ := rejectRedemption_success s t n id hn hv hk hi.2.1 (hi.2.2.1 _).2 hi.1.1 h
  refine ⟨[.shareTransfer s.config.self (s.requests id).investor (s.requests id).sharesAmount,.rejection id (s.requests id)],htrace,?_⟩
  simpa [expectedWorldStep,hk,show (RequestType.redemption == RequestType.subscription) = false from rfl] using hext

theorem approvedSubscription_world (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hp : price < wordLimit)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) : WorldRun s t := by
  obtain ⟨hn,ha,_,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨q,_,_,_,ht,_⟩ := approveSubscription_success env s t n id price hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  refine ⟨[.mint (s.requests id).receiver q,.assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,.subscription id (s.requests id) q],congrArg State.trace ht,?_⟩
  rw [ht]; rfl

theorem approvedRedemption_world (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hp : price < wordLimit)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) : WorldRun s t := by
  obtain ⟨hn,_,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨fee,net,payout,_,_,_,_,hfee,_,hnet,hpayout,_,_,_,_,_,_,_,_,_,htrace⟩ := approveRedemption_execution env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  obtain ⟨fee',net',payout',hfee',hnet',hpayout',_,_,hworld,_⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  have hf : fee' = fee := hfee'.trans hfee.symm
  have hn : net' = net := by rw [hnet',hf]; exact hnet.symm
  have hpay : payout' = payout := by rw [hpayout',hn]; exact hpayout.symm
  rw [hf,hn,hpay] at hworld
  refine ⟨(if fee > 0 then [.shareTransfer s.config.self s.config.feeReceiver fee] else []) ++ [.burn s.config.self net] ++ (if assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1 then [] else [.allowanceSpent (s.requests id).asset s.config.portfolioSafe s.config.self payout]) ++ [.assetTransfer (s.requests id).asset s.config.portfolioSafe (s.requests id).receiver payout,.redemption id (s.requests id) fee net payout],by simpa only [List.append_assoc] using htrace,?_⟩
  split_ifs <;> simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,expectedWorldStep] using hworld

theorem approveOne_world (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n) (hp : price < wordLimit)
    (h : approveOne env asset price id s = .ok ((),t)) : WorldRun s t := by
  rw [approveOne_dispatch] at h
  by_cases hv : _checkValidRequest (s.requests id) = true
  · obtain ⟨hn,ha,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
    have hc := hi.2.2.1 (s.requests id).asset
    simp only [hv,Bool.not_true,Bool.false_eq_true,if_false] at h
    by_cases hass : (s.requests id).asset = asset
    · have he : eligible s asset id = true := by simp [eligible,hv,hass]
      simp only [show ((s.requests id).asset != asset) = false by simpa using hass,Bool.false_eq_true,if_false] at h
      by_cases hex : env.now > (s.requests id).expiryAt
      · rw [if_pos hex] at h
        have hstatus : chosenStatus env true (s.requests id) = .rejected := by simp [chosenStatus,show ¬env.now ≤ (s.requests id).expiryAt by omega]
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact rejectedSubscription_world env s t n id hi hv hk h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact rejectedRedemption_world env s t n id hi hv hk h
      · rw [if_neg hex] at h
        have hstatus : chosenStatus env true (s.requests id) = .processed := by simp [chosenStatus,show env.now ≤ (s.requests id).expiryAt by omega]
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact approvedSubscription_world env s t n id price hi hv hk hp h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          obtain ⟨_,_,_,_,_,_,hdata,_⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 hc.2 hp hd hi.1 hreg htoken h
          exact approvedRedemption_world env s t n id price hi hv hk hp h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact worldRun_nil s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact worldRun_nil s

theorem rejectOne_world (env : Environment) (s t : State) (n id : Nat) (asset : Address)
    (hi : Structural env s n)
    (h : rejectOne env asset id s = .ok ((),t)) : WorldRun s t := by
  rw [rejectOne_dispatch] at h
  by_cases hv : _checkValidRequest (s.requests id) = true
  · obtain ⟨hn,ha,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
    have hc := hi.2.2.1 (s.requests id).asset
    simp only [hv,Bool.not_true,Bool.false_eq_true,if_false] at h
    by_cases hass : (s.requests id).asset = asset
    · have he : eligible s asset id = true := by simp [eligible,hv,hass]
      simp only [show ((s.requests id).asset != asset) = false by simpa using hass,Bool.false_eq_true,if_false] at h
      cases hk : (s.requests id).requestType
      · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
        exact rejectedSubscription_world env s t n id hi hv hk h
      · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
        exact rejectedRedemption_world env s t n id hi hv hk h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact worldRun_nil s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact worldRun_nil s


theorem worldRun_trans (s m t : State) (hcfg : m.config = s.config)
    (h1 : WorldRun s m) (h2 : WorldRun m t) : WorldRun s t := by
  obtain ⟨first,hfirst,hw1⟩ := h1
  obtain ⟨second,hsecond,hw2⟩ := h2
  exact ⟨first ++ second,by rw [hsecond,hfirst,List.append_assoc],by rw [List.foldl_append,← hw1,← hcfg]; exact hw2⟩

theorem iterate_world (env : Environment) (body : Nat → Tx Unit) (n : Nat)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (world : ∀ id s t, Structural env s n → body id s = .ok ((),t) → WorldRun s t)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : iterate body ids s = .ok ((),t)) : WorldRun s t := by
  induction ids generalizing s with
  | nil =>
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact worldRun_nil s
  | cons id ids ih =>
    obtain ⟨u,m,hb,hr⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    have hs := step id s m hi hb
    exact worldRun_trans s m t hs.config (world id s m hi hb) (ih m hs.closed hr)

#print axioms rejectedSubscription_world
#print axioms rejectedRedemption_world
#print axioms approvedSubscription_world
#print axioms approvedRedemption_world
#print axioms approveOne_world
#print axioms rejectOne_world
#print axioms iterate_world
end Benchmark.Cases.KPK.SharesSettlementAccounting
