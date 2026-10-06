import Benchmark.Cases.KPK.SharesSettlementAccounting.WorldReplay

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem actualPayments_append (xs ys : List Effect) :
    actualPayments (xs ++ ys) = actualPayments xs ++ actualPayments ys := by
  induction xs with
  | nil => rfl
  | cons e es ih => cases e <;> simp [actualPayments,ih,List.append_assoc]

theorem expectedPayments_append (cfg : Configuration) (xs ys : List Effect) :
    expectedPayments cfg (xs ++ ys) = expectedPayments cfg xs ++ expectedPayments cfg ys := by
  induction xs with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.cons_append,expectedPayments,ih,List.append_assoc]

def EffectRun (s t : State) : Prop :=
  ∃ suffix, t.trace = s.trace ++ suffix ∧
    actualPayments suffix = expectedPayments s.config suffix ∧
    (totalSupply t : Int) - totalSupply s = ((expectedPayments s.config suffix).map supplyEffect).sum ∧
    (∀ x, (shareBalance t x : Int) - shareBalance s x = ((expectedPayments s.config suffix).map (shareEffect x)).sum) ∧
    (∀ token x, (s.config.assets token).asset = token → token ≠ 0 →
      (assetBalance t token x : Int) - assetBalance s token x = ((expectedPayments s.config suffix).map (assetEffect token x)).sum)

theorem effectRun_nil (s : State) : EffectRun s s := by
  refine ⟨[],by simp,rfl,?_,?_,?_⟩
  · simp [expectedPayments]
  · intro x; simp [expectedPayments]
  · intro token x _ _; simp [expectedPayments]

theorem effectRun_trans (s m t : State) (hcfg : m.config = s.config)
    (h1 : EffectRun s m) (h2 : EffectRun m t) : EffectRun s t := by
  obtain ⟨first,hfirst,hpay1,hs1,hsh1,ha1⟩ := h1
  obtain ⟨second,hsecond,hpay2,hs2,hsh2,ha2⟩ := h2
  rw [hcfg] at hpay2 hs2 hsh2 ha2
  refine ⟨first ++ second,by rw [hsecond,hfirst,List.append_assoc],?_,?_,?_,?_⟩
  · rw [actualPayments_append,expectedPayments_append,hpay1,hpay2]
  · rw [expectedPayments_append,List.map_append,List.sum_append,← hs1,← hs2]; omega
  · intro x
    rw [expectedPayments_append,List.map_append,List.sum_append,← hsh1 x,← hsh2 x]; omega
  · intro token x hreg hnz
    rw [expectedPayments_append,List.map_append,List.sum_append,← ha1 token x hreg hnz,← ha2 token x hreg hnz]; omega

theorem rejectedSubscription_effect (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) : EffectRun s t := by
  obtain ⟨hn,ha,_,hreg,htoken,_⟩ := hi.2.2.2.1 id hv
  have hr := rejectSubscription_success env s t n id hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hi.1.2.1 hreg htoken h
  have hd := rejectSubscription_data env s t n id hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hi.1.2.1 hreg htoken h
  have ha := rejectSubscription_vector env s t n id hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hi.1.2.1 hreg htoken h
  refine ⟨[.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,.rejection id (s.requests id)],congrArg State.trace hr.1,?_,?_,?_,?_⟩
  · simp [actualPayments,expectedPayments,hk,show (RequestType.subscription == RequestType.subscription) = true from rfl]
  · simp [expectedPayments,hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,supplyEffect,hd.2.2.2.1]
  · intro x
    simp [expectedPayments,hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,shareEffect,hd.2.2.2.2]
  · intro token x _ _
    simpa [expectedPayments,hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,assetEffect] using ha token x

theorem approvedSubscription_effect (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hp : price < wordLimit)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) : EffectRun s t := by
  obtain ⟨hn,ha,_,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨q,_,_,_,ht,_,_,_,hs,hsh,_⟩ := approveSubscription_success env s t n id price hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  have hav := approveSubscription_vector env s t n id price hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  refine ⟨[.mint (s.requests id).receiver q,.assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,.subscription id (s.requests id) q],congrArg State.trace ht,?_,?_,?_,?_⟩
  · rfl
  · simpa [expectedPayments,supplyEffect] using hs
  · intro x; simpa [expectedPayments,shareEffect] using hsh x
  · intro token x _ _; simpa [expectedPayments,assetEffect] using hav token x


theorem rejectedRedemption_effect (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) : EffectRun s t := by
  obtain ⟨hn,_,_,_,_,_⟩ := hi.2.2.2.1 id hv
  obtain ⟨_,_,_,htrace,_,_,_,_,hext,_,hs,hsh⟩ := rejectRedemption_success s t n id hn hv hk hi.2.1 (hi.2.2.1 _).2 hi.1.1 h
  refine ⟨[.shareTransfer s.config.self (s.requests id).investor (s.requests id).sharesAmount,.rejection id (s.requests id)],htrace,?_,?_,?_,?_⟩
  · simp [actualPayments,expectedPayments,hk,show (RequestType.redemption == RequestType.subscription) = false from rfl]
  · simp [expectedPayments,hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,supplyEffect,hs]
  · intro x
    simpa [expectedPayments,hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,shareEffect] using hsh x
  · intro token x _ _
    simp [expectedPayments,hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,assetEffect,assetBalance,hext]

theorem approvedRedemption_effect (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hp : price < wordLimit)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) : EffectRun s t := by
  obtain ⟨hn,_,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨fee,net,payout,_,_,_,_,hfee,_,hnet,hpayout,_,_,_,_,_,_,_,_,_,htrace⟩ := approveRedemption_execution env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  obtain ⟨fee',net',payout',hfee',hnet',hpayout',_,_,_,hSupply,hShares⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  have hf : fee' = fee := hfee'.trans hfee.symm
  have hnetEq : net' = net := by rw [hnet',hf]; exact hnet.symm
  rw [hnetEq] at hSupply
  rw [hf,hnetEq] at hShares
  obtain ⟨payout'',hpayout'',hAssets,_⟩ := approveRedemption_vector env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  have hpay : payout'' = payout := by rw [hpayout'',← hfee,← hnet]; exact hpayout.symm
  rw [hpay] at hAssets
  refine ⟨(if fee > 0 then [.shareTransfer s.config.self s.config.feeReceiver fee] else []) ++ [.burn s.config.self net] ++ (if assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1 then [] else [.allowanceSpent (s.requests id).asset s.config.portfolioSafe s.config.self payout]) ++ [.assetTransfer (s.requests id).asset s.config.portfolioSafe (s.requests id).receiver payout,.redemption id (s.requests id) fee net payout],by simpa only [List.append_assoc] using htrace,?_,?_,?_,?_⟩
  · split_ifs with h1 h2 <;> simp only [actualPayments,expectedPayments,h1,if_true,if_false,List.nil_append,List.append_assoc,List.cons_append]
  · split_ifs with h1 h2 <;> simpa [expectedPayments,supplyEffect,h1] using hSupply
  · intro x
    by_cases hfee0 : fee > 0
    · split_ifs <;> simpa [expectedPayments,shareEffect,hfee0,sub_eq_add_neg] using hShares x
    · have hz : fee = 0 := by omega
      split_ifs <;> simpa [expectedPayments,shareEffect,hfee0,hz,indicator] using hShares x
  · intro token x _ _
    split_ifs with h1 h2 <;> simpa [expectedPayments,assetEffect,h1] using hAssets token x

#print axioms approvedRedemption_effect
theorem approveOne_effect (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n) (hp : price < wordLimit)
    (h : approveOne env asset price id s = .ok ((),t)) : EffectRun s t := by
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
          exact rejectedSubscription_effect env s t n id hi hv hk h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact rejectedRedemption_effect env s t n id hi hv hk h
      · rw [if_neg hex] at h
        have hstatus : chosenStatus env true (s.requests id) = .processed := by simp [chosenStatus,show env.now ≤ (s.requests id).expiryAt by omega]
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact approvedSubscription_effect env s t n id price hi hv hk hp h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          obtain ⟨_,_,_,_,_,_,hdata,_⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 hc.2 hp hd hi.1 hreg htoken h
          exact approvedRedemption_effect env s t n id price hi hv hk hp h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact effectRun_nil s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact effectRun_nil s

theorem rejectOne_effect (env : Environment) (s t : State) (n id : Nat) (asset : Address)
    (hi : Structural env s n)
    (h : rejectOne env asset id s = .ok ((),t)) : EffectRun s t := by
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
        exact rejectedSubscription_effect env s t n id hi hv hk h
      · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
        exact rejectedRedemption_effect env s t n id hi hv hk h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact effectRun_nil s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact effectRun_nil s


theorem iterate_effect (env : Environment) (body : Nat → Tx Unit) (n : Nat)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (world : ∀ id s t, Structural env s n → body id s = .ok ((),t) → EffectRun s t)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : iterate body ids s = .ok ((),t)) : EffectRun s t := by
  induction ids generalizing s with
  | nil =>
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact effectRun_nil s
  | cons id ids ih =>
    obtain ⟨u,m,hb,hr⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    have hs := step id s m hi hb
    exact effectRun_trans s m t hs.config (world id s m hi hb) (ih m hs.closed hr)

#print axioms iterate_effect
end Benchmark.Cases.KPK.SharesSettlementAccounting
