import Benchmark.Cases.KPK.SharesSettlementAccounting.FeeEffects

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def debitSum (cfg : Configuration) (trace : List Effect) (token owner spender : Address) : Nat :=
  (trace.map fun e => match e with
    | .redemption _ r _ _ payout => if token = r.asset ∧ owner = cfg.portfolioSafe ∧ spender = cfg.self then payout else 0
    | _ => 0).sum

def AllowRun (s t : State) : Prop :=
  ∃ suffix, t.trace = s.trace ++ suffix ∧
    ∀ token owner spender, (s.config.assets token).asset = token → token ≠ 0 →
      if assetAllowance s token owner spender = wordLimit-1 then assetAllowance t token owner spender = wordLimit-1
      else (assetAllowance t token owner spender : Int) - assetAllowance s token owner spender = -(debitSum s.config suffix token owner spender : Int)

theorem allowRun_nil (s : State) : AllowRun s s := by
  refine ⟨[],by simp,?_⟩
  intro token owner spender _ _
  split_ifs <;> simp [debitSum, *]

theorem allowRun_trans (s m t : State) (hcfg : m.config = s.config)
    (ranges : RegisteredAllowanceRanges s) (h1 : AllowRun s m) (h2 : AllowRun m t) : AllowRun s t := by
  obtain ⟨first,hfirst,ha1⟩ := h1
  obtain ⟨second,hsecond,ha2⟩ := h2
  refine ⟨first ++ second,by rw [hsecond,hfirst,List.append_assoc],?_⟩
  intro token owner spender hreg hnz
  have hA := ha1 token owner spender hreg hnz
  have hB := ha2 token owner spender (by rwa [hcfg]) hnz
  by_cases hinf : assetAllowance s token owner spender = wordLimit-1
  · rw [if_pos hinf] at hA ⊢
    rwa [if_pos hA] at hB
  · rw [if_neg hinf] at hA ⊢
    have hb := ranges token owner spender hreg hnz
    have hmid : assetAllowance m token owner spender ≠ wordLimit-1 := by
      have hn : (debitSum s.config first token owner spender : Int) ≥ 0 := Int.natCast_nonneg _
      omega
    rw [if_neg hmid,hcfg] at hB
    have hadd : debitSum s.config (first ++ second) token owner spender = debitSum s.config first token owner spender + debitSum s.config second token owner spender := by simp [debitSum]
    rw [hadd,Int.natCast_add]
    omega

theorem rejectedSubscription_allow (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) : AllowRun s t := by
  obtain ⟨hn,ha,_,hreg,htoken,_⟩ := hi.2.2.2.1 id hv
  have hr := rejectSubscription_success env s t n id hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hi.1.2.1 hreg htoken h
  refine ⟨[.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,.rejection id (s.requests id)],congrArg State.trace hr.1,?_⟩
  intro token owner spender _ _
  rw [hr.2.2.2.2 token owner spender]
  split_ifs <;> simp [debitSum, *]

theorem rejectedRedemption_allow (env : Environment) (s t : State) (n id : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) : AllowRun s t := by
  obtain ⟨hn,_,_,_,_,_⟩ := hi.2.2.2.1 id hv
  have hr := rejectRedemption_success s t n id hn hv hk hi.2.1 (hi.2.2.1 _).2 hi.1.1 h
  obtain ⟨_,_,_,htrace,_,_,_,_,hext,_⟩ := hr
  refine ⟨[.shareTransfer s.config.self (s.requests id).investor (s.requests id).sharesAmount,.rejection id (s.requests id)],htrace,?_⟩
  intro token owner spender _ _
  simp only [assetAllowance,hext]
  split_ifs <;> simp [debitSum, *]

theorem approvedSubscription_allow (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hp : price < wordLimit)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) : AllowRun s t := by
  obtain ⟨hn,ha,_,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨q,_,_,_,ht,_,_,_,_,_,_,hallow⟩ := approveSubscription_success env s t n id price hn hv hk hi.2.1 ha (hi.2.2.1 _).1 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  refine ⟨[.mint (s.requests id).receiver q,.assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,.subscription id (s.requests id) q],congrArg State.trace ht,?_⟩
  intro token owner spender _ _
  rw [hallow token owner spender]
  split_ifs <;> simp [debitSum, *]

theorem approvedRedemption_allow (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hp : price < wordLimit)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) : AllowRun s t := by
  obtain ⟨hn,_,hs,hreg,htoken,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨fee,net,payout,_,_,_,_,hfee,_,hnet,hpayout,_,_,_,_,_,_,_,_,_,htrace⟩ := approveRedemption_execution env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  obtain ⟨payout',hpayout',_,hallow⟩ := approveRedemption_vector env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg htoken h
  have hpEq : payout' = payout := by rw [hpayout',← hfee,← hnet]; exact hpayout.symm
  rw [hpEq] at hallow
  refine ⟨(if fee > 0 then [.shareTransfer s.config.self s.config.feeReceiver fee] else []) ++ [.burn s.config.self net] ++ (if assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1 then [] else [.allowanceSpent (s.requests id).asset s.config.portfolioSafe s.config.self payout]) ++ [.assetTransfer (s.requests id).asset s.config.portfolioSafe (s.requests id).receiver payout,.redemption id (s.requests id) fee net payout],by simpa only [List.append_assoc] using htrace,?_⟩
  intro token owner spender _ _
  have hh := hallow token owner spender
  by_cases hInf : assetAllowance s token owner spender = wordLimit-1
  · rw [if_pos hInf] at hh ⊢; exact hh
  · rw [if_neg hInf] at hh ⊢
    split_ifs with hf hal <;> simp only [debitSum,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,zero_add]
    all_goals by_cases he : token = (s.requests id).asset ∧ owner = s.config.portfolioSafe ∧ spender = s.config.self
    all_goals simpa [he] using hh

theorem approveOne_allow (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n) (hp : price < wordLimit)
    (h : approveOne env asset price id s = .ok ((),t)) : AllowRun s t := by
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
          exact rejectedSubscription_allow env s t n id hi hv hk h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact rejectedRedemption_allow env s t n id hi hv hk h
      · rw [if_neg hex] at h
        have hstatus : chosenStatus env true (s.requests id) = .processed := by simp [chosenStatus,show env.now ≤ (s.requests id).expiryAt by omega]
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact approvedSubscription_allow env s t n id price hi hv hk hp h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          obtain ⟨_,_,_,_,_,_,hdata,_⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 hc.2 hp hd hi.1 hreg htoken h
          exact approvedRedemption_allow env s t n id price hi hv hk hp h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact allowRun_nil s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact allowRun_nil s

theorem rejectOne_allow (env : Environment) (s t : State) (n id : Nat) (asset : Address)
    (hi : Structural env s n)
    (h : rejectOne env asset id s = .ok ((),t)) : AllowRun s t := by
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
        exact rejectedSubscription_allow env s t n id hi hv hk h
      · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
        exact rejectedRedemption_allow env s t n id hi hv hk h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact allowRun_nil s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact allowRun_nil s


theorem iterate_allow (env : Environment) (body : Nat → Tx Unit) (n : Nat)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (world : ∀ id s t, Structural env s n → body id s = .ok ((),t) → AllowRun s t)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : iterate body ids s = .ok ((),t)) : AllowRun s t := by
  induction ids generalizing s with
  | nil =>
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact allowRun_nil s
  | cons id ids ih =>
    obtain ⟨u,m,hb,hr⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    have hs := step id s m hi hb
    exact allowRun_trans s m t hs.config hi.1.2.2 (world id s m hi hb) (ih m hs.closed hr)

#print axioms iterate_allow
end Benchmark.Cases.KPK.SharesSettlementAccounting
