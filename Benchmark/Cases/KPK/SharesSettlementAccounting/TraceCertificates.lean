import Benchmark.Cases.KPK.SharesSettlementAccounting.ConversionBounds

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def eventPending (s : State) : Effect → Prop
  | .subscription id _ _ | .redemption id _ _ _ _ | .rejection id _ => (s.requests id).requestStatus = .pending
  | _ => True

def CorrectRun (cfg : Configuration) (price : Nat) (s t : State) : Prop :=
  ∃ suffix, t.trace = s.trace ++ suffix ∧
    ∀ e, e ∈ suffix → ConversionCorrect cfg price e ∧ TraceRequestCorrect s t e ∧ eventPending s e

theorem correctRun_nil (cfg : Configuration) (price : Nat) (s : State) : CorrectRun cfg price s s :=
  ⟨[],by simp,by simp⟩

theorem correctRun_trans (cfg : Configuration) (price : Nat) (s m t : State)
    (hp : ∀ id, Payload (s.requests id) (m.requests id))
    (hs : ∀ id, (s.requests id).requestStatus ≠ .pending → m.requests id = s.requests id)
    (hm : ∀ id, (m.requests id).requestStatus ≠ .pending → t.requests id = m.requests id)
    (h1 : CorrectRun cfg price s m) (h2 : CorrectRun cfg price m t) : CorrectRun cfg price s t := by
  obtain ⟨first,hfirst,h1⟩ := h1
  obtain ⟨second,hsecond,h2⟩ := h2
  refine ⟨first ++ second,by rw [hsecond,hfirst,List.append_assoc],?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨hc,hr,hn⟩ := h1 e he
    refine ⟨hc,?_,hn⟩
    cases e <;> simp only [TraceRequestCorrect] at hr ⊢
    all_goals first | trivial | (rcases hr with ⟨hr,hk,hfinal⟩; refine ⟨hr,hk,?_⟩; rw [hm _ (by rw [hfinal]; decide)]; exact hfinal) | (rcases hr with ⟨hr,hfinal⟩; refine ⟨hr,?_⟩; rw [hm _ (by rw [hfinal]; decide)]; exact hfinal)
  · obtain ⟨hc,hr,hn⟩ := h2 e he
    refine ⟨hc,?_,?_⟩
    all_goals cases e <;> simp only [TraceRequestCorrect,eventPending] at hr hn ⊢
    all_goals first | trivial | (have heq := current_pending_original s m _ (hp _) (hs _) hn; simpa only [heq] using hr) | (have heq := current_pending_original s m _ (hp _) (hs _) hn; simpa only [heq] using hn)

theorem rejectedSubscription_correct (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription)
    (h : _rejectSubscriptionRequest env id (s.requests id) s = .ok ((),t)) : CorrectRun s.config price s t := by
  obtain ⟨hn,ha,_,hreg,hnz,_⟩ := hi.2.2.2.1 id hv
  have hc := hi.2.2.1 (s.requests id).asset
  have he := rejectSubscription_success env s t n id hn hv hk hi.2.1 ha hc.1 hc.2 hi.1.2.1 hreg hnz h
  have hd := (rejectSubscription_data env s t n id hn hv hk hi.2.1 ha hc.1 hc.2 hi.1.2.1 hreg hnz h).1
  refine ⟨[.assetTransfer (s.requests id).asset s.config.self (s.requests id).investor (s.requests id).assetAmount,.rejection id (s.requests id)],congrArg State.trace he.1,?_⟩
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · trivial
  · simp [ConversionCorrect,TraceRequestCorrect,eventPending,hd.2.1,statusState,valid_pending _ hv]

theorem rejectedRedemption_correct (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption)
    (h : _rejectRedeemRequest id (s.requests id) s = .ok ((),t)) : CorrectRun s.config price s t := by
  obtain ⟨hn,_,_,_,_,_⟩ := hi.2.2.2.1 id hv
  obtain ⟨z,_,_,htrace,hreq,_⟩ := rejectRedemption_success s t n id hn hv hk hi.2.1 (hi.2.2.1 _).2 hi.1.1 h
  refine ⟨[.shareTransfer s.config.self (s.requests id).investor (s.requests id).sharesAmount,.rejection id (s.requests id)],htrace,?_⟩
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · trivial
  · simp [ConversionCorrect,TraceRequestCorrect,eventPending,hreq,statusState,valid_pending _ hv]

theorem approvedSubscription_correct (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hp : price < wordLimit)
    (h : _approveSubscriptionRequest env id (s.requests id) price s = .ok ((),t)) : CorrectRun s.config price s t := by
  obtain ⟨hn,ha,_,hreg,hnz,hd⟩ := hi.2.2.2.1 id hv
  have hc := hi.2.2.1 (s.requests id).asset
  obtain ⟨q,hq,hmin,_,ht,_⟩ := approveSubscription_success env s t n id price hn hv hk hi.2.1 ha hc.1 hc.2 hp hd hi.1 hreg hnz h
  refine ⟨[.mint (s.requests id).receiver q,.assetTransfer (s.requests id).asset s.config.self s.config.portfolioSafe (s.requests id).assetAmount,.subscription id (s.requests id) q],congrArg State.trace ht,?_⟩
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at he
  rcases he with rfl | rfl | rfl
  · trivial
  · trivial
  · refine ⟨⟨hq,hmin,?_⟩,?_,valid_pending _ hv⟩
    · intro hpos; rw [hq]; exact Mint_floor_bounds _ _ _ hpos
    · simp [TraceRequestCorrect,ht,bookkeepingState,statusState,mintedState,shareWrite,supplyWrite,hk]

theorem approvedRedemption_correct (env : Environment) (s t : State) (n id price : Nat)
    (hi : Structural env s n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .redemption) (hp : price < wordLimit)
    (h : _approveRedeemRequest env id (s.requests id) price s = .ok ((),t)) : CorrectRun s.config price s t := by
  obtain ⟨hn,_,hs,hreg,hnz,hd⟩ := hi.2.2.2.1 id hv
  obtain ⟨fee,net,payout,f,b,z,paid,hfee,_,hnet,hout,hmin,_,_,_,_,_,_,_,_,htrace⟩ :=
    approveRedemption_execution env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg hnz h
  have hreq := (approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 (hi.2.2.1 _).2 hp hd hi.1 hreg hnz h).choose_spec.choose_spec.choose_spec.2.2.2.1.2.1
  refine ⟨(if fee > 0 then [.shareTransfer s.config.self s.config.feeReceiver fee] else []) ++ [.burn s.config.self net] ++
    (if assetAllowance s (s.requests id).asset s.config.portfolioSafe s.config.self = wordLimit-1 then [] else [.allowanceSpent (s.requests id).asset s.config.portfolioSafe s.config.self payout]) ++
    [.assetTransfer (s.requests id).asset s.config.portfolioSafe (s.requests id).receiver payout,.redemption id (s.requests id) fee net payout],by simpa only [List.append_assoc] using htrace,?_⟩
  intro e he
  split_ifs at he <;> simp only [List.mem_append,List.mem_cons,List.not_mem_nil,false_or,or_false,or_assoc] at he
  all_goals rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals first | trivial | exact ⟨⟨hfee,hnet,hout,hmin,by intro _; rw [hout]; exact Out_floor_bounds _ _ _⟩,by simp [TraceRequestCorrect,hreq,statusState,hk],valid_pending _ hv⟩

theorem approveOne_correct (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n) (hp : price < wordLimit)
    (h : approveOne env asset price id s = .ok ((),t)) : CorrectRun s.config price s t := by
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
          exact rejectedSubscription_correct env s t n id price hi hv hk h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact rejectedRedemption_correct env s t n id price hi hv hk h
      · rw [if_neg hex] at h
        have hstatus : chosenStatus env true (s.requests id) = .processed := by simp [chosenStatus,show env.now ≤ (s.requests id).expiryAt by omega]
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact approvedSubscription_correct env s t n id price hi hv hk hp h
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          obtain ⟨_,_,_,_,_,_,hdata,_⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 hc.2 hp hd hi.1 hreg htoken h
          exact approvedRedemption_correct env s t n id price hi hv hk hp h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact correctRun_nil s.config price s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact correctRun_nil s.config price s

theorem rejectOne_correct (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n)
    (h : rejectOne env asset id s = .ok ((),t)) : CorrectRun s.config price s t := by
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
        exact rejectedSubscription_correct env s t n id price hi hv hk h
      · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
        exact rejectedRedemption_correct env s t n id price hi hv hk h
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact correctRun_nil s.config price s
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact correctRun_nil s.config price s



theorem iterate_correct (env : Environment) (body : Nat → Tx Unit) (n price : Nat)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (cert : ∀ id s t, Structural env s n → body id s = .ok ((),t) → CorrectRun s.config price s t)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : iterate body ids s = .ok ((),t)) : CorrectRun s.config price s t := by
  induction ids generalizing s with
  | nil =>
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact correctRun_nil s.config price s
  | cons id ids ih =>
    obtain ⟨u,m,hb,hr⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    have hs := step id s m hi hb
    have hreq := recordTransition_requests env s m n id hs
    have hrest := iterate_recordRun env body n step ids m t hs.closed hr
    obtain ⟨rest,_,_,_,_,_,hterminal,_⟩ := hrest.suffix
    have hc := ih m hs.closed hr
    rw [hs.config] at hc
    exact correctRun_trans s.config price s m t hreq.1 hreq.2.1 hterminal (cert id s m hi hb) hc

#print axioms iterate_correct
#print axioms approvedRedemption_correct
end Benchmark.Cases.KPK.SharesSettlementAccounting
