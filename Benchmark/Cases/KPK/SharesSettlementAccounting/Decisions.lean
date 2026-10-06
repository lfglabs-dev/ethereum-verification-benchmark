import Benchmark.Cases.KPK.SharesSettlementAccounting.LoopRecords

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def eligible (s : State) (asset : Address) (id : Nat) : Bool :=
  _checkValidRequest (s.requests id) && (s.requests id).asset == asset

def chosenStatus (env : Environment) (approve : Bool) (r : UserRequest) : RequestStatus :=
  if approve && env.now <= r.expiryAt then .processed else .rejected

def Choice (env : Environment) (s t : State) (asset : Address) (approve : Bool) (id : Nat) : Prop :=
  ∃ suffix, t.trace = s.trace ++ suffix ∧
    actualDecisions suffix = (if eligible s asset id then [⟨id,chosenStatus env approve (s.requests id)⟩] else []) ∧
    t.requests = (if eligible s asset id then statusState s id (chosenStatus env approve (s.requests id)) else s).requests

theorem handler_choice (env : Environment) (s t : State) (n id : Nat) (status : RequestStatus)
    (isSub : Bool) (hr : RecordTransition env s t n id)
    (hv : _checkValidRequest (s.requests id) = true) (ht : status ≠ .pending)
    (hd : HandlerData s t id status isSub) :
    ∃ suffix, t.trace = s.trace ++ suffix ∧ actualDecisions suffix = [⟨id,status⟩] := by
  have hpending := valid_pending _ hv
  have htstatus : (t.requests id).requestStatus = status := by rw [hd.2.1]; simp [statusState]
  rcases hr.outcome with heq | ⟨other,sub,suffix,_,_,hdata,htrace,hdec,_⟩
  · rw [heq,hpending] at htstatus
    exact False.elim (ht htstatus.symm)
  · have hother : (t.requests id).requestStatus = other := by rw [hdata.2.1]; simp [statusState]
    have heq : other = status := hother.symm.trans htstatus
    exact ⟨suffix,htrace,by rwa [heq] at hdec⟩

theorem selectDecisions_payload (s t : State) (now : Nat) (asset : Address) (approve : Bool)
    (ids : List Nat) (statuses : Nat → RequestStatus)
    (hp : ∀ id, Payload (s.requests id) (t.requests id)) :
    selectDecisions s now asset approve ids statuses = selectDecisions t now asset approve ids statuses := by
  induction ids generalizing statuses with
  | nil => rfl
  | cons id ids ih =>
    have hasset := (hp id).2.1
    have hinv := (hp id).2.2.2.2.1
    have hexp := (hp id).2.2.2.2.2.2.2
    simp only [selectDecisions,hasset,hinv,hexp]
    split <;> rw [ih]

theorem Choice_noop (env : Environment) (s : State) (asset : Address) (approve : Bool) (id : Nat)
    (he : eligible s asset id = false) : Choice env s s asset approve id := by
  exact ⟨[],by simp,by simp [he,actualDecisions],by simp [he]⟩

theorem Choice_handled (env : Environment) (s t : State) (n id : Nat) (asset : Address) (approve : Bool)
    (status : RequestStatus) (isSub : Bool) (hr : RecordTransition env s t n id)
    (hv : _checkValidRequest (s.requests id) = true) (ht : status ≠ .pending)
    (hd : HandlerData s t id status isSub) (he : eligible s asset id = true)
    (hstatus : chosenStatus env approve (s.requests id) = status) : Choice env s t asset approve id := by
  obtain ⟨suffix,htrace,hdec⟩ := handler_choice env s t n id status isSub hr hv ht hd
  exact ⟨suffix,htrace,by simpa only [he,if_true,hstatus] using hdec,by simpa only [he,if_true,hstatus] using hd.2.1⟩


theorem approveOne_choice (env : Environment) (s t : State) (n id price : Nat) (asset : Address)
    (hi : Structural env s n) (hp : price < wordLimit)
    (h : approveOne env asset price id s = .ok ((),t)) : Choice env s t asset true id := by
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
          exact Choice_handled env s t n id asset true .rejected true
            (rejectedSubscription_transition env s t n id hi hv hk h) hv (by decide)
            (rejectSubscription_data env s t n id hn hv hk hi.2.1 ha hc.1 hc.2 hi.1.2.1 hreg htoken h).1 he hstatus
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          exact Choice_handled env s t n id asset true .rejected false
            (rejectedRedemption_transition env s t n id hi hv hk h) hv (by decide)
            (rejectRedemption_data s t n id hn hv hk hi.2.1 hc.2 hi.1.1 h).1 he hstatus
      · rw [if_neg hex] at h
        have hstatus : chosenStatus env true (s.requests id) = .processed := by simp [chosenStatus,show env.now ≤ (s.requests id).expiryAt by omega]
        cases hk : (s.requests id).requestType
        · simp only [hk,show (RequestType.subscription == RequestType.subscription) = true from rfl,if_true] at h
          exact Choice_handled env s t n id asset true .processed true
            (approvedSubscription_transition env s t n id price hi hv hk hp h) hv (by decide)
            (approveSubscription_data env s t n id price hn hv hk hi.2.1 ha hc.1 hc.2 hp hd hi.1 hreg htoken h).1 he hstatus
        · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
          obtain ⟨_,_,_,_,_,_,hdata,_⟩ := approveRedemption_data env s t n id price hn hv hk hi.2.1 hs hi.2.2.2.2 hc.2 hp hd hi.1 hreg htoken h
          exact Choice_handled env s t n id asset true .processed false
            (approvedRedemption_transition env s t n id price hi hv hk hp h) hv (by decide) hdata he hstatus
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact Choice_noop env s asset true id (by simp [eligible,hv,hass])
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact Choice_noop env s asset true id (by simp [eligible,hf])

theorem rejectOne_choice (env : Environment) (s t : State) (n id : Nat) (asset : Address)
    (hi : Structural env s n)
    (h : rejectOne env asset id s = .ok ((),t)) : Choice env s t asset false id := by
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
        exact Choice_handled env s t n id asset false .rejected true
          (rejectedSubscription_transition env s t n id hi hv hk h) hv (by decide)
          (rejectSubscription_data env s t n id hn hv hk hi.2.1 ha hc.1 hc.2 hi.1.2.1 hreg htoken h).1 he (by simp [chosenStatus])
      · simp only [hk,show (RequestType.redemption == RequestType.subscription) = false from rfl,Bool.false_eq_true,if_false] at h
        exact Choice_handled env s t n id asset false .rejected false
          (rejectedRedemption_transition env s t n id hi hv hk h) hv (by decide)
          (rejectRedemption_data s t n id hn hv hk hi.2.1 hc.2 hi.1.1 h).1 he (by simp [chosenStatus])
    · simp only [show ((s.requests id).asset != asset) = true by simpa using hass,if_true] at h
      have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
      rw [ht]
      exact Choice_noop env s asset false id (by simp [eligible,hv,hass])
  · have hf : _checkValidRequest (s.requests id) = false := Bool.eq_false_iff.mpr hv
    simp only [hf,Bool.not_false,if_true] at h
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]
    exact Choice_noop env s asset false id (by simp [eligible,hf])

theorem selectDecisions_cons_current (env : Environment) (s : State) (asset : Address) (approve : Bool)
    (id : Nat) (ids : List Nat) :
    selectDecisions s env.now asset approve (id::ids) (fun j => (s.requests j).requestStatus) =
      if eligible s asset id then
        ⟨id,chosenStatus env approve (s.requests id)⟩ :: selectDecisions s env.now asset approve ids
          (fun j => if j == id then chosenStatus env approve (s.requests id) else (s.requests j).requestStatus)
      else selectDecisions s env.now asset approve ids (fun j => (s.requests j).requestStatus) := rfl

theorem iterate_choice (env : Environment) (body : Nat → Tx Unit) (n : Nat) (asset : Address) (approve : Bool)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (choice : ∀ id s t, Structural env s n → body id s = .ok ((),t) → Choice env s t asset approve id)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : iterate body ids s = .ok ((),t)) :
    ∃ suffix, t.trace = s.trace ++ suffix ∧
      actualDecisions suffix = selectDecisions s env.now asset approve ids (fun j => (s.requests j).requestStatus) := by
  induction ids generalizing s with
  | nil =>
    have ht : t = s := (congrArg Prod.snd (Except.ok.inj h)).symm
    rw [ht]; exact ⟨[],by simp, rfl⟩
  | cons id ids ih =>
    simp only [iterate] at h
    obtain ⟨u,m,hstep,hrest⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    have hr := step id s m hi hstep
    obtain ⟨first,hfirst,hdecFirst,hreq⟩ := choice id s m hi hstep
    obtain ⟨rest,htrace,hdecRest⟩ := ih m hr.closed hrest
    have hpayload := (recordTransition_requests env s m n id hr).1
    have hselect := selectDecisions_payload s m env.now asset approve ids (fun j => (m.requests j).requestStatus) hpayload
    refine ⟨first ++ rest,by rw [htrace,hfirst,List.append_assoc],?_⟩
    rw [actualDecisions_append,hdecFirst,hdecRest,← hselect,selectDecisions_cons_current]
    by_cases he : eligible s asset id = true
    · simp only [he,if_true] at hreq ⊢
      have hstatus : (fun j => (m.requests j).requestStatus) =
          (fun j => if j == id then chosenStatus env approve (s.requests id) else (s.requests j).requestStatus) := by
        funext j
        rw [hreq]
        simp only [statusState]
        by_cases hj : j = id <;> simp [hj]
      rw [hstatus]; rfl
    · have hf : eligible s asset id = false := Bool.eq_false_iff.mpr he
      simp only [he,if_false] at hreq ⊢
      rw [hreq]; rfl

theorem pending_test (status : RequestStatus) :
    (status == RequestStatus.pending) = if status = .pending then true else false := by
  cases status <;> rfl

theorem selectDecisions_pending_equiv (s : State) (now : Nat) (asset : Address) (approve : Bool)
    (ids : List Nat) (left right : Nat → RequestStatus)
    (h : ∀ j, (left j == RequestStatus.pending) = (right j == RequestStatus.pending)) :
    selectDecisions s now asset approve ids left = selectDecisions s now asset approve ids right := by
  induction ids generalizing left right with
  | nil => rfl
  | cons id ids ih =>
    simp only [selectDecisions,h id]
    split
    · congr 1
      apply ih
      intro j
      by_cases he : j = id <;> simp [he,h j]
    · exact ih left right h

#print axioms approveOne_choice
#print axioms rejectOne_choice
#print axioms selectDecisions_payload
#print axioms iterate_choice
#print axioms selectDecisions_pending_equiv

theorem two_arrays_decisions (env : Environment) (s t : State) (n price : Nat) (asset : Address)
    (approved rejected : List Nat) (hi : Structural env s n) (hp : price < wordLimit)
    (h : (do _processApproved env approved asset price; _processRejected env rejected asset) s = .ok ((),t)) :
    ∃ suffix, t.trace = s.trace ++ suffix ∧ actualDecisions suffix = expectedDecisions s env.now asset approved rejected := by
  obtain ⟨u,m,ha,hr⟩ := tx_bind_ok _ _ _ _ _ h
  cases u
  have ar := approved_recordRun env s m n price asset approved hi hp ha
  obtain ⟨first,hfirst,hdec1⟩ := iterate_choice env (approveOne env asset price) n asset true
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h)
    (by intro id s t hi h; exact approveOne_choice env s t n id price asset hi hp h) approved s m hi ha
  obtain ⟨second,hsecond,hdec2⟩ := iterate_choice env (rejectOne env asset) n asset false
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h)
    (by intro id s t hi h; exact rejectOne_choice env s t n id asset hi h) rejected m t ar.closed hr
  obtain ⟨runSuffix,htrace,_,_,_,hpayload,_,_,hfinal,huntouched⟩ := ar.suffix
  have heq : runSuffix = first := List.append_cancel_left (htrace.symm.trans hfirst)
  rw [heq] at hfinal huntouched
  let updated := fun id => if ((selectDecisions s env.now asset true approved (fun j => (s.requests j).requestStatus)).map Decision.id).contains id
    then RequestStatus.processed else (s.requests id).requestStatus
  have htests : ∀ j, ((m.requests j).requestStatus == RequestStatus.pending) = (updated j == RequestStatus.pending) := by
    intro j
    by_cases hm : j ∈ consumed first
    · have hcontains : ((selectDecisions s env.now asset true approved (fun j => (s.requests j).requestStatus)).map Decision.id).contains j = true := by
        rw [← hdec1,← consumed_decisions]
        simpa using hm
      have hterm := hfinal j hm
      simp only [updated,hcontains,if_true,pending_test,if_neg hterm,show RequestStatus.processed ≠ RequestStatus.pending by decide,if_false]
    · have hcontains : ((selectDecisions s env.now asset true approved (fun j => (s.requests j).requestStatus)).map Decision.id).contains j = false := by
        rw [← hdec1,← consumed_decisions]
        simpa using hm
      simp only [updated,hcontains,Bool.false_eq_true,if_false,huntouched j hm]
  have hselect := selectDecisions_payload s m env.now asset false rejected (fun j => (m.requests j).requestStatus) hpayload
  have hshadow := selectDecisions_pending_equiv s env.now asset false rejected
    (fun j => (m.requests j).requestStatus) updated htests
  refine ⟨first ++ second,by rw [hsecond,hfirst,List.append_assoc],?_⟩
  rw [actualDecisions_append,hdec1,hdec2,← hselect,hshadow]
  rfl

#print axioms two_arrays_decisions
end Benchmark.Cases.KPK.SharesSettlementAccounting
