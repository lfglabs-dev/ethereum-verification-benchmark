import Benchmark.Cases.KPK.SharesSettlementAccounting.Shares

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def statusState (s : State) (id : Nat) (status : RequestStatus) : State :=
  {s with requests := fun j => if j == id then {s.requests id with requestStatus := status} else s.requests j}

theorem sum_zero_at (ids : List Nat) (f : Nat → Nat) (id : Nat)
    (hn : ids.Nodup) (hm : id ∈ ids) :
    (ids.map fun j => if j = id then 0 else f j).sum = (ids.map f).sum - f id := by
  have pointwise (j : Nat) :
      (if j = id then 0 else f j) + (if j = id then f id else 0) = f j := by
    by_cases hj : j = id <;> simp [hj]
  have sumEq : (ids.map fun j => if j = id then 0 else f j).sum +
      (ids.map fun j => if j = id then f id else 0).sum = (ids.map f).sum := by
    have combine (xs : List Nat) :
        (xs.map fun j => if j = id then 0 else f j).sum +
        (xs.map fun j => if j = id then f id else 0).sum = (xs.map f).sum := by
      induction xs with
      | nil => simp
      | cons j js ih =>
        have hh := pointwise j
        simp only [List.map_cons,List.sum_cons]
        omega
    exact combine ids
  have indicatorEq : (ids.map fun j => if j = id then f id else 0).sum = f id := by
    have indicator (xs : List Nat) (hx : xs.Nodup) :
        (xs.map fun j => if j = id then f id else 0).sum = if id ∈ xs then f id else 0 := by
      induction xs with
      | nil => simp
      | cons j js ih =>
        have hnd := List.nodup_cons.mp hx
        by_cases hj : j = id
        · subst j; simp [hnd.1,ih hnd.2]
        · simp [hj,Ne.symm hj,ih hnd.2]
    simpa [hm] using indicator ids hn
  rw [indicatorEq] at sumEq
  omega

theorem filter_count_sum (ids : List Nat) (p : Nat → Bool) :
    (ids.filter p).length = (ids.map fun j => if p j then 1 else 0).sum := by
  induction ids with
  | nil => rfl
  | cons j js ih =>
    cases hp : p j <;> simp [hp,ih,Nat.add_comm]

theorem statusState_other (s : State) (id j : Nat) (status : RequestStatus) (hne : j ≠ id) :
    (statusState s id status).requests j = s.requests j := by
  simp [statusState,hne]

theorem statusState_valid (s : State) (id : Nat) (status : RequestStatus)
    (hstatus : status ≠ .pending) : _checkValidRequest ((statusState s id status).requests id) = false := by
  have hb : (status == RequestStatus.pending) = false := by
    cases status <;> first | contradiction | rfl
  simp [statusState,_checkValidRequest,hb]

theorem statusState_sub_liability (s : State) (n id : Nat) (status : RequestStatus)
    (hm : id < n) (hstatus : status ≠ .pending) (a : Address) :
    SubLiability (statusState s id status) n a = SubLiability s n a -
      (if _checkValidRequest (s.requests id) && (s.requests id).asset == a &&
        (s.requests id).requestType == .subscription then (s.requests id).assetAmount else 0) := by
  let f := fun j => if _checkValidRequest (s.requests j) && (s.requests j).asset == a &&
      (s.requests j).requestType == .subscription then (s.requests j).assetAmount else 0
  have heq : (fun j => let r := (statusState s id status).requests j
      if _checkValidRequest r && r.asset == a && r.requestType == .subscription then r.assetAmount else 0) =
      (fun j => if j = id then 0 else f j) := by
    funext j
    by_cases hj : j = id
    · subst j; simp [statusState_valid s id status hstatus]
    · simp [statusState_other s id j status hj,hj,f]
  unfold SubLiability
  rw [heq]
  exact sum_zero_at (allocated n) f id (by simpa [allocated] using (List.nodup_range (n := n))) (by simpa [allocated] using hm)

theorem statusState_pending_count (s : State) (n id : Nat) (status : RequestStatus)
    (hm : id < n) (hstatus : status ≠ .pending) (a : Address) :
    PendingCount (statusState s id status) n a = PendingCount s n a -
      (if _checkValidRequest (s.requests id) && (s.requests id).asset == a then 1 else 0) := by
  let f := fun j => if _checkValidRequest (s.requests j) && (s.requests j).asset == a then 1 else 0
  have heq : (fun j => if _checkValidRequest ((statusState s id status).requests j) &&
      ((statusState s id status).requests j).asset == a then 1 else 0) =
      (fun j => if j = id then 0 else f j) := by
    funext j
    by_cases hj : j = id
    · subst j; simp [statusState_valid s id status hstatus]
    · simp [statusState_other s id j status hj,hj,f]
  unfold PendingCount
  rw [filter_count_sum,filter_count_sum,heq]
  exact sum_zero_at (allocated n) f id (by simpa [allocated] using (List.nodup_range (n := n))) (by simpa [allocated] using hm)

theorem statusState_red_liability (s : State) (n id : Nat) (status : RequestStatus)
    (hm : id < n) (hstatus : status ≠ .pending) :
    RedLiability (statusState s id status) n = RedLiability s n -
      (if _checkValidRequest (s.requests id) && (s.requests id).requestType == .redemption
       then (s.requests id).sharesAmount else 0) := by
  let f := fun j => if _checkValidRequest (s.requests j) &&
      (s.requests j).requestType == .redemption then (s.requests j).sharesAmount else 0
  have heq : (fun j => let r := (statusState s id status).requests j
      if _checkValidRequest r && r.requestType == .redemption then r.sharesAmount else 0) =
      (fun j => if j = id then 0 else f j) := by
    funext j
    by_cases hj : j = id
    · subst j; simp [statusState_valid s id status hstatus]
    · simp [statusState_other s id j status hj,hj,f]
  unfold RedLiability
  rw [heq]
  exact sum_zero_at (allocated n) f id (by simpa [allocated] using (List.nodup_range (n := n)))
    (by simpa [allocated] using hm)

theorem statusState_payload (s : State) (id j : Nat) (status : RequestStatus) :
    Payload (s.requests j) ((statusState s id status).requests j) := by
  by_cases hj : j = id
  · subst j; simp [Payload,statusState]
  · simp [Payload,statusState_other s id j status hj]

theorem statusState_terminal_untouched (s : State) (id j : Nat) (status : RequestStatus)
    (hp : (s.requests id).requestStatus = .pending)
    (ht : (s.requests j).requestStatus ≠ .pending) :
    (statusState s id status).requests j = s.requests j := by
  apply statusState_other
  intro he; subst j; exact ht hp

theorem payload_pending_full (r q : UserRequest) (h : Payload r q)
    (hr : r.requestStatus = .pending) (hq : q.requestStatus = .pending) : r = q := by
  cases r; cases q
  simp only [Payload] at h
  rcases h with ⟨ht,ha,haa,hs,hi,hrc,htm,hex⟩
  simp_all

def bookkeepingState (s : State) (id : Nat) (status : RequestStatus) (isSub : Bool) : State :=
  let r := s.requests id
  {statusState s id status with
    subscriptionAssets := fun a => if isSub && a == r.asset then s.subscriptionAssets a - r.assetAmount else s.subscriptionAssets a
    pendingRequestsCount := fun a => if a == r.asset then s.pendingRequestsCount a - 1 else s.pendingRequestsCount a}

theorem bookkeeping_subscription_consistent (s : State) (n id : Nat) (status : RequestStatus)
    (hn : id < n) (ht : status ≠ .pending) (hv : _checkValidRequest (s.requests id) = true)
    (hkind : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n) :
    RecordsConsistent (bookkeepingState s id status true) n := by
  rcases hc with ⟨hs,hp⟩
  have hk : ((s.requests id).requestType == RequestType.subscription) = true := by rw [hkind]; rfl
  constructor
  · intro a
    change (if true && a == (s.requests id).asset then s.subscriptionAssets a - (s.requests id).assetAmount else s.subscriptionAssets a) =
      SubLiability (statusState s id status) n a
    rw [statusState_sub_liability s n id status hn ht, ← hs a]
    by_cases he : a = (s.requests id).asset
    · subst a; simp [hv,hk]
    · simp [hv,hk,he,Ne.symm he]
  · intro a
    change (if a == (s.requests id).asset then s.pendingRequestsCount a - 1 else s.pendingRequestsCount a) =
      PendingCount (statusState s id status) n a
    rw [statusState_pending_count s n id status hn ht, ← hp a]
    by_cases he : a = (s.requests id).asset
    · subst a; simp [hv]
    · simp [hv,he,Ne.symm he]

theorem bookkeeping_redemption_consistent (s : State) (n id : Nat) (status : RequestStatus)
    (hn : id < n) (ht : status ≠ .pending) (hv : _checkValidRequest (s.requests id) = true)
    (hkind : (s.requests id).requestType = .redemption) (hc : RecordsConsistent s n) :
    RecordsConsistent (bookkeepingState s id status false) n := by
  rcases hc with ⟨hs,hp⟩
  have hk : ((s.requests id).requestType == RequestType.subscription) = false := by rw [hkind]; rfl
  constructor
  · intro a
    change s.subscriptionAssets a = SubLiability (statusState s id status) n a
    rw [statusState_sub_liability s n id status hn ht, ← hs a]
    simp [hk]
  · intro a
    change (if a == (s.requests id).asset then s.pendingRequestsCount a - 1 else s.pendingRequestsCount a) =
      PendingCount (statusState s id status) n a
    rw [statusState_pending_count s n id status hn ht, ← hp a]
    by_cases he : a = (s.requests id).asset
    · subst a; simp [hv]
    · simp [hv,he,Ne.symm he]

theorem nat_sum_member_bound (ids : List Nat) (f : Nat → Nat) (id : Nat) (hm : id ∈ ids) :
    f id ≤ (ids.map f).sum := by
  induction ids with
  | nil => simp at hm
  | cons j js ih =>
    rcases List.mem_cons.mp hm with he | ht
    · subst j; simp only [List.map_cons,List.sum_cons]; omega
    · have hh := ih ht
      simp only [List.map_cons,List.sum_cons]; omega

theorem valid_subscription_reserved (s : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true)
    (hk : (s.requests id).requestType = .subscription) (hc : RecordsConsistent s n) :
    (s.requests id).assetAmount ≤ s.subscriptionAssets (s.requests id).asset ∧
    1 ≤ s.pendingRequestsCount (s.requests id).asset := by
  rcases hc with ⟨hs,hp⟩
  have hmem : id ∈ allocated n := by simpa [allocated] using hn
  have hkb : ((s.requests id).requestType == RequestType.subscription) = true := by rw [hk]; rfl
  constructor
  · rw [hs]; unfold SubLiability
    have hh := nat_sum_member_bound (allocated n)
      (fun j => if _checkValidRequest (s.requests j) && (s.requests j).asset == (s.requests id).asset &&
        (s.requests j).requestType == .subscription then (s.requests j).assetAmount else 0) id hmem
    simpa [hv,hkb] using hh
  · rw [hp]; unfold PendingCount; rw [filter_count_sum]
    have hh := nat_sum_member_bound (allocated n)
      (fun j => if _checkValidRequest (s.requests j) && (s.requests j).asset == (s.requests id).asset then 1 else 0) id hmem
    simpa [hv] using hh

theorem tx_bind_run (c : Tx α) (f : α → Tx β) (s m t : State) (a : α) (b : β)
    (hc : c s = .ok (a,m)) (hf : f a m = .ok (b,t)) :
    (c >>= f) s = .ok (b,t) := by
  simp only [Bind.bind,StateT.bind,Except.bind,hc]
  exact hf

theorem subscription_bookkeeping_run (s : State) (id : Nat) (status : RequestStatus)
    (ho : s.subscriptionAssets (s.requests id).asset < wordLimit)
    (ha : (s.requests id).assetAmount < wordLimit)
    (hb : (s.requests id).assetAmount ≤ s.subscriptionAssets (s.requests id).asset)
    (hc : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hp : 1 ≤ s.pendingRequestsCount (s.requests id).asset) :
    (show Tx Unit from do
        setStatus id status
        debitSubscription (s.requests id).asset (s.requests id).assetAmount
        decrementCount (s.requests id).asset) s = .ok ((),bookkeepingState s id status true) := by
  let m := statusState s id status
  let d : State := {m with
    subscriptionAssets := fun a => if a == (s.requests id).asset then
      s.subscriptionAssets (s.requests id).asset - (s.requests id).assetAmount else s.subscriptionAssets a}
  have hd := debitSubscription_run (s.requests id).asset (s.requests id).assetAmount m ho ha hb
  have hcount := decrementCount_run (s.requests id).asset d hc hp
  have hset : setStatus id status s = .ok ((),m) := rfl
  have hd' : debitSubscription (s.requests id).asset (s.requests id).assetAmount m = .ok ((),d) := hd
  apply tx_bind_run _ _ s m _ () () hset
  apply tx_bind_run _ _ m d _ () () hd'
  rw [hcount]
  dsimp only [d,m]
  have hsF : (fun a => if a == (s.requests id).asset then s.subscriptionAssets (s.requests id).asset - (s.requests id).assetAmount else s.subscriptionAssets a) =
      (fun a => if a == (s.requests id).asset then s.subscriptionAssets a - (s.requests id).assetAmount else s.subscriptionAssets a) := by
    funext a; by_cases he : a = (s.requests id).asset <;> simp [he]
  have hpF : (fun a => if a == (s.requests id).asset then s.pendingRequestsCount (s.requests id).asset - 1 else s.pendingRequestsCount a) =
      (fun a => if a == (s.requests id).asset then s.pendingRequestsCount a - 1 else s.pendingRequestsCount a) := by
    funext a; by_cases he : a = (s.requests id).asset <;> simp [he]
  simp only [bookkeepingState,statusState,Bool.true_and]
  rw [hsF,hpF]

theorem valid_pending_count_positive (s : State) (n id : Nat)
    (hn : id < n) (hv : _checkValidRequest (s.requests id) = true) (hc : RecordsConsistent s n) :
    1 ≤ s.pendingRequestsCount (s.requests id).asset := by
  rw [hc.2]; unfold PendingCount; rw [filter_count_sum]
  have hh := nat_sum_member_bound (allocated n)
    (fun j => if _checkValidRequest (s.requests j) && (s.requests j).asset == (s.requests id).asset then 1 else 0)
    id (by simpa [allocated] using hn)
  simpa [hv] using hh

theorem redemption_bookkeeping_run (s : State) (id : Nat) (status : RequestStatus)
    (hc : s.pendingRequestsCount (s.requests id).asset < wordLimit)
    (hp : 1 ≤ s.pendingRequestsCount (s.requests id).asset) :
    (show Tx Unit from do setStatus id status; decrementCount (s.requests id).asset) s =
      .ok ((),bookkeepingState s id status false) := by
  let m := statusState s id status
  have hset : setStatus id status s = .ok ((),m) := rfl
  apply tx_bind_run _ _ s m _ () () hset
  rw [decrementCount_run (s.requests id).asset m hc hp]
  have hpF : (fun a => if a == (s.requests id).asset then s.pendingRequestsCount (s.requests id).asset - 1 else s.pendingRequestsCount a) =
      (fun a => if a == (s.requests id).asset then s.pendingRequestsCount a - 1 else s.pendingRequestsCount a) := by
    funext a; by_cases he : a = (s.requests id).asset <;> simp [he]
  simp only [bookkeepingState,Bool.false_and,Bool.false_eq_true,↓reduceIte,m,statusState]
  rw [hpF]

-- Only registered ERC20 cells need word ranges after arbitrary mutable module calls.
def RegisteredAllowanceRanges (s : State) : Prop :=
  ∀ token owner spender, (s.config.assets token).asset = token → token ≠ 0 →
    assetAllowance s token owner spender < wordLimit

theorem module_registered_allowance_frame (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (moduleAddr token owner spender : Address)
    (hm : env.isToken moduleAddr = false)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0)
    (moduleState : Nat → Nat) :
    assetAllowance {s with external := {accountState := fun target k =>
      if target == moduleAddr.val then moduleState k else s.external.accountState target k}}
      token owner spender = assetAllowance s token owner spender := by
  have hi := (hap token hreg ht).2.1
  have hn : token.val ≠ moduleAddr.val := by
    intro he
    have ha : token = moduleAddr := Verity.Core.Address.ext he
    rw [ha,hm] at hi; cases hi
  simp [assetAllowance,hn]

theorem module_registered_ranges (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (hr : RegisteredAllowanceRanges s)
    (moduleAddr : Address) (hm : env.isToken moduleAddr = false) (moduleState : Nat → Nat) :
    RegisteredAllowanceRanges {s with
      external := {accountState := fun target k =>
        if target == moduleAddr.val then moduleState k else s.external.accountState target k}} := by
  intro token owner spender hreg ht
  rw [module_registered_allowance_frame s env hap moduleAddr token owner spender hm hreg ht moduleState]
  exact hr token owner spender hreg ht

theorem transferFrom_registered_ranges (s t : State) (env : Environment)
    (hap : ExternalApplicability env s) (token spender fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0) (amount : Nat)
    (ha : amount < wordLimit) (hr : RegisteredAllowanceRanges s)
    (h : safeTransferFrom env token spender fromAddr toAddr amount s = .ok ((),t)) :
    ∀ other owner sp, (s.config.assets other).asset = other → other ≠ 0 →
      assetAllowance t other owner sp < wordLimit := by
  have hc := (safeTransferFrom_accounting s t env hap token spender fromAddr toAddr
    hreg ht amount ha (hr token fromAddr spender hreg ht) h).2.2
  intro other owner sp hother hnonzero
  rw [hc]
  have hb := hr other owner sp hother hnonzero
  split <;> omega

#print axioms valid_pending_count_positive
#print axioms redemption_bookkeeping_run
#print axioms module_registered_allowance_frame
#print axioms module_registered_ranges
#print axioms transferFrom_registered_ranges
#print axioms valid_subscription_reserved
#print axioms subscription_bookkeeping_run
#print axioms bookkeeping_subscription_consistent
#print axioms bookkeeping_redemption_consistent
#print axioms statusState_red_liability
#print axioms statusState_payload
#print axioms statusState_terminal_untouched
#print axioms payload_pending_full
#print axioms sum_zero_at
#print axioms statusState_sub_liability
#print axioms statusState_pending_count
end Benchmark.Cases.KPK.SharesSettlementAccounting
