import Benchmark.Cases.Kuru.WithdrawalLimit.Proofs.LimiterProofs

namespace Benchmark.Cases.Kuru.WithdrawalLimit
open LimiterProofs

/-- Derived trace invariant, not an assumed target property. -/
def WorldSafe (w : World) (xs : List Checkpoint) : Prop := LimiterSafe w.limiter xs w.now

theorem writer_policy (d : Deployment) (w : World) (caller : Key)
    (a : PolicyAction) (next : World) (hs : WorldSafe w xs)
    (h : policyAction d w caller a = .ok next) :
    WorldSafe next xs ∧ current next.limiter.persistent.history = current w.limiter.persistent.history := by
  have hn := (core_policy_frame d w caller a next h).1
  have result : LimiterSafe next.limiter xs w.now ∧
      current next.limiter.persistent.history = current w.limiter.persistent.history := by
    cases a with
    | setFeeCollector owner =>
      unfold policyAction at h
      obtain ⟨u,_,h⟩ := core_bind_ok h
      obtain ⟨p,_,h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | setRegistry registry =>
      unfold policyAction at h
      obtain ⟨_,h⟩ := core_ensure_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | pause paused =>
      cases paused with
      | false =>
        simp only [policyAction,Bool.false_eq_true,if_false] at h
        obtain ⟨_,h⟩ := core_ensure_ok h
        obtain ⟨_,h⟩ := core_ensure_ok h
        rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
      | true =>
        simp only [policyAction,if_true] at h
        obtain ⟨u,_,h⟩ := core_bind_ok h
        rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | rotateAuthority authority =>
      unfold policyAction at h
      obtain ⟨u,_,h⟩ := core_bind_ok h
      obtain ⟨n,_,h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | freeze frozen =>
      cases frozen <;> simp only [policyAction,Bool.false_eq_true,if_false,if_true] at h
      all_goals
        obtain ⟨u,_,h⟩ := core_bind_ok h
        rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | freezeToken token frozen =>
      cases frozen <;> simp only [policyAction,Bool.false_eq_true,if_false,if_true] at h
      all_goals
        obtain ⟨u,_,h⟩ := core_bind_ok h
        rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | invalidateNonce account n =>
      unfold policyAction at h
      obtain ⟨_,h⟩ := core_ensure_ok h
      obtain ⟨u,_,h⟩ := core_bind_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | bindLimiter limiter =>
      unfold policyAction at h
      obtain ⟨u,_,h⟩ := core_bind_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      obtain ⟨_,h⟩ := core_ensure_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | configureDrip capacity rate =>
      unfold policyAction at h
      obtain ⟨l,hl,h⟩ := core_bind_ok h
      have safe := safe_configureDrip w.limiter xs w.now capacity rate caller
        (w.roles w.core.registry).governance l hs hl
      have hx := hl
      unfold setDripConfig at hx
      obtain ⟨_,hx⟩ := core_ensure_ok hx
      obtain ⟨_,hx⟩ := core_ensure_ok hx
      obtain ⟨_,hx⟩ := core_ensure_ok hx
      obtain ⟨t,_,hx⟩ := core_bind_ok hx
      obtain ⟨A,_,hx⟩ := core_bind_ok hx
      have htotal : current l.persistent.history = current w.limiter.persistent.history := by
        rw [← Except.ok.inj hx]
      rw [← Except.ok.inj h]; exact ⟨safe,htotal⟩
    | configureSource token source =>
      unfold policyAction at h
      obtain ⟨l,hl,h⟩ := core_bind_ok h
      have safe := safe_configureSource w.limiter xs w.now caller (w.roles w.core.registry).governance
        token source d.codePresent l hs hl
      have hx := hl
      unfold setPriceSource at hx
      obtain ⟨_,hx⟩ := core_ensure_ok hx
      obtain ⟨_,hx⟩ := core_ensure_ok hx
      obtain ⟨_,hx⟩ := core_ensure_ok hx
      have htotal : current l.persistent.history = current w.limiter.persistent.history := by
        rw [← Except.ok.inj hx]
      rw [← Except.ok.inj h]; exact ⟨safe,htotal⟩
    | configureToken token enabled metadata =>
      obtain ⟨config,hv⟩ := core_configureToken_success d w caller token enabled metadata next h
      rw [hv]; exact ⟨hs,rfl⟩
    | receiveNative amount =>
      unfold policyAction at h
      obtain ⟨n,_,h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | nestedGuarded =>
      unfold policyAction at h
      obtain ⟨entered,_,h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
    | observe => rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
  exact ⟨by unfold WorldSafe; rw [hn]; exact result.1,result.2⟩

theorem writer_environment (d : Deployment) (w : World) (a : EnvironmentAction)
    (hs : WorldSafe w xs) : WorldSafe (environmentAction d w a) xs ∧
    current (environmentAction d w a).limiter.persistent.history = current w.limiter.persistent.history := by
  obtain ⟨hn,hl,_,_⟩ := core_environment_frame d w a
  unfold WorldSafe
  rw [hn,hl]
  exact ⟨hs,rfl⟩

theorem writer_environment_fold (d : Deployment) (as : List EnvironmentAction) (w : World)
    (hs : WorldSafe w xs) : WorldSafe (as.foldl (environmentAction d) w) xs ∧
    current (as.foldl (environmentAction d) w).limiter.persistent.history = current w.limiter.persistent.history := by
  obtain ⟨hn,hl,_,_⟩ := core_environment_fold_frame d as w
  unfold WorldSafe
  rw [hn,hl]
  exact ⟨hs,rfl⟩

theorem writer_callbacks (d : Deployment) (cs : List Callback) (w next : World)
    (hs : WorldSafe w xs) (h : callbacks d cs w = .ok next) :
    WorldSafe next xs ∧ current next.limiter.persistent.history = current w.limiter.persistent.history := by
  induction cs generalizing w with
  | nil => rw [← Except.ok.inj h]; exact ⟨hs,rfl⟩
  | cons c cs ih =>
    have he := writer_environment_fold d c.environmentBefore w hs
    simp only [callbacks] at h
    cases hp : policyAction d (c.environmentBefore.foldl (environmentAction d) w) c.caller c.action with
    | ok out =>
      rw [hp] at h
      have hs' := writer_policy d _ c.caller c.action out he.1 hp
      have hi := ih out hs'.1 h
      exact ⟨hi.1,hi.2.trans (hs'.2.trans he.2)⟩
    | error e =>
      rw [hp] at h
      dsimp only at h
      split at h
      · have hi := ih _ he.1 h; exact ⟨hi.1,hi.2.trans he.2⟩
      · contradiction

theorem writer_transfer (d : Deployment) (w : World) (token recipient : Key) (amount : Nat) {debited : Nat}
    (obs : TransferObservation) (next : World) (hs : WorldSafe w xs)
    (h : transferAsset d w token recipient amount obs = .ok (debited, next)) :
    WorldSafe next xs ∧ current next.limiter.persistent.history = current w.limiter.persistent.history := by
  unfold transferAsset at h
  split at h
  · obtain ⟨_,h⟩ := core_ensure_ok h
    obtain ⟨out,hout,h⟩ := core_bind_ok h
    obtain ⟨_,h⟩ := core_ensure_ok h
    have hv := congrArg Prod.snd (Except.ok.inj h)
    dsimp only at hv
    rw [← hv]
    exact writer_callbacks d obs.callbacks { w with nativeCustody := w.nativeCustody-amount } out hs hout
  · obtain ⟨_,h⟩ := core_ensure_ok h
    obtain ⟨out,hout,h⟩ := core_bind_ok h
    obtain ⟨_,h⟩ := core_ensure_ok h
    obtain ⟨_,h⟩ := core_ensure_ok h
    obtain ⟨_,h⟩ := core_ensure_ok h
    have hv := congrArg Prod.snd (Except.ok.inj h)
    dsimp only at hv
    rw [← hv]
    exact writer_callbacks d obs.callbacks w out hs hout

theorem consumption_total {a b : Limiter} {now E : Nat} {f : Funding}
    (h : OrdinaryConsumption a b now E f) : current b.persistent.history = current a.persistent.history := by
  rcases h with ⟨A,ha,hcursor,hcredit,hu,hr,hbound,hD,_⟩
  exact hD

theorem writer_approved_frame (s : Limiter) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (next : Limiter)
    (h : checkApprovedWithdrawal s now fetch caller core token = .ok next) : FundingFrame s next := by
  unfold checkApprovedWithdrawal at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨started, hs, h⟩ := core_bind_ok h
  obtain ⟨quote, snapped, hp, h⟩ := core_bind_pair_ok h
  rw [← Except.ok.inj h]
  exact frame_trans (beginFlow_frame s started now hs) (snapshot_frame started fetch token quote snapped hp)

theorem writer_refund (w next : World) (id : Nat) (token : Key) (amount debit : Nat)
    (hs : WorldSafe w xs) (h : refundAsset w id token amount debit = .ok next) : WorldSafe next xs := by
  have hf := core_refund_frame w next id token amount debit h
  change LimiterSafe next.limiter xs next.now
  rw [hf.1, hf.2.2.1]
  exact hs

theorem writer_withdraw (d : Deployment) (w : World) (caller : Key)
    (a : OrdinaryArgs) (obs : TransferObservation) (next : World) (hs : WorldSafe w xs)
    (h : withdraw d w caller a obs = .ok next) :
    WorldSafe next xs ∧ current next.limiter.persistent.history = current w.limiter.persistent.history ∧
    OrdinaryCheckpoints d w caller a ∧
    ∃ f, next.payouts = w.payouts ++ [⟨.ordinary,a.token,a.recipient,debitedAmount a.token a.amount obs,some f,none⟩] ∧
      OrdinaryConsumption w.limiter next.limiter w.now (expiredReference xs w.now).1 f := by
  unfold withdraw at h
  obtain ⟨_,h⟩ := core_ensure_ok h
  obtain ⟨entered,he,h⟩ := core_bind_ok h
  obtain ⟨hp,hg,heq⟩ := core_activeGuardEnter_success d w entered he
  subst entered
  obtain ⟨u,hroot,h⟩ := core_bind_ok h
  unfold requireRoot at hroot
  obtain ⟨hrnz,hroot⟩ := core_ensure_ok hroot
  have hr := core_ensure_success hroot
  obtain ⟨hauth,h⟩ := core_ensure_ok h
  obtain ⟨hamount,h⟩ := core_ensure_ok h
  obtain ⟨hrecipient,h⟩ := core_ensure_ok h
  obtain ⟨u,hrelease,h⟩ := core_bind_ok h
  have hfreeze := core_ensure_success hrelease
  obtain ⟨prepared,hprep,h⟩ := core_bind_ok h
  obtain ⟨hbalance,hbound,pinned,hpin,hpeq⟩ := core_withdrawBefore_success d _ prepared a.rootId a.token a.amount hprep
  have hpSafe : WorldSafe prepared xs := by
    rw [hpeq]
    exact safe_approved w.limiter xs w.now w.quotes d.coreAddress d.coreAddress a.token pinned hs hpin
  have hpFrame := writer_approved_frame w.limiter w.now w.quotes d.coreAddress d.coreAddress a.token pinned hpin
  have hpFlow := (core_approvedLimiter_frame w.limiter w.now w.quotes d.coreAddress d.coreAddress a.token pinned hpin).2
  obtain ⟨debit,out,hout,h⟩ := core_bind_pair_ok h
  have htSafe := writer_transfer d prepared a.token a.recipient a.amount obs out hpSafe hout
  have htFrame := core_transferAsset_frame d prepared a.token a.recipient a.amount obs out hout
  have htEq : out.limiter = pinned := by
    rw [htFrame.2.2.2 (by rw [hpeq]; exact hpFlow), hpeq]
  have hd := (core_transfer_debit d prepared a.token a.recipient a.amount debit obs out hout).1
  obtain ⟨refunded,hrf,h⟩ := core_bind_ok h
  have hrSafe := writer_refund out refunded a.rootId a.token a.amount debit htSafe.1 hrf
  have hrFrame := core_refund_frame out refunded a.rootId a.token a.amount debit hrf
  have hrEq : refunded.limiter = pinned := hrFrame.2.2.1.trans htEq
  have hn : refunded.now = w.now := by rw [hrFrame.1, htFrame.1, hpeq]
  obtain ⟨u,_,h⟩ := core_bind_ok h
  obtain ⟨f,limiter,hl,h⟩ := core_bind_pair_ok h
  have hlim := withdrawal_exact refunded.limiter xs refunded.now refunded.quotes d.coreAddress d.coreAddress
    a.token debit (refunded.core.tokens a.token).decimals f limiter hrSafe hl
  have hcons : OrdinaryConsumption w.limiter limiter w.now (expiredReference xs w.now).1 f := by
    have hh := hlim.2.1
    rw [hn,hrEq] at hh
    exact consumption_frame hpFrame hh
  rw [← Except.ok.inj h]
  refine ⟨hlim.1,consumption_total hcons,?_,f,?_,hcons⟩
  · exact ⟨hp,hg,hrnz,hr,hauth,hamount,hrecipient.1,hrecipient.2,hbalance,hfreeze.1,hfreeze.2,hbound⟩
  · change refunded.payouts ++ [_] = w.payouts ++ [_]
    rw [hrFrame.2.1,htFrame.2.1,hpeq,hd]

theorem writer_approvedBefore (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (next : World)
    (hs : WorldSafe w xs)
    (h : approvedBeforeTransfer d w caller q sig = .ok next) :
    WorldSafe next xs := by
  unfold approvedBeforeTransfer at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
  obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
  subst entered
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨n, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨l, hl, h⟩ := core_bind_ok h
  have hsafe := safe_approved w.limiter xs w.now w.quotes d.coreAddress d.coreAddress q.token l hs hl
  have hv := Except.ok.inj h
  rw [← hv]
  exact hsafe

theorem writer_approved (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (obs : TransferObservation)
    (next : World) (hs : WorldSafe w xs)
    (h : fulfillApprovedWithdrawal d w caller q sig obs = .ok next) :
    WorldSafe next xs ∧ current next.limiter.persistent.history = current w.limiter.persistent.history := by
  have hpools := (core_approved_success d w caller q sig obs next h).2.2.1
  unfold fulfillApprovedWithdrawal at h
  obtain ⟨prepared,hp,h⟩ := core_bind_ok h
  obtain ⟨debit,out,hout,h⟩ := core_bind_pair_ok h
  obtain ⟨refunded,hr,h⟩ := core_bind_ok h
  have hs' := writer_approvedBefore d w caller q sig prepared hs hp
  have hs'' := writer_transfer d prepared q.token q.recipient q.amount obs out hs' hout
  have hsFinal := writer_refund out refunded (w.core.rootAccountIdOf q.account) q.token q.amount debit hs''.1 hr
  refine ⟨?_,hpools.1⟩
  rw [← Except.ok.inj h]
  exact hsFinal

theorem writer_deposit (d : Deployment) (w : World) (caller : Key)
    (target : DepositTarget) (token : Key) (amount msgValue : Nat)
    (obs : TransferObservation) (next : World)
    (hs : WorldSafe w xs)
    (h : deposit d w caller target token amount msgValue obs = .ok next) :
    WorldSafe next (nextGhost xs w next) := by
  simp only [deposit, allocateDeposit] at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
  obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
  let allocation : Checked (Nat × Core) := match target with
    | .rootId id => do
      ensure (id < width 40) .config
      requireRoot entered.core id
      pure (id, entered.core)
    | .owner owner => ensureRoot entered.core owner
  have h0 : (allocation >>= fun p =>
    ensure (amount > 0) .amount >>= fun _ =>
    ensure ((p.2.tokens token).enabled = true) .token >>= fun _ =>
    ((if token = 0 then
      ensure (msgValue = amount) .transfer >>= fun _ =>
      checkedAdd 256 entered.nativeCustody msgValue >>= fun custody =>
        pure ({ entered with core := p.2, nativeCustody := custody } : World)
    else
      ensure (msgValue = 0) .transfer >>= fun _ =>
      ensure (obs.readsSucceed = true ∧ obs.beforeBalance < width 256) .transfer >>= fun _ =>
      callbacks d obs.callbacks { entered with core := p.2 } >>= fun funded =>
      ensure (obs.callSucceeds = true ∧ obs.afterBalance < width 256) .transfer >>= fun _ =>
      ensure (obs.afterBalance > obs.beforeBalance ∧ obs.afterBalance - obs.beforeBalance ≤ amount) .transfer >>= fun _ =>
        pure funded) >>= fun funded =>
      requireLimiter funded >>= fun _ =>
      recordDeposit funded.limiter funded.now funded.quotes d.coreAddress d.coreAddress
        token (receivedAmount token amount obs) (funded.core.tokens token).decimals >>= fun lp =>
      checkedAdd 256 (funded.core.balances p.1 token) (receivedAmount token amount obs) >>= fun balance =>
      pure (guardExit d { funded with limiter := lp.2, core := { funded.core with
        balances := updateBalance funded.core.balances p.1 token balance } }))) = .ok next := by
    cases target <;> by_cases ht : token = 0 <;>
      simpa [allocation, ht, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
        Pure.pure, Except.pure] using h
  obtain ⟨id, core, _, h0⟩ := core_bind_pair_ok h0
  obtain ⟨_, h0⟩ := core_ensure_ok h0
  obtain ⟨_, h0⟩ := core_ensure_ok h0
  obtain ⟨funded, hf, h0⟩ := core_bind_ok h0
  have hsEntered : WorldSafe entered xs := by rw [heq]; exact hs
  have hframe : WorldSafe funded xs ∧ current funded.limiter.persistent.history = current entered.limiter.persistent.history := by
    split at hf
    · obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨custody, _, hf⟩ := core_bind_ok hf
      have hv := Except.ok.inj hf
      rw [← hv]
      exact ⟨hsEntered,rfl⟩
    · obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨out, hout, hf⟩ := core_bind_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      have hv := Except.ok.inj hf
      rw [← hv]
      exact writer_callbacks d obs.callbacks { entered with core := core } out hsEntered hout
  obtain ⟨u, _, h0⟩ := core_bind_ok h0
  obtain ⟨v, limiter, hlim, h0⟩ := core_bind_pair_ok h0
  obtain ⟨balance, _, h0⟩ := core_bind_ok h0
  have hv := Except.ok.inj h0
  rw [← hv]
  have hrecord := deposit_exact funded.limiter xs funded.now funded.quotes d.coreAddress d.coreAddress
    token (receivedAmount token amount obs) (funded.core.tokens token).decimals v limiter hframe.1 hlim
  have hD : current funded.limiter.persistent.history = current w.limiter.persistent.history := by
    simpa only [heq] using hframe.2
  have hg : nextGhost xs w (guardExit d { funded with limiter := limiter, core := { funded.core with balances := updateBalance funded.core.balances id token balance } }) =
      depositGhost xs funded.now (current funded.limiter.persistent.history) v := by
    change (if current limiter.persistent.history > current w.limiter.persistent.history
      then ghostWrite xs ⟨funded.now,current limiter.persistent.history⟩ else xs) = _
    rw [hrecord.2.1,hD]
    by_cases hv : v ≠ 0
    · have hp : current w.limiter.persistent.history < current w.limiter.persistent.history+v := by omega
      simp only [depositGhost,if_pos hv,if_pos hp]
    · have hz : v = 0 := by omega
      simp only [depositGhost,hz,Nat.add_zero,gt_iff_lt,lt_self_iff_false,if_false,ne_eq,not_true_eq_false]
  rw [hg]
  exact hrecord.1

theorem writer_fresh (d : Deployment) (now capacity rate : Nat)
    (owner fee registry : Key) (roles : Key → Roles) (w : World)
    (h : freshBoundPair d now capacity rate owner fee registry roles = .ok w) :
    WorldSafe w [] ∧ current w.limiter.persistent.history = 0 ∧ w.limiter.persistent.cursor = 0 ∧
    w.limiter.persistent.history.latestSequence = 0 ∧ w.limiter.persistent.drip.available = capacity*usdScale ∧
    w.limiter.transient.flowStarted = false ∧ w.core.limiterBound = true := by
  unfold freshBoundPair at h
  obtain ⟨_,h⟩ := core_ensure_ok h
  obtain ⟨limiter,hl,h⟩ := core_bind_ok h
  obtain ⟨id,core,hroot,h⟩ := core_bind_pair_ok h
  obtain ⟨registered,hregistered,h⟩ := core_bind_ok h
  simp only [policyAction] at hregistered
  obtain ⟨_,hregistered⟩ := core_ensure_ok hregistered
  obtain ⟨_,hregistered⟩ := core_ensure_ok hregistered
  obtain ⟨_,hregistered⟩ := core_ensure_ok hregistered
  rw [← Except.ok.inj hregistered] at h
  simp only [policyAction] at h
  obtain ⟨u,_,h⟩ := core_bind_ok h
  obtain ⟨_,h⟩ := core_ensure_ok h
  obtain ⟨_,h⟩ := core_ensure_ok h
  obtain ⟨_,h⟩ := core_ensure_ok h
  rw [← Except.ok.inj h]
  have hi := initialize_success now capacity rate limiter hl
  exact ⟨safe_initialize now capacity rate limiter hl,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2,hi.2.1,rfl⟩

theorem ghost_unchanged (w next : World) (xs : List Checkpoint)
    (hD : current next.limiter.persistent.history = current w.limiter.persistent.history) :
    nextGhost xs w next = xs := by simp only [nextGhost,hD,gt_iff_lt,lt_self_iff_false,if_false]

theorem writer_invoke (d : Deployment) (w : World) (entry : Entry) (next : World)
    (hs : WorldSafe w xs) (h : invoke d w entry = .ok next) : WorldSafe next (nextGhost xs w next) := by
  cases entry with
  | ordinary caller args obs =>
    have hi := writer_withdraw d w caller args obs next hs h
    rw [ghost_unchanged w next xs hi.2.1]; exact hi.1
  | approved caller args sig obs =>
    have hi := writer_approved d w caller args sig obs next hs h
    rw [ghost_unchanged w next xs hi.2]; exact hi.1
  | funding caller target token amount msgValue obs => exact writer_deposit d w caller target token amount msgValue obs next hs h
  | policy caller action =>
    have hi := writer_policy d w caller action next hs h
    rw [ghost_unchanged w next xs hi.2]; exact hi.1
  | environment action =>
    have hv := (Except.ok.inj h).symm
    have hi := writer_environment d w action hs
    rw [hv,ghost_unchanged w _ xs hi.2]; exact hi.1
  | abort error => contradiction

theorem writer_endTransaction (w : World) (hs : WorldSafe w xs) : WorldSafe (endTransaction w) xs := by
  exact ⟨hs.funding,(by intro h; cases h), (by intro h; cases h)⟩

theorem writer_nextTransaction (w next : World) (now : Nat) (hs : WorldSafe w xs)
    (h : nextTransaction w now = .ok next) : WorldSafe next xs := by
  unfold nextTransaction at h
  obtain ⟨ht,h⟩ := core_ensure_ok h
  rw [← Except.ok.inj h]
  exact ⟨funding_mono_time hs.funding ht,(by intro h; cases h), (by intro h; cases h)⟩

theorem writer_reachable (d : Deployment) (w : World) (xs : List Checkpoint) (hr : Reachable d w xs) : WorldSafe w xs := by
  induction hr with
  | initialized now capacity rate owner fee registry roles w h => exact (writer_fresh d now capacity rate owner fee registry roles w h).1
  | success w next xs entry hr ha h ih => exact writer_invoke d w entry next ih h
  | caughtFailure w xs entry err hr h ih => exact ih
  | endTx w xs hr ih => exact writer_endTransaction w ih
  | newTx w next xs now hr h ih => exact writer_nextTransaction w next now ih h

theorem initialization_and_writer_closure : InitializationAndWriterClosure := by
  refine ⟨?_,?_,?_,?_⟩
  · intro d now capacity rate owner fee registry roles w h
    exact (writer_fresh d now capacity rate owner fee registry roles w h).2
  · intro d w xs hr; exact (writer_reachable d w xs hr).funding
  · intro d w xs hr; exact core_safe_ranges (core_safe_reachable d w xs hr)
  · intro d w xs hr; exact (writer_reachable d w xs hr).cache

theorem transaction_and_snapshots : TransactionAndSnapshots :=
  core_transaction_and_snapshots_of_history beginFlow_first

#print axioms initialization_and_writer_closure
#print axioms transaction_and_snapshots

theorem capacity_normal (s : Limiter) (now : Nat) : capacityState s now =
    ((if s.transient.flowStarted then pure s.transient.expired else
      referenceAt s.persistent.history now >>= fun p => pure p.1) >>= fun E =>
    checkedSub (current s.persistent.history) (creditCursor s.persistent E) >>= fun C =>
    timestamp now >>= fun t => availableDrip s.persistent t >>= fun A => pure (C,A)) := by
  cases hf : s.transient.flowStarted <;>
    simp [capacityState,hf,Bind.bind,core_except_bind_assoc,core_except_ok_bind,Pure.pure,Except.pure]

theorem capacity_total (s : Limiter) (xs : List Checkpoint) (now A : Nat)
    (hs : LimiterSafe s xs now) (ht : now < width 64)
    (hA : availableDrip s.persistent now = .ok A) :
    capacityState s now = .ok (current s.persistent.history - max (expiredReference xs now).1 s.persistent.cursor,A) := by
  have href := HistoryProofs.referenceAt_exact s.persistent.history xs now hs.funding.1
    hs.funding.2.2.2.2.2.2.2.2.2.2 ht
  have hExp : (if s.transient.flowStarted then pure s.transient.expired else
      referenceAt s.persistent.history now >>= fun p => pure p.1) = .ok (expiredReference xs now).1 := by
    cases hf : s.transient.flowStarted with
    | true => simp only [hf,if_true,hs.cache hf,Pure.pure,Except.pure]
    | false => simp only [hf,Bool.false_eq_true,if_false,href,ok_bind,Pure.pure,Except.pure]
  have hle : max s.persistent.cursor (expiredReference xs now).1 ≤ current s.persistent.history :=
    max_le hs.funding.2.2.1 (expired_bounds hs.funding.1 now).1
  rw [capacity_normal,hExp,ok_bind]
  rw [show checkedSub (current s.persistent.history) (creditCursor s.persistent (expiredReference xs now).1) =
      .ok (current s.persistent.history-max s.persistent.cursor (expiredReference xs now).1) from
    sub_of_le _ _ hle]
  rw [ok_bind,timestamp_of_lt ht,ok_bind,hA,ok_bind]
  simp only [Nat.max_comm,Pure.pure,Except.pure]

theorem capacity_success (s : Limiter) (xs : List Checkpoint) (now C A : Nat)
    (hs : LimiterSafe s xs now) (h : capacityState s now = .ok (C,A)) :
    C = current s.persistent.history - max (expiredReference xs now).1 s.persistent.cursor ∧
    availableDrip s.persistent now = .ok A ∧ now < width 64 := by
  have h0 := h
  rw [capacity_normal] at h0
  obtain ⟨E,_,h0⟩ := core_bind_ok h0
  obtain ⟨c,_,h0⟩ := core_bind_ok h0
  obtain ⟨t,ht,h0⟩ := core_bind_ok h0
  obtain ⟨htEq,hw⟩ := timestamp_ok ht
  obtain ⟨a,ha,h0⟩ := core_bind_ok h0
  rw [htEq] at ha
  have hp := Except.ok.inj h0
  have haEq := congrArg Prod.snd hp
  simp only [Prod.snd] at haEq
  rw [haEq] at ha
  have exactCap := capacity_total s xs now A hs hw ha
  have hC := congrArg Prod.fst (Except.ok.inj (h.symm.trans exactCap))
  exact ⟨hC,ha,hw⟩

theorem gross_acc (ps : List Payout) (acc : Nat) :
    ps.foldl (fun total p => total + match p.funding with | some f => f.value | none => 0) acc =
    acc + ordinaryGrossValues ps := by
  induction ps generalizing acc with
  | nil => simp [ordinaryGrossValues]
  | cons p ps ih =>
    simp only [List.foldl_cons,ordinaryGrossValues]
    simp only [ih,Nat.zero_add,Nat.add_assoc]
    exact congrArg (Nat.add acc) (ih _).symm

theorem gross_append_ordinary (ps : List Payout) (token recipient : Key) (amount : Nat) (f : Funding) :
    ordinaryGrossValues (ps ++ [⟨.ordinary,token,recipient,amount,some f,none⟩]) = ordinaryGrossValues ps + f.value := by
  simp only [ordinaryGrossValues,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem single_conservation (d : Deployment) (w : World) (caller : Key)
    (args : OrdinaryArgs) (obs : TransferObservation) (next : World) (C A : Nat)
    (hs : WorldSafe w xs) (hcap : capacityState w.limiter w.now = .ok (C,A))
    (h : withdraw d w caller args obs = .ok next) :
    ∃ Cnew Anew, capacityState next.limiter next.now = .ok (Cnew,Anew) ∧
      ordinaryGrossValues w.payouts ≤ ordinaryGrossValues next.payouts ∧
      Cnew+Anew+(ordinaryGrossValues next.payouts-ordinaryGrossValues w.payouts) = C+A := by
  obtain ⟨hsnext,hD,hcheck,f,hlogs,hcons⟩ := writer_withdraw d w caller args obs next hs h
  obtain ⟨hC,hAvail,ht⟩ := capacity_success w.limiter xs w.now C A hs hcap
  have htime := (core_withdraw_frame d w caller args obs next h).1
  rcases hcons with ⟨a,ha,hcursor,hcredit,hused,hrest,hbound,hD',hS',hA',hC',hAvail'⟩
  have haEq : a = A := Except.ok.inj (ha.symm.trans hAvail)
  rw [haEq] at hbound hA' hAvail'
  have hused' : f.depositUsed = min f.value C := by simpa only [← hC] using hused
  have hbound' : f.value ≤ C+A := by simpa only [← hC] using hbound
  have hCnext : current next.limiter.persistent.history-max (expiredReference xs w.now).1 next.limiter.persistent.cursor = C-f.depositUsed := by
    rw [hD']
    simpa only [← hC] using hC'
  have hsnext' : LimiterSafe next.limiter xs w.now := by
    have hi : LimiterSafe next.limiter xs next.now := hsnext
    rw [htime] at hi
    exact hi
  have hnextcap := capacity_total next.limiter xs w.now (A-f.dripUsed) hsnext' ht hAvail'
  rw [hCnext] at hnextcap
  have hdelta : ordinaryGrossValues next.payouts = ordinaryGrossValues w.payouts+f.value := by
    rw [hlogs,gross_append_ordinary]
  refine ⟨C-f.depositUsed,A-f.dripUsed,?_,?_,?_⟩
  · rw [htime]; exact hnextcap
  · omega
  · omega

theorem batch_conservation (d : Deployment) (calls : List WithdrawalCall) (w next : World) (C A : Nat)
    (hs : WorldSafe w xs) (hcap : capacityState w.limiter w.now = .ok (C,A))
    (h : ordinaryBatch d calls w = .ok next) :
    ∃ Cnew Anew, capacityState next.limiter next.now = .ok (Cnew,Anew) ∧
      ordinaryGrossValues w.payouts ≤ ordinaryGrossValues next.payouts ∧
      Cnew+Anew+(ordinaryGrossValues next.payouts-ordinaryGrossValues w.payouts) = C+A := by
  induction calls generalizing w C A with
  | nil =>
    rw [← Except.ok.inj h]
    exact ⟨C,A,hcap,Nat.le_refl _,by omega⟩
  | cons c cs ih =>
    simp only [ordinaryBatch] at h
    obtain ⟨out,hout,hrest⟩ := core_bind_ok h
    obtain ⟨Cmid,Amid,hmid,hmono,hstep⟩ := single_conservation d w c.caller c.args c.observation out C A hs hcap hout
    have hsout := (writer_withdraw d w c.caller c.args c.observation out hs hout).1
    obtain ⟨Cnew,Anew,hnew,hmono',htail⟩ := ih out Cmid Amid hsout hmid hrest
    exact ⟨Cnew,Anew,hnew,hmono.trans hmono',by omega⟩

theorem ordinary_and_global_no_reuse : OrdinaryAndGlobalNoReuse := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro d w xs token amount decimals f next hr h
    exact (withdrawal_exact w.limiter xs w.now w.quotes d.coreAddress d.coreAddress token amount decimals f next
      (writer_reachable d w xs hr) h).2.1
  · intro d w xs caller args obs next hr ha h
    exact (writer_withdraw d w caller args obs next (writer_reachable d w xs hr) h).2.2
  · intro d w xs calls next C A hr hcap ha h
    obtain ⟨Cnew,Anew,hcap',hmono,heq⟩ := batch_conservation d calls w next C A (writer_reachable d w xs hr) hcap h
    exact ⟨Cnew,Anew,hcap',heq⟩
  · intro D E S Enew Snew hS hE hEn hSn hEm hSm
    omega
  · intro w; exact ⟨rfl,rfl⟩
  · intro d w xs token amount decimals v next hr h
    have hi := deposit_exact w.limiter xs w.now w.quotes d.coreAddress d.coreAddress token amount decimals v next
      (writer_reachable d w xs hr) h
    exact ⟨hi.2.1,hi.2.2.1,hi.2.2.2.1⟩

#print axioms ordinary_and_global_no_reuse
#print axioms batch_conservation

end Benchmark.Cases.Kuru.WithdrawalLimit
