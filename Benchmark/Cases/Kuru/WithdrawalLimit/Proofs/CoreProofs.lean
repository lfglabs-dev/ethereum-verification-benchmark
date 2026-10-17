import Benchmark.Cases.Kuru.WithdrawalLimit.Proofs.ArithmeticProofs

namespace Benchmark.Cases.Kuru.WithdrawalLimit

/-- Invert actual successful checked execution, without adding caller premises. -/
theorem core_bind_ok {α β : Type} {m : Checked α} {f : α → Checked β} {v : β}
    (h : (m >>= f) = .ok v) : ∃ x, m = .ok x ∧ f x = .ok v := by
  cases hm : m with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok x => exact ⟨x, rfl, by simpa [hm, Bind.bind, Except.bind] using h⟩

theorem core_ensure_ok {α : Type} {p : Prop} [Decidable p] {e : Error}
    {m : Checked α} {v : α} (h : (do ensure p e; m) = .ok v) : p ∧ m = .ok v := by
  by_cases hp : p
  · exact ⟨hp, by simpa [ensure, hp, Bind.bind, Except.bind] using h⟩
  · simp [ensure, hp, Bind.bind, Except.bind] at h

theorem core_ensure_success {p : Prop} [Decidable p] {e : Error} {u : Unit}
    (h : ensure p e = .ok u) : p := by
  by_cases hp : p
  · exact hp
  · simp [ensure, hp] at h

theorem core_checkedAdd_ok {bits a b v : Nat} (h : checkedAdd bits a b = .ok v) :
    v = a + b ∧ v < width bits := by
  unfold checkedAdd at h
  obtain ⟨hr, h⟩ := core_ensure_ok h
  have hv := Except.ok.inj h
  exact ⟨hv.symm, hv ▸ hr⟩

theorem core_bind_assoc {α β γ : Type} (m : Checked α) (f : α → Checked β)
    (g : β → Checked γ) : ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  cases m <;> rfl

theorem core_except_bind_assoc {α β γ : Type} (m : Checked α) (f : α → Checked β)
    (g : β → Checked γ) : Except.bind (Except.bind m f) g =
    Except.bind m (fun x => Except.bind (f x) g) := by
  cases m <;> rfl

theorem core_except_ok_bind {α β : Type} (x : α) (f : α → Checked β) :
    Except.bind (.ok x : Checked α) f = f x := rfl

/-- Shared allocator changes only its counter and one account record. -/
theorem core_registerAccount_success (c : Core) (owner : Key) (root sequence id : Nat)
    (next : Core) (h : registerAccount c owner root sequence = .ok (id, next)) :
    id = c.lastAccountId + 1 ∧ id < width 40 ∧
    next = { c with lastAccountId := id, accounts := fun i =>
      if i = id then ⟨owner, if root = 0 then id else root, sequence⟩ else c.accounts i } := by
  unfold registerAccount at h
  obtain ⟨n, hn, h⟩ := core_bind_ok h
  obtain ⟨heq, hlt⟩ := core_checkedAdd_ok hn
  have hv := Except.ok.inj h
  have hi := congrArg Prod.fst hv
  have hc := congrArg Prod.snd hv
  simp only [Prod.fst, Prod.snd] at hi hc
  exact ⟨hi.symm.trans heq, hi ▸ hlt, by simpa only [hi] using hc.symm⟩

/-- Root allocation cannot reset a previously consumed approved nonce. -/
theorem core_ensureRoot_stable (c : Core) (owner : Key) (id : Nat) (next : Core)
    (h : ensureRoot c owner = .ok (id, next)) :
    next.approvedNonces = c.approvedNonces ∧ next.epoch = c.epoch ∧
    next.guardWord = c.guardWord ∧ next.balances = c.balances := by
  unfold ensureRoot at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  dsimp only at h
  split at h
  · have hv := Except.ok.inj h
    have hc := congrArg Prod.snd hv
    simp only [Prod.snd] at hc
    subst next
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨p, hp, h⟩ := core_bind_ok h
    rcases p with ⟨n, allocated⟩
    obtain ⟨_, _, ha⟩ := core_registerAccount_success c owner 0 0 n allocated hp
    have hv := Except.ok.inj h
    have hc := congrArg Prod.snd hv
    simp only [Prod.snd] at hc
    rw [← hc, ha]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Child allocation retains nonce, epoch, balance and persistent guard records. -/
theorem core_createSubaccount_stable (c : Core) (root id : Nat) (next : Core)
    (h : createSubaccount c root = .ok (id, next)) :
    next.approvedNonces = c.approvedNonces ∧ next.epoch = c.epoch ∧
    next.guardWord = c.guardWord ∧ next.balances = c.balances := by
  unfold createSubaccount at h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨p, hp, h⟩ := core_bind_ok h
  rcases p with ⟨n, allocated⟩
  obtain ⟨_, _, ha⟩ := core_registerAccount_success c (c.accounts root).owner root
    ((c.subaccountsByRoot root).length + 1) n allocated hp
  have hv := Except.ok.inj h
  have hc := congrArg Prod.snd hv
  simp only [Prod.snd] at hc
  rw [← hc, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem core_guardEnter_success (d : Deployment) (w next : World)
    (h : guardEnter d w = .ok next) :
    w.core.guardWord ≠ d.coreAddress.toNat ∧
    next = { w with core := { w.core with guardWord := d.coreAddress.toNat } } := by
  unfold guardEnter at h
  obtain ⟨hg, h⟩ := core_ensure_ok h
  exact ⟨hg, (Except.ok.inj h).symm⟩

theorem core_activeGuardEnter_success (d : Deployment) (w next : World)
    (h : activeGuardEnter d w = .ok next) :
    w.core.paused = false ∧ w.core.guardWord ≠ d.coreAddress.toNat ∧
    next = { w with core := { w.core with guardWord := d.coreAddress.toNat } } := by
  unfold activeGuardEnter at h
  obtain ⟨hp, h⟩ := core_ensure_ok h
  exact ⟨hp, core_guardEnter_success d w next h⟩

/-- Transaction end resets transient storage only. -/
theorem core_endTransaction_frame (w : World) :
    (endTransaction w).now = w.now ∧ (endTransaction w).core = w.core ∧
    (endTransaction w).limiter.persistent = w.limiter.persistent ∧
    (endTransaction w).nativeCustody = w.nativeCustody ∧
    (endTransaction w).payouts = w.payouts ∧
    (endTransaction w).limiter.transient.flowStarted = false ∧
    (∀ k, (endTransaction w).limiter.transient.prices k = 0) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem core_caught_failure (w : World) (action : World → Checked World) (err : Error)
    (h : action w = .error err) : caughtCall w action = w := by
  simp [caughtCall, h]

theorem core_outer_rollback (d : Deployment) (w : World) (calls : List RouteCall)
    (err : Error) (h : route d calls w = .error err) :
    executeTransaction d w calls = endTransaction w := by
  simp [executeTransaction, h]

theorem core_subroute_rollback (d : Deployment) (w : World)
    (precedingCalls subroute : List RouteCall) (previous : World) (err : Error)
    (_hp : route d precedingCalls w = .ok previous)
    (h : route d subroute previous = .error err) :
    caughtCall previous (fun s => route d subroute s) = previous := by
  exact core_caught_failure previous _ err h

theorem core_nested_guard_reject (d : Deployment) (w : World) (caller : Key)
    (hg : w.core.guardWord = d.coreAddress.toNat) (hp : w.core.paused = false) :
    policyAction d w caller .nestedGuarded = .error .reentrant := by
  simp [policyAction, activeGuardEnter, guardEnter, ensure, hp, hg, Bind.bind, Except.bind]

theorem core_receiveNative_frame (d : Deployment) (w : World) (caller : Key)
    (amount : Nat) (next : World)
    (h : policyAction d w caller (.receiveNative amount) = .ok next) :
    next.limiter = w.limiter ∧ next.payouts = w.payouts ∧
    next.nativeCustody = w.nativeCustody + amount := by
  unfold policyAction at h
  obtain ⟨n, hn, h⟩ := core_bind_ok h
  obtain ⟨heq, _⟩ := core_checkedAdd_ok hn
  have hv := Except.ok.inj h
  rw [← hv, heq]
  exact ⟨rfl, rfl, rfl⟩

theorem core_internalFrame_frame (w : World) (f : InternalFrame) :
    (applyInternalFrame w f).limiter = w.limiter ∧
    (applyInternalFrame w f).payouts = w.payouts ∧
    (applyInternalFrame w f).nativeCustody = w.nativeCustody := by
  exact ⟨rfl, rfl, rfl⟩

/-- beginFlow changes the reference cache, never the three funding pools. -/
theorem core_beginFlow_pools (s : Limiter) (now : Nat) (next : Limiter)
    (h : beginFlow s now = .ok next) : SameFundingPools s next ∧
    next.transient.flowStarted = true := by
  unfold beginFlow at h
  split at h
  · have hv := Except.ok.inj h
    subst next
    exact ⟨⟨rfl, rfl, rfl⟩, by assumption⟩
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨t, _, h⟩ := core_bind_ok h
    obtain ⟨p, _, h⟩ := core_bind_ok h
    rcases p with ⟨expired, sequence⟩
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

theorem core_snapshotPrice_frame (s : Limiter) (fetch : PriceFetch) (token : Key)
    (quote : Nat) (next : Limiter) (h : snapshotPrice s fetch token = .ok (quote, next)) :
    next.transient.prices token = quote ∧ SamePersistent s next ∧
    next.transient.flowStarted = s.transient.flowStarted := by
  unfold snapshotPrice at h
  obtain ⟨q, _, h⟩ := core_bind_ok h
  have hv := Except.ok.inj h
  have hq := congrArg Prod.fst hv
  have hs := congrArg Prod.snd hv
  simp only [Prod.fst, Prod.snd] at hq hs
  rw [← hs, ← hq]
  exact ⟨by simp, rfl, rfl⟩

theorem core_approvedLimiter_frame (s : Limiter) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (next : Limiter)
    (h : checkApprovedWithdrawal s now fetch caller core token = .ok next) :
    SameFundingPools s next ∧ next.transient.flowStarted = true := by
  unfold checkApprovedWithdrawal at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨started, hstarted, h⟩ := core_bind_ok h
  obtain ⟨p, hp, h⟩ := core_bind_ok h
  rcases p with ⟨quote, snapped⟩
  obtain ⟨hf, hflow⟩ := core_beginFlow_pools s now started hstarted
  obtain ⟨_, hpers, ht⟩ := core_snapshotPrice_frame started fetch token quote snapped hp
  have hv := Except.ok.inj h
  subst next
  exact ⟨by simpa [SameFundingPools, SamePersistent] using hpers ▸ hf, ht.trans hflow⟩

/-- Every source checkpoint and the exact pre-CALL increment, for arbitrary inputs. -/
theorem core_approvedBeforeTransfer_success (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (checkpoint : World)
    (h : approvedBeforeTransfer d w caller q sig = .ok checkpoint) :
    ApprovedCheckpoints d w caller q sig ∧
    checkpoint.core.approvedNonces q.account = q.nonce + 1 ∧
    checkpoint.core.balances (w.core.rootAccountIdOf q.account) q.token =
      w.core.balances (w.core.rootAccountIdOf q.account) q.token - q.amount ∧
    checkpoint.core.guardWord = d.coreAddress.toNat ∧
    SameFundingPools w.limiter checkpoint.limiter := by
  unfold approvedBeforeTransfer at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, hentered, h⟩ := core_bind_ok h
  obtain ⟨hp, hg, he⟩ := core_activeGuardEnter_success d w entered hentered
  subst entered
  obtain ⟨hauth, h⟩ := core_ensure_ok h
  obtain ⟨u, hroot, h⟩ := core_bind_ok h
  unfold requireRoot at hroot
  obtain ⟨hrnz, hroot⟩ := core_ensure_ok hroot
  have hr := core_ensure_success hroot
  obtain ⟨hamount, h⟩ := core_ensure_ok h
  obtain ⟨hrecipient, h⟩ := core_ensure_ok h
  obtain ⟨hdeadline, h⟩ := core_ensure_ok h
  obtain ⟨hepoch, h⟩ := core_ensure_ok h
  obtain ⟨hnonce, h⟩ := core_ensure_ok h
  obtain ⟨hsig, h⟩ := core_ensure_ok h
  obtain ⟨u, hrelease, h⟩ := core_bind_ok h
  unfold requireRelease at hrelease
  have hfreeze := core_ensure_success hrelease
  obtain ⟨n, hn, h⟩ := core_bind_ok h
  obtain ⟨heqn, _⟩ := core_checkedAdd_ok hn
  obtain ⟨hbalance, h⟩ := core_ensure_ok h
  obtain ⟨u, hbound, h⟩ := core_bind_ok h
  unfold requireLimiter at hbound
  have hb := core_ensure_success hbound
  obtain ⟨limiter, hl, h⟩ := core_bind_ok h
  obtain ⟨hpool, _⟩ := core_approvedLimiter_frame w.limiter w.now w.quotes
    d.coreAddress d.coreAddress q.token limiter hl
  have hv := Except.ok.inj h
  rw [← hv]
  refine ⟨?_, ?_, ?_, rfl, hpool⟩
  · exact ⟨hp, hg, hrnz, hr, hamount, hrecipient.1, hrecipient.2, hbalance,
      hb, hauth.1, hauth.2, hepoch, hnonce, hdeadline, hsig, hfreeze.1, hfreeze.2⟩
  · simp [update, heqn]
  · simp [updateBalance]

theorem core_invalidateNonce_success (d : Deployment) (w : World) (caller account : Key)
    (n : Nat) (next : World)
    (h : policyAction d w caller (.invalidateNonce account n) = .ok next) :
    next.core.approvedNonces account = n ∧ w.core.approvedNonces account < n := by
  unfold policyAction at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨hlt, h⟩ := core_ensure_ok h
  have hv := Except.ok.inj h
  rw [← hv]
  exact ⟨by simp [update], hlt⟩

theorem core_rotateAuthority_success (d : Deployment) (w : World) (caller authority : Key)
    (next : World) (h : policyAction d w caller (.rotateAuthority authority) = .ok next) :
    next.core.epoch = w.core.epoch + 1 := by
  unfold policyAction at h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨n, hn, h⟩ := core_bind_ok h
  obtain ⟨heq, _⟩ := core_checkedAdd_ok hn
  have hv := Except.ok.inj h
  rw [← hv]
  exact heq

/-- All admitted non-custody environment frames retain physical payout logs,
    limiter storage, fixed transaction time and consumed nonces. -/
theorem core_environment_frame (d : Deployment) (w : World) (a : EnvironmentAction) :
    (environmentAction d w a).now = w.now ∧
    (environmentAction d w a).limiter = w.limiter ∧
    (environmentAction d w a).payouts = w.payouts ∧
    (environmentAction d w a).core.approvedNonces = w.core.approvedNonces := by
  cases a with
  | publish source quote => exact ⟨rfl, rfl, rfl, rfl⟩
  | registryResponse registry roles => exact ⟨rfl, rfl, rfl, rfl⟩
  | ensureRootAccount owner =>
    simp only [environmentAction]
    cases h : ensureRoot w.core owner with
    | error e => exact ⟨rfl, rfl, rfl, rfl⟩
    | ok p =>
      rcases p with ⟨id, core⟩
      exact ⟨rfl, rfl, rfl, (core_ensureRoot_stable w.core owner id core h).1⟩
  | createChild owner =>
    simp only [environmentAction]
    split
    · rename_i next h
      obtain ⟨entered, he, h⟩ := core_bind_ok h
      obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
      subst entered
      obtain ⟨p, hp, h⟩ := core_bind_ok h
      rcases p with ⟨root, core⟩
      obtain ⟨hn, _, _, _⟩ := core_ensureRoot_stable _ owner root core hp
      obtain ⟨p, hp, h⟩ := core_bind_ok h
      rcases p with ⟨id, childCore⟩
      obtain ⟨hcn, _, _, _⟩ := core_createSubaccount_stable core root id childCore hp
      have hv := Except.ok.inj h
      rw [← hv]
      exact ⟨rfl, rfl, rfl, hcn.trans hn⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  | internalFrame frame =>
    simp only [environmentAction]
    split
    · rename_i next h
      have h0 : ((if frame.protocolActive then ensure (w.core.paused = false) .paused
          else pure ()) >>= fun _ =>
        ((if frame.guarded then guardEnter d w else pure w) >>= fun entered =>
          ((match frame.registerRoot with
            | none => pure entered
            | some owner => ensureRoot entered.core owner >>= fun p =>
                pure ({ entered with core := p.2 } : World)) >>= fun registered =>
              pure (if frame.guarded then guardExit d (applyInternalFrame registered frame)
                else applyInternalFrame registered frame)))) = .ok next := by
        cases hp : frame.protocolActive <;> cases hg : frame.guarded <;>
          cases hr : frame.registerRoot <;>
          simpa [hp, hg, hr, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
            Pure.pure, Except.pure] using h
      clear h
      have h := h0
      obtain ⟨u, _, h⟩ := core_bind_ok h
      obtain ⟨entered, he, h⟩ := core_bind_ok h
      have heFrame : entered.now = w.now ∧ entered.limiter = w.limiter ∧
          entered.payouts = w.payouts ∧ entered.core.approvedNonces = w.core.approvedNonces := by
        split at he
        · obtain ⟨_, heq⟩ := core_guardEnter_success d w entered he
          rw [heq]
          exact ⟨rfl, rfl, rfl, rfl⟩
        · have heq := Except.ok.inj he
          rw [← heq]
          exact ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨registered, hr, h⟩ := core_bind_ok h
      have hrFrame : registered.now = entered.now ∧ registered.limiter = entered.limiter ∧
          registered.payouts = entered.payouts ∧
          registered.core.approvedNonces = entered.core.approvedNonces := by
        cases ho : frame.registerRoot with
        | none =>
          simp only [ho] at hr
          have heq := Except.ok.inj hr
          rw [← heq]
          exact ⟨rfl, rfl, rfl, rfl⟩
        | some owner =>
          simp only [ho] at hr
          obtain ⟨p, hp, hr⟩ := core_bind_ok hr
          rcases p with ⟨id, core⟩
          have hn := (core_ensureRoot_stable entered.core owner id core hp).1
          have heq := Except.ok.inj hr
          rw [← heq]
          exact ⟨rfl, rfl, rfl, hn⟩
      have hv := Except.ok.inj h
      rw [← hv]
      split <;> exact ⟨hrFrame.1.trans heFrame.1, hrFrame.2.1.trans heFrame.2.1,
        hrFrame.2.2.1.trans heFrame.2.2.1, hrFrame.2.2.2.trans heFrame.2.2.2⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Folding arbitrary environment callback preludes retains these exact fields. -/
theorem core_environment_fold_frame (d : Deployment) (as : List EnvironmentAction)
    (w : World) :
    (as.foldl (environmentAction d) w).now = w.now ∧
    (as.foldl (environmentAction d) w).limiter = w.limiter ∧
    (as.foldl (environmentAction d) w).payouts = w.payouts ∧
    (as.foldl (environmentAction d) w).core.approvedNonces = w.core.approvedNonces := by
  induction as generalizing w with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    obtain ⟨hn, hl, hp, hnonce⟩ := core_environment_frame d w a
    obtain ⟨hn', hl', hp', hnonce'⟩ := ih (environmentAction d w a)
    exact ⟨hn'.trans hn, hl'.trans hl, hp'.trans hp, hnonce'.trans hnonce⟩

theorem core_configureToken_success (d : Deployment) (w : World) (caller token : Key)
    (enabled : Bool) (metadata : Checked Nat) (next : World)
    (h : policyAction d w caller (.configureToken token enabled metadata) = .ok next) :
    ∃ config, next = { w with core := { w.core with tokens := update w.core.tokens token config } } := by
  simp only [policyAction] at h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  try dsimp only at h
  have h0 : ((if enabled then
      ((if token = 0 then pure 18 else metadata) >>= fun dec =>
        ensure (dec ≤ 77) .config >>= fun _ =>
          ((if (w.core.tokens token).seen then ensure ((w.core.tokens token).decimals = dec) .config
            else pure ()) >>= fun _ =>
            requireLimiter w >>= fun _ =>
              price w.limiter w.quotes token >>= fun _ => pure (TokenConfig.mk dec true true)))
      else pure (TokenConfig.mk (w.core.tokens token).decimals false (w.core.tokens token).seen)) >>=
      fun config => pure ({ w with core := { w.core with tokens := update w.core.tokens token config } } : World)) = .ok next := by
    by_cases ht : token = 0
    · subst token
      cases he : enabled <;> cases hs : (w.core.tokens 0).seen <;>
        simpa [he, hs, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
          Pure.pure, Except.pure] using h
    · cases he : enabled <;> cases hs : (w.core.tokens token).seen <;>
        simpa [he, hs, ht, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
          Pure.pure, Except.pure] using h
  obtain ⟨config, _, h0⟩ := core_bind_ok h0
  exact ⟨config, (Except.ok.inj h0).symm⟩

/-- Unguarded setters can rotate or freeze after the checkpoint, but cannot
    lower any nonce or reset a started flow's funding pools. -/
theorem core_policy_frame (d : Deployment) (w : World) (caller : Key)
    (a : PolicyAction) (next : World) (h : policyAction d w caller a = .ok next) :
    next.now = w.now ∧ next.payouts = w.payouts ∧
    (∀ k, w.core.approvedNonces k ≤ next.core.approvedNonces k) ∧
    (w.limiter.transient.flowStarted = true → next.limiter = w.limiter) := by
  cases a with
  | setFeeCollector owner =>
    unfold policyAction at h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨p, hp, h⟩ := core_bind_ok h
    rcases p with ⟨id, core⟩
    have hn := (core_ensureRoot_stable w.core owner id core hp).1
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun k => by simp [hn], fun _ => rfl⟩
  | setRegistry registry =>
    unfold policyAction at h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | pause paused =>
    cases paused with
    | false =>
      simp only [policyAction, Bool.false_eq_true, if_false] at h
      obtain ⟨_, h⟩ := core_ensure_ok h
      obtain ⟨_, h⟩ := core_ensure_ok h
      have hv := Except.ok.inj h
      rw [← hv]
      exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
    | true =>
      simp only [policyAction, if_true] at h
      obtain ⟨u, _, h⟩ := core_bind_ok h
      have hv := Except.ok.inj h
      rw [← hv]
      exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | rotateAuthority authority =>
    unfold policyAction at h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨n, _, h⟩ := core_bind_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | freeze frozen =>
    cases frozen <;> simp only [policyAction, Bool.false_eq_true, if_false, if_true] at h
    all_goals
      obtain ⟨u, _, h⟩ := core_bind_ok h
      have hv := Except.ok.inj h
      rw [← hv]
      exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | freezeToken token frozen =>
    cases frozen <;> simp only [policyAction, Bool.false_eq_true, if_false, if_true] at h
    all_goals
      obtain ⟨u, _, h⟩ := core_bind_ok h
      have hv := Except.ok.inj h
      rw [← hv]
      exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | invalidateNonce account n =>
    unfold policyAction at h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨hlt, h⟩ := core_ensure_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    refine ⟨rfl, rfl, ?_, fun _ => rfl⟩
    intro k
    by_cases hk : k = account
    · simp [update, hk]
      exact Nat.le_of_lt hlt
    · simp [update, hk]
  | bindLimiter limiter =>
    unfold policyAction at h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | configureDrip capacity rate =>
    unfold policyAction at h
    obtain ⟨l, hl, h⟩ := core_bind_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    refine ⟨rfl, rfl, fun _ => Nat.le_refl _, ?_⟩
    intro hflow
    unfold setDripConfig at hl
    obtain ⟨_, hl⟩ := core_ensure_ok hl
    obtain ⟨hfalse, _⟩ := core_ensure_ok hl
    simp [hflow] at hfalse
  | configureSource token source =>
    unfold policyAction at h
    obtain ⟨l, hl, h⟩ := core_bind_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    refine ⟨rfl, rfl, fun _ => Nat.le_refl _, ?_⟩
    intro hflow
    unfold setPriceSource at hl
    obtain ⟨_, hl⟩ := core_ensure_ok hl
    obtain ⟨hfalse, _⟩ := core_ensure_ok hl
    simp [hflow] at hfalse
  | configureToken token enabled metadata =>
    obtain ⟨config, hv⟩ := core_configureToken_success d w caller token enabled metadata next h
    rw [hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | receiveNative amount =>
    unfold policyAction at h
    obtain ⟨n, _, h⟩ := core_bind_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | nestedGuarded =>
    unfold policyAction at h
    obtain ⟨entered, _, h⟩ := core_bind_ok h
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | observe =>
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩

/-- Callback induction includes real ordered preludes and caught/propagated errors. -/
theorem core_callbacks_frame (d : Deployment) (cs : List Callback) (w next : World)
    (h : callbacks d cs w = .ok next) :
    next.now = w.now ∧ next.payouts = w.payouts ∧
    (∀ k, w.core.approvedNonces k ≤ next.core.approvedNonces k) ∧
    (w.limiter.transient.flowStarted = true → next.limiter = w.limiter) := by
  induction cs generalizing w with
  | nil =>
    have hv := Except.ok.inj h
    rw [← hv]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _, fun _ => rfl⟩
  | cons c cs ih =>
    obtain ⟨hn, hl, hp, hnonce⟩ := core_environment_fold_frame d c.environmentBefore w
    simp only [callbacks] at h
    cases ha : policyAction d (c.environmentBefore.foldl (environmentAction d) w) c.caller c.action with
    | ok intermediate =>
      rw [ha] at h
      obtain ⟨hn1, hp1, hnonce1, hl1⟩ := core_policy_frame d _ c.caller c.action intermediate ha
      obtain ⟨hn2, hp2, hnonce2, hl2⟩ := ih intermediate h
      refine ⟨hn2.trans (hn1.trans hn), hp2.trans (hp1.trans hp), ?_, ?_⟩
      · intro k
        rw [← hnonce]
        exact (hnonce1 k).trans (hnonce2 k)
      · intro hflow
        have hflow0 : (c.environmentBefore.foldl (environmentAction d) w).limiter.transient.flowStarted = true :=
          by rw [hl]; exact hflow
        have heq1 := hl1 hflow0
        have hflow1 : intermediate.limiter.transient.flowStarted = true := by rw [heq1]; exact hflow0
        exact (hl2 hflow1).trans (heq1.trans hl)
    | error e =>
      rw [ha] at h
      dsimp only at h
      split at h
      · obtain ⟨hn2, hp2, hnonce2, hl2⟩ := ih _ h
        refine ⟨hn2.trans hn, hp2.trans hp, ?_, ?_⟩
        · intro k
          rw [← hnonce]
          exact hnonce2 k
        · intro hflow
          have hflow0 : (c.environmentBefore.foldl (environmentAction d) w).limiter.transient.flowStarted = true :=
            by rw [hl]; exact hflow
          exact (hl2 hflow0).trans hl
      · contradiction

/-- The measured return is tied to observations, never freely chosen. -/
theorem core_transfer_debit (d : Deployment) (w : World) (token recipient : Key)
    (amount debit : Nat) (obs : TransferObservation) (next : World)
    (h : transferAsset d w token recipient amount obs = .ok (debit, next)) :
    debit = debitedAmount token amount obs ∧ debit ≤ amount ∧ (amount > 0 → debit > 0) := by
  unfold transferAsset at h
  by_cases ht : token = 0
  · simp only [ht, if_pos] at h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨out, _, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := congrArg Prod.fst (Except.ok.inj h)
    dsimp only at hv
    exact ⟨by simpa [debitedAmount, ht] using hv.symm, by omega, by omega⟩
  · simp only [ht, if_false] at h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨out, _, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨hd, h⟩ := core_ensure_ok h
    have hv := congrArg Prod.fst (Except.ok.inj h)
    dsimp only at hv
    exact ⟨by simpa [debitedAmount, ht] using hv.symm, by omega, by omega⟩

theorem core_withdrawBefore_success (d : Deployment) (w next : World)
    (id : Nat) (token : Key) (amount : Nat)
    (h : withdrawBeforeTransfer d w id token amount = .ok next) :
    w.core.balances id token ≥ amount ∧ w.core.limiterBound = true ∧
    ∃ limiter, checkApprovedWithdrawal w.limiter w.now w.quotes d.coreAddress d.coreAddress token = .ok limiter ∧
      next = { w with core := { w.core with balances := updateBalance w.core.balances id token (w.core.balances id token - amount) }, limiter := limiter } := by
  unfold withdrawBeforeTransfer at h
  obtain ⟨hb, h⟩ := core_ensure_ok h
  obtain ⟨u, hu, h⟩ := core_bind_ok h
  have hl := core_ensure_success hu
  obtain ⟨limiter, hp, h⟩ := core_bind_ok h
  exact ⟨hb, hl, limiter, hp, (Except.ok.inj h).symm⟩

theorem core_refund_frame (w next : World) (id : Nat) (token : Key) (amount debit : Nat)
    (h : refundAsset w id token amount debit = .ok next) :
    next.now = w.now ∧ next.payouts = w.payouts ∧ next.limiter = w.limiter ∧
      next.core.approvedNonces = w.core.approvedNonces ∧
      next.core.balances id token = w.core.balances id token + (amount - debit) := by
  unfold refundAsset at h
  split at h
  · obtain ⟨balance, hb, h⟩ := core_bind_ok h
    have he := (core_checkedAdd_ok hb).1
    rw [← Except.ok.inj h]
    exact ⟨rfl, rfl, rfl, rfl, by simpa [updateBalance] using he⟩
  · have hv := Except.ok.inj h
    subst next
    exact ⟨rfl, rfl, rfl, rfl, by omega⟩

/-- transferAsset retains time/logs and monotone nonces even with native refunds. -/
theorem core_transferAsset_frame (d : Deployment) (w : World) (token recipient : Key)
    (amount : Nat) {debited : Nat} (obs : TransferObservation) (next : World)
    (h : transferAsset d w token recipient amount obs = .ok (debited, next)) :
    next.now = w.now ∧ next.payouts = w.payouts ∧
    (∀ k, w.core.approvedNonces k ≤ next.core.approvedNonces k) ∧
    (w.limiter.transient.flowStarted = true → next.limiter = w.limiter) := by
  unfold transferAsset at h
  split at h
  · obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨out, hout, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := congrArg Prod.snd (Except.ok.inj h)
    dsimp only at hv
    subst next
    simpa only using core_callbacks_frame d obs.callbacks
      { w with nativeCustody := w.nativeCustody - amount } out hout
  · obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨out, hout, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := congrArg Prod.snd (Except.ok.inj h)
    dsimp only at hv
    subst next
    exact core_callbacks_frame d obs.callbacks w out hout

/-- The successful checkpoint also starts flow and retains outer time/logs. -/
theorem core_approvedBeforeTransfer_frame (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (next : World)
    (h : approvedBeforeTransfer d w caller q sig = .ok next) :
    next.now = w.now ∧ next.payouts = w.payouts ∧ next.limiter.transient.flowStarted = true := by
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
  have hflow := (core_approvedLimiter_frame w.limiter w.now w.quotes
    d.coreAddress d.coreAddress q.token l hl).2
  have hv := Except.ok.inj h
  rw [← hv]
  exact ⟨rfl, rfl, hflow⟩

/-- No reachable-state or deployment premise is inserted in replay exclusion. -/
theorem core_approved_success (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (obs : TransferObservation)
    (next : World) (h : fulfillApprovedWithdrawal d w caller q sig obs = .ok next) :
    ApprovedCheckpoints d w caller q sig ∧
    q.nonce + 1 ≤ next.core.approvedNonces q.account ∧
    SameFundingPools w.limiter next.limiter ∧
    next.payouts = w.payouts ++ [⟨.approved, q.token, q.recipient, debitedAmount q.token q.amount obs, none, some q⟩] ∧
    next.now = w.now := by
  unfold fulfillApprovedWithdrawal at h
  obtain ⟨prepared, hprepared, h⟩ := core_bind_ok h
  obtain ⟨hc, hnonce, _, _, hpools⟩ := core_approvedBeforeTransfer_success d w caller q sig prepared hprepared
  obtain ⟨hnow, hlogs, hflow⟩ := core_approvedBeforeTransfer_frame d w caller q sig prepared hprepared
  obtain ⟨pair, hout, h⟩ := core_bind_ok h
  rcases pair with ⟨debit, out⟩
  have hd := (core_transfer_debit d prepared q.token q.recipient q.amount debit obs out hout).1
  obtain ⟨houtnow, houtlogs, houtnonce, houtlimiter⟩ :=
    core_transferAsset_frame d prepared q.token q.recipient q.amount obs out hout
  obtain ⟨refunded, hrefund, h⟩ := core_bind_ok h
  obtain ⟨hrnow, hrlogs, hrli, hrnonce, _⟩ :=
    core_refund_frame out refunded (w.core.rootAccountIdOf q.account) q.token q.amount debit hrefund
  have hv := Except.ok.inj h
  rw [← hv]
  refine ⟨hc, ?_, ?_, ?_, hrnow.trans (houtnow.trans hnow)⟩
  · change q.nonce + 1 ≤ refunded.core.approvedNonces q.account
    rw [hrnonce, ← hnonce]
    exact houtnonce q.account
  · change SameFundingPools w.limiter refunded.limiter
    rw [hrli, houtlimiter hflow]
    exact hpools
  · simp only [guardExit, hrlogs, houtlogs, hlogs, hd]

theorem core_approved_replay_rejected (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (obs : TransferObservation)
    (first second : World) (h : fulfillApprovedWithdrawal d w caller q sig obs = .ok first) :
    fulfillApprovedWithdrawal d first caller q sig obs ≠ .ok second := by
  intro hsecond
  have hnonce := (core_approved_success d w caller q sig obs first h).2.1
  have hcheckpoint := (core_approved_success d first caller q sig obs second hsecond).1
  have heq := hcheckpoint.2.2.2.2.2.2.2.2.2.2.2.2.1
  change q.nonce = first.core.approvedNonces q.account at heq
  omega

/-- Entire group7: measured receipts and the retained arbitrary-input checkpoint/replay clauses. -/
theorem approved_authority_and_replay : ApprovedAuthorityAndReplay := by
  refine ⟨core_approvedBeforeTransfer_success, ?_, core_invalidateNonce_success,
    core_rotateAuthority_success, core_approved_replay_rejected⟩
  intro d w xs caller q sig obs next _hr _ha h
  obtain ⟨hc, hn, hp, hlogs, _⟩ := core_approved_success d w caller q sig obs next h
  exact ⟨hc, hn, hp, hlogs⟩

theorem core_bind_pair_ok {α β γ : Type} {m : Checked (α × β)}
    {f : α × β → Checked γ} {v : γ} (h : (m >>= f) = .ok v) :
    ∃ a b, m = .ok (a,b) ∧ f (a,b) = .ok v := by
  obtain ⟨p, hp, hf⟩ := core_bind_ok h
  exact ⟨p.1, p.2, hp, hf⟩

/-- Gross ordinary receipt framing; no net-custody interpretation. -/
theorem core_withdraw_frame (d : Deployment) (w : World) (caller : Key)
    (a : OrdinaryArgs) (obs : TransferObservation) (next : World)
    (h : withdraw d w caller a obs = .ok next) :
    next.now = w.now ∧ ∃ f, next.payouts = w.payouts ++
      [⟨.ordinary, a.token, a.recipient, debitedAmount a.token a.amount obs, some f, none⟩] := by
  unfold withdraw at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
  obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
  subst entered
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨prepared, hp, h⟩ := core_bind_ok h
  obtain ⟨_, _, limiter, _, hpeq⟩ := core_withdrawBefore_success d _ prepared a.rootId a.token a.amount hp
  obtain ⟨debit, out, hout, h⟩ := core_bind_pair_ok h
  have hf := core_transferAsset_frame d prepared a.token a.recipient a.amount obs out hout
  have hd := (core_transfer_debit d prepared a.token a.recipient a.amount debit obs out hout).1
  obtain ⟨refunded, hr, h⟩ := core_bind_ok h
  have hrf := core_refund_frame out refunded a.rootId a.token a.amount debit hr
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨f, finalLimiter, _, h⟩ := core_bind_pair_ok h
  have hv := Except.ok.inj h
  rw [← hv]
  refine ⟨hrf.1.trans (hf.1.trans (by rw [hpeq])), f, ?_⟩
  change refunded.payouts ++ [_] = w.payouts ++ [_]
  rw [hrf.2.1, hf.2.1, hpeq, hd]

/-- Both deposit overloads create no physical payout receipt and keep time fixed. -/
theorem core_deposit_frame (d : Deployment) (w : World) (caller : Key)
    (target : DepositTarget) (token : Key) (amount msgValue : Nat)
    (obs : TransferObservation) (next : World)
    (h : deposit d w caller target token amount msgValue obs = .ok next) :
    next.now = w.now ∧ next.payouts = w.payouts := by
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
  have hframe : funded.now = entered.now ∧ funded.payouts = entered.payouts := by
    split at hf
    · obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨custody, _, hf⟩ := core_bind_ok hf
      have hv := Except.ok.inj hf
      rw [← hv]
      exact ⟨rfl, rfl⟩
    · obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨out, hout, hf⟩ := core_bind_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      have hv := Except.ok.inj hf
      rw [← hv]
      have hh := core_callbacks_frame d obs.callbacks { entered with core := core } out hout
      exact ⟨hh.1, hh.2.1⟩
  obtain ⟨u, _, h0⟩ := core_bind_ok h0
  obtain ⟨v, limiter, _, h0⟩ := core_bind_pair_ok h0
  obtain ⟨balance, _, h0⟩ := core_bind_ok h0
  have hv := Except.ok.inj h0
  rw [← hv]
  simpa only [guardExit, heq] using hframe

theorem core_invoke_now (d : Deployment) (w : World) (entry : Entry) (next : World)
    (h : invoke d w entry = .ok next) : next.now = w.now := by
  cases entry with
  | ordinary caller args obs => exact (core_withdraw_frame d w caller args obs next h).1
  | approved caller args sig obs => exact (core_approved_success d w caller args sig obs next h).2.2.2.2
  | funding caller target token amount msgValue obs => exact (core_deposit_frame d w caller target token amount msgValue obs next h).1
  | policy caller action => exact (core_policy_frame d w caller action next h).1
  | environment action =>
    have hv := Except.ok.inj h
    rw [← hv]
    exact (core_environment_frame d w action).1
  | abort error => contradiction

theorem core_invoke_payout_inventory (d : Deployment) (w : World) (entry : Entry)
    (next : World) (h : invoke d w entry = .ok next) :
    (next.payouts = w.payouts ∨ ∃ p, next.payouts = w.payouts ++ [p] ∧
      ((p.kind = .ordinary ∧ p.funding.isSome = true) ∨
       (p.kind = .approved ∧ p.approvedInstruction.isSome = true))) := by
  cases entry with
  | ordinary caller args obs =>
    obtain ⟨_, f, hf⟩ := core_withdraw_frame d w caller args obs next h
    exact Or.inr ⟨_, hf, Or.inl ⟨rfl, rfl⟩⟩
  | approved caller args sig obs =>
    have hf := (core_approved_success d w caller args sig obs next h).2.2.2.1
    exact Or.inr ⟨_, hf, Or.inr ⟨rfl, rfl⟩⟩
  | funding caller target token amount msgValue obs =>
    exact Or.inl (core_deposit_frame d w caller target token amount msgValue obs next h).2
  | policy caller action => exact Or.inl (core_policy_frame d w caller action next h).2.1
  | environment action =>
    have hv := Except.ok.inj h
    rw [← hv]
    exact Or.inl (core_environment_frame d w action).2.2.1
  | abort error => contradiction

theorem measured_deposit_credit : MeasuredDepositCredit := by
  intro d w caller target token amount msgValue obs next h
  dsimp only
  simp only [deposit, allocateDeposit] at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
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
  obtain ⟨id, core, halloc, h0⟩ := core_bind_pair_ok h0
  have ha : allocateDeposit entered.core target = .ok (id, core) := by
    cases target <;> simpa only [allocateDeposit, allocation] using halloc
  obtain ⟨hamount, h0⟩ := core_ensure_ok h0
  obtain ⟨_, h0⟩ := core_ensure_ok h0
  obtain ⟨funded, hf, h0⟩ := core_bind_ok h0
  have hreceipt : 0 < receivedAmount token amount obs ∧ receivedAmount token amount obs ≤ amount ∧
      (if token = 0 then ∃ custody,
        checkedAdd 256 entered.nativeCustody msgValue = .ok custody ∧
        funded = { entered with core := core, nativeCustody := custody }
       else callbacks d obs.callbacks { entered with core := core } = .ok funded) := by
    by_cases ht : token = 0
    · simp only [ht, if_pos] at hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨custody, hc, hf⟩ := core_bind_ok hf
      exact ⟨by simpa [receivedAmount, ht] using hamount, by simp [receivedAmount, ht],
        by simpa only [ht, if_pos] using (show ∃ custody,
          checkedAdd 256 entered.nativeCustody msgValue = .ok custody ∧
          funded = { entered with core := core, nativeCustody := custody } from
          ⟨custody, hc, (Except.ok.inj hf).symm⟩)⟩
    · simp only [ht, if_false] at hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨out, hout, hf⟩ := core_bind_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨hdelta, hf⟩ := core_ensure_ok hf
      have hv := Except.ok.inj hf
      exact ⟨by simp only [receivedAmount, if_neg ht]; omega,
        by simpa only [receivedAmount, if_neg ht] using hdelta.2,
        by simpa only [if_neg ht, ← hv] using hout⟩
  obtain ⟨u, _, h0⟩ := core_bind_ok h0
  obtain ⟨v, limiter, hl, h0⟩ := core_bind_pair_ok h0
  obtain ⟨balance, hb, h0⟩ := core_bind_ok h0
  have heq := (core_checkedAdd_ok hb).1
  exact ⟨hreceipt.1, hreceipt.2.1, entered, id, core, funded, v, limiter,
    he, ha, hreceipt.2.2, hl, by simpa only [heq] using (Except.ok.inj h0).symm⟩

theorem measured_ordinary_settlement : MeasuredOrdinarySettlement := by
  intro d w caller a obs next h
  dsimp only
  unfold withdraw at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨hamount, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨prepared, hp, h⟩ := core_bind_ok h
  obtain ⟨_, _, pinned, hpin, hpeq⟩ := core_withdrawBefore_success d entered prepared a.rootId a.token a.amount hp
  have hflow : prepared.limiter.transient.flowStarted = true := by
    rw [hpeq]
    exact (core_approvedLimiter_frame entered.limiter entered.now entered.quotes d.coreAddress d.coreAddress a.token pinned hpin).2
  obtain ⟨debit, transferred, ht, h⟩ := core_bind_pair_ok h
  obtain ⟨hd, hle, hpos⟩ := core_transfer_debit d prepared a.token a.recipient a.amount debit obs transferred ht
  have htf := core_transferAsset_frame d prepared a.token a.recipient a.amount obs transferred ht
  obtain ⟨refunded, hr, h⟩ := core_bind_ok h
  have hrf := core_refund_frame transferred refunded a.rootId a.token a.amount debit hr
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨funding, limiter, hl, h⟩ := core_bind_pair_ok h
  subst debit
  exact ⟨hpos hamount, hle, entered, prepared, transferred, refunded, funding, limiter,
    he, hp, hflow, ht, htf.2.2.2 hflow, hr, hrf.2.2.2.2, hl, (Except.ok.inj h).symm⟩

theorem measured_approved_settlement : MeasuredApprovedSettlement := by
  intro d w caller q sig obs next h
  dsimp only
  unfold fulfillApprovedWithdrawal at h
  obtain ⟨prepared, hp, h⟩ := core_bind_ok h
  have hc := (core_approvedBeforeTransfer_success d w caller q sig prepared hp).1
  have hposAmount : q.amount > 0 := by
    have hn := hc.2.2.2.2.1
    change q.amount ≠ 0 at hn
    omega
  have hflow := (core_approvedBeforeTransfer_frame d w caller q sig prepared hp).2.2
  obtain ⟨debit, transferred, ht, h⟩ := core_bind_pair_ok h
  obtain ⟨hd, hle, hpos⟩ := core_transfer_debit d prepared q.token q.recipient q.amount debit obs transferred ht
  have htf := core_transferAsset_frame d prepared q.token q.recipient q.amount obs transferred ht
  obtain ⟨refunded, hr, h⟩ := core_bind_ok h
  have hrf := core_refund_frame transferred refunded (w.core.rootAccountIdOf q.account) q.token q.amount debit hr
  subst debit
  exact ⟨hpos hposAmount, hle, prepared, transferred, refunded, hp, hflow, ht,
    htf.2.2.2 hflow, hr, hrf.2.2.2.2, (Except.ok.inj h).symm⟩

/-- Entire group8; gross path receipts, guard, surplus and atomicity. -/
theorem payout_coverage_and_atomicity : PayoutCoverageAndAtomicity := by
  refine ⟨?_, core_nested_guard_reject, core_receiveNative_frame, core_internalFrame_frame,
    ?_, ?_, measured_deposit_credit, measured_ordinary_settlement, measured_approved_settlement⟩
  · intro d w xs entry next _hr _ha h
    exact core_invoke_payout_inventory d w entry next h
  · intro d w entry err h
    exact core_caught_failure w (fun s => invoke d s entry) err h
  · intro d w calls err h
    rw [core_outer_rollback d w calls err h]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem core_beginFlow_reuse (s : Limiter) (now : Nat) (next : Limiter)
    (hflow : s.transient.flowStarted = true) (h : beginFlow s now = .ok next) : next = s := by
  simpa [beginFlow, hflow, Pure.pure, Except.pure] using h.symm

theorem core_price_cached (s : Limiter) (token : Key) (cached : Nat) (fetch : PriceFetch)
    (hc : s.transient.prices token = cached) (hn : cached ≠ 0) :
    price s fetch token = .ok (castWord 128 cached) := by
  simp [price, hc, hn, Pure.pure, Except.pure]

/-- Group4 assembly exposes exactly the sole history-dependent snapshot clause;
    all Core time, cache, reset and rollback clauses are proved here. -/
theorem core_transaction_and_snapshots_of_history
    (historySnapshot : ∀ h xs now s next, RingRepresentation h xs → lastTimestamp xs ≤ now →
      now < width 64 → s.persistent.history = h → s.transient.flowStarted = false →
      beginFlow s now = .ok next →
      next.transient.expired = (expiredReference xs now).1 ∧ next.transient.flowStarted = true ∧
      next.persistent.history.referenceSequence = (expiredReference xs now).2) :
    TransactionAndSnapshots := by
  refine ⟨core_invoke_now, core_beginFlow_reuse, historySnapshot, ?_, core_price_cached,
    ?_, core_caught_failure, core_outer_rollback, core_subroute_rollback⟩
  · intro s fetch token quote next h
    obtain ⟨hp, hs, _⟩ := core_snapshotPrice_frame s fetch token quote next h
    exact ⟨hp, hs⟩
  · intro w
    exact ⟨rfl, rfl, fun _ => rfl⟩

theorem core_route_now (d : Deployment) (calls : List RouteCall) (w next : World)
    (h : route d calls w = .ok next) : next.now = w.now := by
  induction calls generalizing w with
  | nil => exact (Except.ok.inj h).symm ▸ rfl
  | cons c cs ih =>
    simp only [route] at h
    cases hc : invoke d w c.entry with
    | ok out =>
      rw [hc] at h
      exact (ih out h).trans (core_invoke_now d w c.entry out hc)
    | error e =>
      rw [hc] at h
      dsimp only at h
      split at h
      · exact ih w h
      · contradiction

theorem core_nextTransaction_frame (w : World) (now : Nat) (next : World)
    (h : nextTransaction w now = .ok next) :
    w.now ≤ now ∧ next.now = now ∧ next.core = w.core ∧
    next.limiter.persistent = w.limiter.persistent ∧ next.payouts = w.payouts := by
  unfold nextTransaction at h
  obtain ⟨ht, h⟩ := core_ensure_ok h
  have hv := Except.ok.inj h
  rw [← hv]
  exact ⟨ht, rfl, rfl, rfl, rfl⟩

/-- Stronger allocation induction fact: future child-list keys are empty.
    This is derived from initialization, not assumed as target closure. -/
structure CoreAllocation (c : Core) : Prop where
  counter : c.lastAccountId < width 40
  vacant : ∀ id, c.lastAccountId < id → (c.accounts id).rootId = 0
  words : ∀ id, (c.accounts id).rootId < width 40 ∧ (c.accounts id).subaccountSeq < width 16
  children : ∀ root, (c.subaccountsByRoot root).length < width 16 ∧
    ∀ position child, (c.subaccountsByRoot root)[position]? = some child →
      child ≤ c.lastAccountId ∧ (c.accounts child).rootId = root ∧
      (c.accounts child).owner = (c.accounts root).owner ∧
      (c.accounts child).subaccountSeq = position + 1
  roots : ∀ owner, let id := c.rootAccountIdOf owner
    id < width 40 ∧ (id ≠ 0 → (c.accounts id).rootId = id ∧ (c.accounts id).owner = owner)
  futureChildren : ∀ root, c.lastAccountId < root → c.subaccountsByRoot root = []

theorem core_allocation_root_le (c : Core) (hc : CoreAllocation c) (owner : Key) :
    c.rootAccountIdOf owner ≤ c.lastAccountId := by
  by_contra hn
  have hv := hc.vacant (c.rootAccountIdOf owner) (by omega)
  have hne : c.rootAccountIdOf owner ≠ 0 := by omega
  have hr := (hc.roots owner).2 hne
  omega

theorem core_allocation_empty (owner fee : Key) :
    CoreAllocation ({ owner := owner, feeCollector := fee } : Core) := by
  constructor
  · norm_num [width]
  · intro id _; rfl
  · intro id; norm_num [width]
  · intro root; constructor
    · norm_num [width]
    · intro position child h; simp at h
  · intro owner; simp [width]
  · intro root _; rfl

/-- Checked ROOT allocation preserves all prior records/list metadata. -/
theorem core_registerRoot_allocation (c : Core) (owner : Key) (id : Nat) (next : Core)
    (hc : CoreAllocation c) (h : registerAccount c owner 0 0 = .ok (id, next)) :
    CoreAllocation next := by
  obtain ⟨hid, hwidth, heq⟩ := core_registerAccount_success c owner 0 0 id next h
  subst next
  have hidpos : 0 < id := by omega
  have hidold : c.lastAccountId < id := by omega
  constructor
  · exact hwidth
  · intro i hi
    dsimp only at hi
    have hne : i ≠ id := by omega
    simp only [if_neg hne]
    exact hc.vacant i (by omega)
  · intro i
    by_cases hi : i = id
    · simp only [hi, if_true]
      exact ⟨hwidth, by norm_num [width]⟩
    · simpa only [if_neg hi] using hc.words i
  · intro root
    refine ⟨(hc.children root).1, ?_⟩
    intro position child hchild
    obtain ⟨hcl, hcr, hco, hcs⟩ := (hc.children root).2 position child hchild
    have hcn : child ≠ id := by omega
    have hrn : root ≠ id := by
      intro hr
      have hempty := hc.futureChildren root (hr ▸ hidold)
      simp [hempty] at hchild
    simp only [if_neg hcn, if_neg hrn]
    exact ⟨by omega, hcr, hco, hcs⟩
  · intro key
    have hrootle := core_allocation_root_le c hc key
    have hneq : c.rootAccountIdOf key ≠ id := by omega
    simpa only [if_neg hneq] using hc.roots key
  · intro root hfuture
    dsimp only at hfuture
    exact hc.futureChildren root (by omega)

/-- Source ensureRoot updates the canonical map only on actual checked allocation. -/
theorem core_ensureRoot_allocation (c : Core) (owner : Key) (id : Nat) (next : Core)
    (hc : CoreAllocation c) (h : ensureRoot c owner = .ok (id, next)) :
    CoreAllocation next := by
  unfold ensureRoot at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  dsimp only at h
  split at h
  · have hv := Except.ok.inj h
    have he := congrArg Prod.snd hv
    simp only [Prod.snd] at he
    rw [← he]
    exact hc
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨n, allocated, ha, h⟩ := core_bind_pair_ok h
    have halloc := core_registerRoot_allocation c owner n allocated hc ha
    obtain ⟨hn, hnwidth, heq⟩ := core_registerAccount_success c owner 0 0 n allocated ha
    have hv := Except.ok.inj h
    have hnext := congrArg Prod.snd hv
    simp only [Prod.snd] at hnext
    rw [← hnext]
    constructor
    · exact halloc.counter
    · exact halloc.vacant
    · exact halloc.words
    · exact halloc.children
    · intro key
      by_cases hk : key = owner
      · subst key
        simp only [update, if_true]
        rw [heq]
        exact ⟨hnwidth, fun _ => ⟨by simp, by simp⟩⟩
      · simpa only [update, if_neg hk] using halloc.roots key
    · exact halloc.futureChildren

/-- Both CHILD source paths share this checked append and metadata induction. -/
theorem core_createSubaccount_allocation (c : Core) (root id : Nat) (next : Core)
    (hc : CoreAllocation c) (h : createSubaccount c root = .ok (id, next)) :
    CoreAllocation next := by
  unfold createSubaccount at h
  obtain ⟨u, hroot, h⟩ := core_bind_ok h
  unfold requireRoot at hroot
  obtain ⟨hrnz, hroot⟩ := core_ensure_ok hroot
  have hr := core_ensure_success hroot
  have hrle : root ≤ c.lastAccountId := by
    by_contra hle
    have hv := hc.vacant root (by omega)
    exact hrnz hv
  have hrpos : root ≠ 0 := by omega
  obtain ⟨hseq, h⟩ := core_ensure_ok h
  have hseqwidth : (c.subaccountsByRoot root).length + 1 < width 16 := by
    have hw : 0 < width 16 := by norm_num [width]
    unfold maxWord at hseq
    omega
  obtain ⟨n, allocated, ha, h⟩ := core_bind_pair_ok h
  obtain ⟨hn, hnwidth, heq⟩ := core_registerAccount_success c (c.accounts root).owner root
    ((c.subaccountsByRoot root).length + 1) n allocated ha
  have hv := Except.ok.inj h
  have hnext := congrArg Prod.snd hv
  simp only [Prod.snd] at hnext
  rw [← hnext, heq]
  have hnold : c.lastAccountId < n := by omega
  have hrn : root ≠ n := by omega
  have hwordroot : root < width 40 := by simpa [hr] using (hc.words root).1
  constructor
  · exact hnwidth
  · intro i hi
    dsimp only at hi
    have hin : i ≠ n := by omega
    simpa only [if_neg hin] using hc.vacant i (by omega)
  · intro i
    by_cases hi : i = n
    · simp only [hi, if_true, if_neg hrpos]
      exact ⟨hwordroot, hseqwidth⟩
    · simpa only [if_neg hi] using hc.words i
  · intro key
    by_cases hk : key = root
    · subst key
      simp only [if_true, List.length_append, List.length_singleton]
      refine ⟨hseqwidth, ?_⟩
      intro position child hp
      by_cases hpos : position < (c.subaccountsByRoot root).length
      · rw [List.getElem?_append_left hpos] at hp
        obtain ⟨hcl, hcr, hco, hcs⟩ := (hc.children root).2 position child hp
        have hcn : child ≠ n := by omega
        simp only [if_neg hcn, if_neg hrn]
        exact ⟨by omega, hcr, hco, hcs⟩
      · rw [List.getElem?_append_right (by omega)] at hp
        have hl : position < (c.subaccountsByRoot root).length + 1 := by
          obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hp
          simp only [List.length_singleton] at hh
          omega
        have heqpos : position = (c.subaccountsByRoot root).length := by omega
        simp only [heqpos, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hp
        subst child
        simp only [if_true, if_neg hrpos, if_neg hrn]
        exact ⟨Nat.le_refl n, trivial, trivial, by omega⟩
    · simp only [if_neg hk]
      refine ⟨(hc.children key).1, ?_⟩
      intro position child hp
      obtain ⟨hcl, hcr, hco, hcs⟩ := (hc.children key).2 position child hp
      have hcn : child ≠ n := by omega
      have hkn : key ≠ n := by
        intro hkn
        have hempty := hc.futureChildren key (hkn ▸ hnold)
        simp [hempty] at hp
      simp only [if_neg hcn, if_neg hkn]
      exact ⟨by omega, hcr, hco, hcs⟩
  · intro key
    have hrootle := core_allocation_root_le c hc key
    have hneq : c.rootAccountIdOf key ≠ n := by omega
    simpa only [if_neg hneq] using hc.roots key
  · intro key hfuture
    dsimp only at hfuture
    have hk : key ≠ root := by omega
    simp only [if_neg hk]
    exact hc.futureChildren key (by omega)

theorem core_ranges_from_allocation (c : Core) (ha : CoreAllocation c)
    (he : c.epoch < width 64)
    (hn : ∀ k, c.approvedNonces k < width 256 ∧ (c.tokens k).decimals ≤ 77)
    (hb : ∀ id k, c.balances id k < width 256 ∧ c.reserves id k < width 256)
    (hg : ∀ id k, (c.grants id k).permissions < width 32 ∧ (c.grants id k).expiry < width 64) :
    CoreRanges c :=
  ⟨ha.counter, he, ha.vacant, hn, hb, ha.words, ha.children, hg, ha.roots⟩

theorem core_ranges_frame (c next : Core) (hc : CoreRanges c)
    (hl : next.lastAccountId = c.lastAccountId) (he : next.epoch = c.epoch)
    (hn : next.approvedNonces = c.approvedNonces) (ht : next.tokens = c.tokens)
    (hb : next.balances = c.balances) (hr : next.reserves = c.reserves)
    (hg : next.grants = c.grants) (ha : next.accounts = c.accounts)
    (hs : next.subaccountsByRoot = c.subaccountsByRoot)
    (hm : next.rootAccountIdOf = c.rootAccountIdOf) : CoreRanges next := by
  simpa only [CoreRanges, hl, he, hn, ht, hb, hr, hg, ha, hs, hm] using hc

theorem core_ensureRoot_other_fields (c : Core) (owner : Key) (id : Nat) (next : Core)
    (h : ensureRoot c owner = .ok (id, next)) :
    next.tokens = c.tokens ∧ next.reserves = c.reserves ∧ next.grants = c.grants := by
  unfold ensureRoot at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  dsimp only at h
  split at h
  · have hv := Except.ok.inj h
    have he := congrArg Prod.snd hv
    simp only [Prod.snd] at he
    rw [← he]
    exact ⟨rfl, rfl, rfl⟩
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨n, allocated, ha, h⟩ := core_bind_pair_ok h
    obtain ⟨_, _, heq⟩ := core_registerAccount_success c owner 0 0 n allocated ha
    have hv := Except.ok.inj h
    have he := congrArg Prod.snd hv
    simp only [Prod.snd] at he
    rw [← he, heq]
    exact ⟨rfl, rfl, rfl⟩

theorem core_ensureRoot_ranges (c : Core) (owner : Key) (id : Nat) (next : Core)
    (hr : CoreRanges c) (ha : CoreAllocation c)
    (h : ensureRoot c owner = .ok (id, next)) : CoreRanges next := by
  have ha' := core_ensureRoot_allocation c owner id next ha h
  obtain ⟨hn, he, _, hb⟩ := core_ensureRoot_stable c owner id next h
  obtain ⟨ht, hres, hg⟩ := core_ensureRoot_other_fields c owner id next h
  rcases hr with ⟨_, hEpoch, _, hNonces, hBalances, _, _, hGrants, _⟩
  exact core_ranges_from_allocation next ha'
    (by simpa only [he] using hEpoch)
    (by simpa only [hn, ht] using hNonces)
    (by simpa only [hb, hres] using hBalances)
    (by simpa only [hg] using hGrants)

theorem core_empty_ranges (owner fee : Key) :
    CoreRanges ({ owner := owner, feeCollector := fee } : Core) := by
  apply core_ranges_from_allocation _ (core_allocation_empty owner fee)
  · norm_num [width]
  · intro k; norm_num [width]
  · intro id k; norm_num [width]
  · intro id k; norm_num [width]

/-- Actual initialization, registry installation and binding; no range premise. -/
theorem core_freshBoundPair_ranges (d : Deployment) (now capacity rate : Nat)
    (owner fee registry : Key) (roles : Key → Roles) (w : World)
    (h : freshBoundPair d now capacity rate owner fee registry roles = .ok w) : CoreRanges w.core := by
  unfold freshBoundPair at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨limiter, _, h⟩ := core_bind_ok h
  obtain ⟨id, core, hroot, h⟩ := core_bind_pair_ok h
  have hr := core_ensureRoot_ranges _ fee id core (core_empty_ranges owner fee)
    (core_allocation_empty owner fee) hroot
  obtain ⟨registered, hregistered, h⟩ := core_bind_ok h
  simp only [policyAction] at hregistered
  obtain ⟨_, hregistered⟩ := core_ensure_ok hregistered
  obtain ⟨_, hregistered⟩ := core_ensure_ok hregistered
  obtain ⟨_, hregistered⟩ := core_ensure_ok hregistered
  have heq := Except.ok.inj hregistered
  subst registered
  simp only [policyAction] at h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  have hv := Except.ok.inj h
  rw [← hv]
  exact core_ranges_frame core _ hr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem core_createSubaccount_other_fields (c : Core) (root id : Nat) (next : Core)
    (h : createSubaccount c root = .ok (id, next)) :
    next.tokens = c.tokens ∧ next.reserves = c.reserves ∧ next.grants = c.grants := by
  unfold createSubaccount at h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨n, allocated, ha, h⟩ := core_bind_pair_ok h
  obtain ⟨_, _, heq⟩ := core_registerAccount_success c (c.accounts root).owner root
    ((c.subaccountsByRoot root).length + 1) n allocated ha
  have hv := Except.ok.inj h
  have he := congrArg Prod.snd hv
  simp only [Prod.snd] at he
  rw [← he, heq]
  exact ⟨rfl, rfl, rfl⟩

theorem core_createSubaccount_ranges (c : Core) (root id : Nat) (next : Core)
    (hr : CoreRanges c) (ha : CoreAllocation c)
    (h : createSubaccount c root = .ok (id, next)) : CoreRanges next := by
  have ha' := core_createSubaccount_allocation c root id next ha h
  obtain ⟨hn, he, _, hb⟩ := core_createSubaccount_stable c root id next h
  obtain ⟨ht, hres, hg⟩ := core_createSubaccount_other_fields c root id next h
  rcases hr with ⟨_, hEpoch, _, hNonces, hBalances, _, _, hGrants, _⟩
  exact core_ranges_from_allocation next ha'
    (by simpa only [he] using hEpoch)
    (by simpa only [hn, ht] using hNonces)
    (by simpa only [hb, hres] using hBalances)
    (by simpa only [hg] using hGrants)

/-- Numeric admissibility supplies only the excluded record widths, not a
    funding or allocation invariant. No target closure is assumed. -/
theorem core_applyInternalFrame_ranges (w : World) (f : InternalFrame)
    (hc : CoreRanges w.core) (hf : FrameAdmissible f) : CoreRanges (applyInternalFrame w f).core := by
  rcases hc with ⟨hcounter, hepoch, hvacant, hnt, hbr, hwords, hchildren, hgrants, hroots⟩
  rcases hf with ⟨hbalances, hgrant⟩
  exact ⟨hcounter, hepoch, hvacant, hnt, hbalances, hwords, hchildren, hgrant, hroots⟩

theorem core_endTransaction_ranges (w : World) (hc : CoreRanges w.core) :
    CoreRanges (endTransaction w).core := hc

theorem core_nextTransaction_ranges (w : World) (now : Nat) (next : World)
    (hc : CoreRanges w.core) (h : nextTransaction w now = .ok next) : CoreRanges next.core := by
  rw [(core_nextTransaction_frame w now next h).2.2.1]
  exact hc

#print axioms approved_authority_and_replay
#print axioms payout_coverage_and_atomicity
#print axioms core_transaction_and_snapshots_of_history
#print axioms core_freshBoundPair_ranges
#print axioms core_registerRoot_allocation
#print axioms core_createSubaccount_allocation
#print axioms core_ensureRoot_ranges
#print axioms core_createSubaccount_ranges
#print axioms core_applyInternalFrame_ranges

/-- Strong simultaneous induction state; derived from concrete initialization. -/
structure CoreSafe (c : Core) : Prop where
  allocation : CoreAllocation c
  epoch : c.epoch < width 64
  nonceToken : ∀ k, c.approvedNonces k < width 256 ∧ (c.tokens k).decimals ≤ 77
  balances : ∀ id k, c.balances id k < width 256 ∧ c.reserves id k < width 256
  grants : ∀ id k, (c.grants id k).permissions < width 32 ∧ (c.grants id k).expiry < width 64

theorem core_safe_ranges {c : Core} (hc : CoreSafe c) : CoreRanges c :=
  core_ranges_from_allocation c hc.allocation hc.epoch hc.nonceToken hc.balances hc.grants

theorem core_safe_of_ranges {c : Core} (hc : CoreRanges c) (ha : CoreAllocation c) : CoreSafe c :=
  ⟨ha, hc.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.2.2.1⟩

theorem core_safe_guard (d : Deployment) (w : World) (hc : CoreSafe w.core) :
    CoreSafe ({ w.core with guardWord := d.coreAddress.toNat }) := by
  exact { hc with allocation := { hc.allocation with } }

theorem core_safe_guardExit (d : Deployment) (w : World) (hc : CoreSafe w.core) :
    CoreSafe (guardExit d w).core := by
  exact { hc with allocation := { hc.allocation with } }

theorem core_safe_ensureRoot (c : Core) (owner : Key) (id : Nat) (next : Core)
    (hc : CoreSafe c) (h : ensureRoot c owner = .ok (id,next)) : CoreSafe next :=
  core_safe_of_ranges (core_ensureRoot_ranges c owner id next (core_safe_ranges hc) hc.allocation h)
    (core_ensureRoot_allocation c owner id next hc.allocation h)

theorem core_safe_child (c : Core) (root id : Nat) (next : Core)
    (hc : CoreSafe c) (h : createSubaccount c root = .ok (id,next)) : CoreSafe next :=
  core_safe_of_ranges (core_createSubaccount_ranges c root id next (core_safe_ranges hc) hc.allocation h)
    (core_createSubaccount_allocation c root id next hc.allocation h)

theorem core_safe_internal (w : World) (f : InternalFrame) (hc : CoreSafe w.core)
    (hf : FrameAdmissible f) : CoreSafe (applyInternalFrame w f).core := by
  exact { hc with allocation := { hc.allocation with }, balances := hf.1, grants := hf.2 }

theorem core_safe_configureToken_shape (d : Deployment) (w : World) (caller token : Key)
    (enabled : Bool) (metadata : Checked Nat) (next : World)
    (hc : CoreSafe w.core) (h : policyAction d w caller (.configureToken token enabled metadata) = .ok next) :
    ∃ config, config.decimals ≤ 77 ∧ next = { w with core := { w.core with tokens := update w.core.tokens token config } } := by
  simp only [policyAction] at h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  try dsimp only at h
  have h0 : ((if enabled then
      ((if token = 0 then pure 18 else metadata) >>= fun dec =>
        ensure (dec ≤ 77) .config >>= fun _ =>
          ((if (w.core.tokens token).seen then ensure ((w.core.tokens token).decimals = dec) .config
            else pure ()) >>= fun _ =>
            requireLimiter w >>= fun _ =>
              price w.limiter w.quotes token >>= fun _ => pure (TokenConfig.mk dec true true)))
      else pure (TokenConfig.mk (w.core.tokens token).decimals false (w.core.tokens token).seen)) >>=
      fun config => pure ({ w with core := { w.core with tokens := update w.core.tokens token config } } : World)) = .ok next := by
    by_cases ht : token = 0
    · subst token
      cases he : enabled <;> cases hs : (w.core.tokens 0).seen <;>
        simpa [he, hs, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
          Pure.pure, Except.pure] using h
    · cases he : enabled <;> cases hs : (w.core.tokens token).seen <;>
        simpa [he, hs, ht, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
          Pure.pure, Except.pure] using h
  obtain ⟨config, hconfig, h0⟩ := core_bind_ok h0
  refine ⟨config, ?_, (Except.ok.inj h0).symm⟩
  cases he : enabled with
  | false =>
    simp only [he, Bool.false_eq_true, if_false] at hconfig
    have hv := Except.ok.inj hconfig
    rw [← hv]
    exact (hc.nonceToken token).2
  | true =>
    simp only [he, if_true] at hconfig
    obtain ⟨dec, _, hconfig⟩ := core_bind_ok hconfig
    obtain ⟨hdec, hconfig⟩ := core_ensure_ok hconfig
    obtain ⟨u, _, hconfig⟩ := core_bind_ok hconfig
    obtain ⟨u, _, hconfig⟩ := core_bind_ok hconfig
    obtain ⟨q, _, hconfig⟩ := core_bind_ok hconfig
    have hv := Except.ok.inj hconfig
    rw [← hv]
    exact hdec


theorem core_safe_policy (d : Deployment) (w : World) (caller : Key)
    (a : PolicyAction) (next : World) (hc : CoreSafe w.core)
    (h : policyAction d w caller a = .ok next) : CoreSafe next.core := by
  cases a with
  | setFeeCollector owner =>
    unfold policyAction at h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨id, core, hp, h⟩ := core_bind_pair_ok h
    have hs := core_safe_ensureRoot w.core owner id core hc hp
    rw [← Except.ok.inj h]
    exact { hs with allocation := { hs.allocation with } }
  | setRegistry registry =>
    unfold policyAction at h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    rw [← Except.ok.inj h]
    exact { hc with allocation := { hc.allocation with } }
  | pause paused =>
    cases paused with
    | false =>
      simp only [policyAction, Bool.false_eq_true, if_false] at h
      obtain ⟨_, h⟩ := core_ensure_ok h
      obtain ⟨_, h⟩ := core_ensure_ok h
      rw [← Except.ok.inj h]
      exact { hc with allocation := { hc.allocation with } }
    | true =>
      simp only [policyAction, if_true] at h
      obtain ⟨u, _, h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]
      exact { hc with allocation := { hc.allocation with } }
  | rotateAuthority authority =>
    unfold policyAction at h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨n, hn, h⟩ := core_bind_ok h
    have hnw := (core_checkedAdd_ok hn).2
    rw [← Except.ok.inj h]
    exact { hc with allocation := { hc.allocation with }, epoch := hnw }
  | freeze frozen =>
    cases frozen <;> simp only [policyAction, Bool.false_eq_true, if_false, if_true] at h
    all_goals
      obtain ⟨u, _, h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]
      exact { hc with allocation := { hc.allocation with } }
  | freezeToken token frozen =>
    cases frozen <;> simp only [policyAction, Bool.false_eq_true, if_false, if_true] at h
    all_goals
      obtain ⟨u, _, h⟩ := core_bind_ok h
      rw [← Except.ok.inj h]
      exact { hc with allocation := { hc.allocation with } }
  | invalidateNonce account n =>
    unfold policyAction at h
    obtain ⟨hw, h⟩ := core_ensure_ok h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    rw [← Except.ok.inj h]
    refine { hc with allocation := { hc.allocation with }, nonceToken := ?_ }
    intro k
    refine ⟨?_, (hc.nonceToken k).2⟩
    by_cases hk : k = account
    · simpa only [update, if_pos hk] using hw
    · simpa only [update, if_neg hk] using (hc.nonceToken k).1
  | bindLimiter limiter =>
    unfold policyAction at h
    obtain ⟨u, _, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    rw [← Except.ok.inj h]
    exact { hc with allocation := { hc.allocation with } }
  | configureDrip capacity rate =>
    unfold policyAction at h
    obtain ⟨l, _, h⟩ := core_bind_ok h
    rw [← Except.ok.inj h]
    exact hc
  | configureSource token source =>
    unfold policyAction at h
    obtain ⟨l, _, h⟩ := core_bind_ok h
    rw [← Except.ok.inj h]
    exact hc
  | configureToken token enabled metadata =>
    obtain ⟨config, hd, hv⟩ := core_safe_configureToken_shape d w caller token enabled metadata next hc h
    rw [hv]
    refine { hc with allocation := { hc.allocation with }, nonceToken := ?_ }
    intro k
    refine ⟨(hc.nonceToken k).1, ?_⟩
    by_cases hk : k = token
    · simpa only [update, if_pos hk] using hd
    · simpa only [update, if_neg hk] using (hc.nonceToken k).2
  | receiveNative amount =>
    unfold policyAction at h
    obtain ⟨n, _, h⟩ := core_bind_ok h
    rw [← Except.ok.inj h]
    exact hc
  | nestedGuarded =>
    unfold policyAction at h
    obtain ⟨entered, _, h⟩ := core_bind_ok h
    rw [← Except.ok.inj h]
    exact hc
  | observe =>
    rw [← Except.ok.inj h]
    exact hc

theorem core_safe_environment (d : Deployment) (w : World) (a : EnvironmentAction)
    (hc : CoreSafe w.core) (ha : EnvironmentAdmissible a) : CoreSafe (environmentAction d w a).core := by
  cases a with
  | publish source quote => exact hc
  | registryResponse registry roles => exact hc
  | ensureRootAccount owner =>
    simp only [environmentAction]
    cases h : ensureRoot w.core owner with
    | error e => exact hc
    | ok p =>
      rcases p with ⟨id, core⟩
      exact core_safe_ensureRoot w.core owner id core hc h
  | createChild owner =>
    simp only [environmentAction]
    split
    · rename_i next h
      obtain ⟨entered, he, h⟩ := core_bind_ok h
      obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
      subst entered
      obtain ⟨root, core, hp, h⟩ := core_bind_pair_ok h
      have hs := core_safe_ensureRoot _ owner root core (core_safe_guard d w hc) hp
      obtain ⟨id, childCore, hp, h⟩ := core_bind_pair_ok h
      have hs' := core_safe_child core root id childCore hs hp
      rw [← Except.ok.inj h]
      exact core_safe_guardExit d _ hs'
    · exact hc
  | internalFrame frame =>
    simp only [environmentAction]
    split
    · rename_i next h
      have h0 : ((if frame.protocolActive then ensure (w.core.paused = false) .paused
          else pure ()) >>= fun _ =>
        ((if frame.guarded then guardEnter d w else pure w) >>= fun entered =>
          ((match frame.registerRoot with
            | none => pure entered
            | some owner => ensureRoot entered.core owner >>= fun p =>
                pure ({ entered with core := p.2 } : World)) >>= fun registered =>
              pure (if frame.guarded then guardExit d (applyInternalFrame registered frame)
                else applyInternalFrame registered frame)))) = .ok next := by
        cases hp : frame.protocolActive <;> cases hg : frame.guarded <;>
          cases hr : frame.registerRoot <;>
          simpa [hp, hg, hr, Bind.bind, core_except_bind_assoc, core_except_ok_bind,
            Pure.pure, Except.pure] using h
      obtain ⟨u, _, h0⟩ := core_bind_ok h0
      obtain ⟨entered, he, h0⟩ := core_bind_ok h0
      have hs : CoreSafe entered.core := by
        split at he
        · rw [(core_guardEnter_success d w entered he).2]
          exact core_safe_guard d w hc
        · rw [← Except.ok.inj he]
          exact hc
      obtain ⟨registered, hr, h0⟩ := core_bind_ok h0
      have hs' : CoreSafe registered.core := by
        cases ho : frame.registerRoot with
        | none =>
          simp only [ho] at hr
          rw [← Except.ok.inj hr]
          exact hs
        | some owner =>
          simp only [ho] at hr
          obtain ⟨id, core, hp, hr⟩ := core_bind_pair_ok hr
          rw [← Except.ok.inj hr]
          exact core_safe_ensureRoot entered.core owner id core hs hp
      rw [← Except.ok.inj h0]
      split
      · exact core_safe_guardExit d _ (core_safe_internal registered frame hs' ha)
      · exact core_safe_internal registered frame hs' ha
    · exact hc

theorem core_safe_environment_fold (d : Deployment) (as : List EnvironmentAction) (w : World)
    (hc : CoreSafe w.core) (ha : ∀ a ∈ as, EnvironmentAdmissible a) :
    CoreSafe (as.foldl (environmentAction d) w).core := by
  induction as generalizing w with
  | nil => exact hc
  | cons a as ih =>
    exact ih _ (core_safe_environment d w a hc (ha a (by simp)))
      (fun x hx => ha x (by simp [hx]))

theorem core_safe_callbacks (d : Deployment) (cs : List Callback) (w next : World)
    (hc : CoreSafe w.core) (ha : ∀ cb ∈ cs, ∀ a ∈ cb.environmentBefore, EnvironmentAdmissible a)
    (h : callbacks d cs w = .ok next) : CoreSafe next.core := by
  induction cs generalizing w with
  | nil => rw [← Except.ok.inj h]; exact hc
  | cons c cs ih =>
    have hs := core_safe_environment_fold d c.environmentBefore w hc (ha c (by simp))
    have htail : ∀ cb ∈ cs, ∀ a ∈ cb.environmentBefore, EnvironmentAdmissible a :=
      fun cb hb => ha cb (by simp [hb])
    simp only [callbacks] at h
    cases hp : policyAction d (c.environmentBefore.foldl (environmentAction d) w) c.caller c.action with
    | ok out =>
      rw [hp] at h
      exact ih out (core_safe_policy d _ c.caller c.action out hs hp) htail h
    | error e =>
      rw [hp] at h
      dsimp only at h
      split at h
      · exact ih _ hs htail h
      · contradiction

theorem core_safe_transfer (d : Deployment) (w : World) (token recipient : Key)
    (amount : Nat) {debited : Nat} (obs : TransferObservation) (next : World) (hc : CoreSafe w.core)
    (ha : CallbacksAdmissible obs)
    (h : transferAsset d w token recipient amount obs = .ok (debited, next)) : CoreSafe next.core := by
  unfold transferAsset at h
  split at h
  · obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨out, hout, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := congrArg Prod.snd (Except.ok.inj h)
    dsimp only at hv
    rw [← hv]
    exact core_safe_callbacks d obs.callbacks
      { w with nativeCustody := w.nativeCustody - amount } out hc ha hout
  · obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨out, hout, h⟩ := core_bind_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    obtain ⟨_, h⟩ := core_ensure_ok h
    have hv := congrArg Prod.snd (Except.ok.inj h)
    dsimp only at hv
    rw [← hv]
    exact core_safe_callbacks d obs.callbacks w out hc ha hout

theorem core_safe_balance (c : Core) (id : Nat) (token : Key) (v : Nat)
    (hc : CoreSafe c) (hv : v < width 256) :
    CoreSafe { c with balances := updateBalance c.balances id token v } := by
  refine { hc with allocation := { hc.allocation with }, balances := ?_ }
  intro i k
  refine ⟨?_, (hc.balances i k).2⟩
  by_cases hi : i = id ∧ k = token
  · simpa only [updateBalance, if_pos hi] using hv
  · simpa only [updateBalance, if_neg hi] using (hc.balances i k).1

theorem core_safe_refund (w next : World) (id : Nat) (token : Key) (amount debit : Nat)
    (hc : CoreSafe w.core) (h : refundAsset w id token amount debit = .ok next) : CoreSafe next.core := by
  unfold refundAsset at h
  split at h
  · obtain ⟨balance, hb, h⟩ := core_bind_ok h
    rw [← Except.ok.inj h]
    exact core_safe_balance w.core id token balance hc (core_checkedAdd_ok hb).2
  · rw [← Except.ok.inj h]
    exact hc

theorem core_safe_withdrawBefore (d : Deployment) (w next : World)
    (id : Nat) (token : Key) (amount : Nat) (hc : CoreSafe w.core)
    (h : withdrawBeforeTransfer d w id token amount = .ok next) : CoreSafe next.core := by
  obtain ⟨_, _, limiter, _, heq⟩ := core_withdrawBefore_success d w next id token amount h
  rw [heq]
  exact core_safe_balance w.core id token _ hc
    (lt_of_le_of_lt (Nat.sub_le _ _) (hc.balances id token).1)

theorem core_safe_nonce (c : Core) (account : Key) (n : Nat) (hc : CoreSafe c)
    (hn : n < width 256) : CoreSafe { c with approvedNonces := update c.approvedNonces account n } := by
  refine { hc with allocation := { hc.allocation with }, nonceToken := ?_ }
  intro k
  refine ⟨?_, (hc.nonceToken k).2⟩
  by_cases hk : k = account
  · simpa only [update, if_pos hk] using hn
  · simpa only [update, if_neg hk] using (hc.nonceToken k).1

theorem core_safe_withdraw (d : Deployment) (w : World) (caller : Key)
    (a : OrdinaryArgs) (obs : TransferObservation) (next : World) (hc : CoreSafe w.core)
    (ha : CallbacksAdmissible obs) (h : withdraw d w caller a obs = .ok next) : CoreSafe next.core := by
  unfold withdraw at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
  obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
  have hs : CoreSafe entered.core := by rw [heq]; exact core_safe_guard d w hc
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨prepared, hp, h⟩ := core_bind_ok h
  obtain ⟨debit, out, hout, h⟩ := core_bind_pair_ok h
  obtain ⟨refunded, hr, h⟩ := core_bind_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨f, limiter, _, h⟩ := core_bind_pair_ok h
  have hpSafe := core_safe_withdrawBefore d entered prepared a.rootId a.token a.amount hs hp
  have htSafe := core_safe_transfer d prepared a.token a.recipient a.amount obs out hpSafe ha hout
  have hrSafe := core_safe_refund out refunded a.rootId a.token a.amount debit htSafe hr
  rw [← Except.ok.inj h]
  exact core_safe_guardExit d _ hrSafe

theorem core_safe_approvedBefore (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (next : World) (hc : CoreSafe w.core)
    (h : approvedBeforeTransfer d w caller q sig = .ok next) : CoreSafe next.core := by
  unfold approvedBeforeTransfer at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨entered, he, h⟩ := core_bind_ok h
  obtain ⟨_, _, heq⟩ := core_activeGuardEnter_success d w entered he
  have hs : CoreSafe entered.core := by rw [heq]; exact core_safe_guard d w hc
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨n, hn, h⟩ := core_bind_ok h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨u, _, h⟩ := core_bind_ok h
  obtain ⟨l, _, h⟩ := core_bind_ok h
  have hs' := core_safe_nonce entered.core q.account n hs (core_checkedAdd_ok hn).2
  have hw : entered.core.balances (entered.core.rootAccountIdOf q.account) q.token - q.amount < width 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (hs.balances _ _).1
  have hs'' := core_safe_balance _ (entered.core.rootAccountIdOf q.account) q.token _ hs' hw
  rw [← Except.ok.inj h]
  exact hs''

theorem core_safe_approved (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (obs : TransferObservation)
    (next : World) (hc : CoreSafe w.core) (ha : CallbacksAdmissible obs)
    (h : fulfillApprovedWithdrawal d w caller q sig obs = .ok next) : CoreSafe next.core := by
  unfold fulfillApprovedWithdrawal at h
  obtain ⟨prepared, hp, h⟩ := core_bind_ok h
  obtain ⟨debit, out, hout, h⟩ := core_bind_pair_ok h
  obtain ⟨refunded, hr, h⟩ := core_bind_ok h
  have hs := core_safe_approvedBefore d w caller q sig prepared hc hp
  have hs' := core_safe_transfer d prepared q.token q.recipient q.amount obs out hs ha hout
  have hs'' := core_safe_refund out refunded (w.core.rootAccountIdOf q.account) q.token q.amount debit hs' hr
  rw [← Except.ok.inj h]
  exact core_safe_guardExit d _ hs''

theorem core_safe_deposit (d : Deployment) (w : World) (caller : Key)
    (target : DepositTarget) (token : Key) (amount msgValue : Nat)
    (obs : TransferObservation) (next : World)
    (hc : CoreSafe w.core) (ha : CallbacksAdmissible obs)
    (h : deposit d w caller target token amount msgValue obs = .ok next) :
    CoreSafe next.core := by
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
  obtain ⟨id, core, hp, h0⟩ := core_bind_pair_ok h0
  have hs : CoreSafe entered.core := by rw [heq]; exact core_safe_guard d w hc
  have halloc : CoreSafe core := by
    cases target with
    | owner owner => exact core_safe_ensureRoot entered.core owner id core hs hp
    | rootId root =>
      dsimp only [allocation] at hp
      obtain ⟨_, hp⟩ := core_ensure_ok hp
      obtain ⟨u, _, hp⟩ := core_bind_ok hp
      have hv := congrArg Prod.snd (Except.ok.inj hp)
      simp only [Prod.snd] at hv
      rw [← hv]
      exact hs
  obtain ⟨_, h0⟩ := core_ensure_ok h0
  obtain ⟨_, h0⟩ := core_ensure_ok h0
  obtain ⟨funded, hf, h0⟩ := core_bind_ok h0
  have hframe : CoreSafe funded.core := by
    split at hf
    · obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨custody, _, hf⟩ := core_bind_ok hf
      have hv := Except.ok.inj hf
      rw [← hv]
      exact halloc
    · obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨out, hout, hf⟩ := core_bind_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      obtain ⟨_, hf⟩ := core_ensure_ok hf
      have hv := Except.ok.inj hf
      rw [← hv]
      exact core_safe_callbacks d obs.callbacks { entered with core := core } out halloc ha hout
  obtain ⟨u, _, h0⟩ := core_bind_ok h0
  obtain ⟨v, limiter, _, h0⟩ := core_bind_pair_ok h0
  obtain ⟨balance, hbalance, h0⟩ := core_bind_ok h0
  have hv := Except.ok.inj h0
  rw [← hv]
  exact core_safe_guardExit d _ (core_safe_balance funded.core id token balance hframe (core_checkedAdd_ok hbalance).2)

theorem core_safe_fresh (d : Deployment) (now capacity rate : Nat)
    (owner fee registry : Key) (roles : Key → Roles) (w : World)
    (h : freshBoundPair d now capacity rate owner fee registry roles = .ok w) : CoreSafe w.core := by
  unfold freshBoundPair at h
  obtain ⟨_, h⟩ := core_ensure_ok h
  obtain ⟨limiter, _, h⟩ := core_bind_ok h
  obtain ⟨id, core, hp, h⟩ := core_bind_pair_ok h
  have hempty := core_safe_of_ranges (core_empty_ranges owner fee) (core_allocation_empty owner fee)
  have hs := core_safe_ensureRoot _ fee id core hempty hp
  obtain ⟨registered, hregistered, h⟩ := core_bind_ok h
  have hs' := core_safe_policy d _ owner (.setRegistry registry) registered hs hregistered
  exact core_safe_policy d registered (roles registry).governance (.bindLimiter d.limiterAddress) w hs' h

theorem core_safe_invoke (d : Deployment) (w : World) (entry : Entry) (next : World)
    (hc : CoreSafe w.core) (ha : EntryAdmissible entry)
    (h : invoke d w entry = .ok next) : CoreSafe next.core := by
  cases entry with
  | ordinary caller args obs => exact core_safe_withdraw d w caller args obs next hc ha h
  | approved caller args sig obs => exact core_safe_approved d w caller args sig obs next hc ha h
  | funding caller target token amount msgValue obs => exact core_safe_deposit d w caller target token amount msgValue obs next hc ha h
  | policy caller action => exact core_safe_policy d w caller action next hc h
  | environment action =>
    rw [← Except.ok.inj h]
    exact core_safe_environment d w action hc ha
  | abort error => contradiction

theorem core_safe_reachable (d : Deployment) (w : World) (xs : List Checkpoint)
    (hr : Reachable d w xs) : CoreSafe w.core := by
  induction hr with
  | initialized now capacity rate owner fee registry roles w h =>
    exact core_safe_fresh d now capacity rate owner fee registry roles w h
  | success w next xs entry hr ha h ih => exact core_safe_invoke d w entry next ih ha h
  | caughtFailure w xs entry err hr h ih => exact ih
  | endTx w xs hr ih => exact ih
  | newTx w next xs now hr h ih =>
    rw [(core_nextTransaction_frame w now next h).2.2.1]
    exact ih

theorem core_safe_route (d : Deployment) (calls : List RouteCall) (w next : World)
    (hc : CoreSafe w.core) (ha : ∀ c ∈ calls, EntryAdmissible c.entry)
    (h : route d calls w = .ok next) : CoreSafe next.core := by
  induction calls generalizing w with
  | nil => rw [← Except.ok.inj h]; exact hc
  | cons c cs ih =>
    have htail : ∀ x ∈ cs, EntryAdmissible x.entry := fun x hx => ha x (by simp [hx])
    simp only [route] at h
    cases hp : invoke d w c.entry with
    | ok out =>
      rw [hp] at h
      exact ih out (core_safe_invoke d w c.entry out hc (ha c (by simp)) hp) htail h
    | error e =>
      rw [hp] at h
      dsimp only at h
      split at h
      · exact ih w hc htail h
      · contradiction

#print axioms core_safe_reachable
#print axioms core_safe_invoke
#print axioms core_safe_route

end Benchmark.Cases.Kuru.WithdrawalLimit
