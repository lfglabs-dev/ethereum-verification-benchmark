import Benchmark.Cases.KPK.SharesSettlementAccounting.Records

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

-- A pure description of the actual inherited-ledger writes, not a fee oracle.
def mintedState (s : State) (toAddr : Address) (amount : Nat) : State :=
  {shareWrite (supplyWrite s ((s.caller.readSlot supplySlot.slot) + word amount))
    toAddr ((s.caller.readMap balanceSlot.slot toAddr) + word amount) with
    trace := s.trace ++ [.mint toAddr amount]}

def optionalMintState (s : State) (toAddr : Address) (amount : Nat) : State :=
  if amount > 0 then mintedState s toAddr amount else s

theorem optionalMint_success (s t : State) (toAddr : Address) (amount : Nat)
    (ha : amount < wordLimit)
    (h : (show Tx Unit from do if amount > 0 then _mint toAddr amount) s = .ok ((),t)) :
    totalSupply s + amount < wordLimit ∧ t = optionalMintState s toAddr amount := by
  by_cases hp : amount > 0
  · simp only [hp,↓reduceIte] at h
    obtain ⟨_,hs,ht⟩ := mint_success s t toAddr amount ha h
    exact ⟨hs,by simpa only [optionalMintState,hp,↓reduceIte,mintedState] using ht⟩
  · have hz : amount = 0 := by omega
    subst amount
    have ht : t = s := by
      change Except.ok ((),s) = Except.ok ((),t) at h
      exact (congrArg Prod.snd (Except.ok.inj h)).symm
    exact ⟨by simpa using totalSupply_bounded s,by simpa [optionalMintState] using ht⟩

theorem optionalMint_effects (s t : State) (toAddr : Address) (amount : Nat)
    (hl : LedgerCoherent s) (ha : amount < wordLimit)
    (h : (show Tx Unit from do if amount > 0 then _mint toAddr amount) s = .ok ((),t)) :
    totalSupply t = totalSupply s + amount ∧
    (∀ x, shareBalance t x = shareBalance s x + if x = toAddr then amount else 0) ∧
    LedgerCoherent t := by
  by_cases hp : amount > 0
  · simp only [hp,↓reduceIte] at h
    exact mint_effects s t toAddr amount hl ha h
  · have hz : amount = 0 := by omega
    have ht := (optionalMint_success s t toAddr amount ha h).2
    simp only [optionalMintState,hp,↓reduceIte] at ht
    subst t
    simpa [hz] using hl

theorem optionalMint_trace (s : State) (toAddr : Address) (amount : Nat) :
    (optionalMintState s toAddr amount).trace =
      s.trace ++ (if amount > 0 then [.mint toAddr amount] else []) := by
  by_cases hp : amount > 0 <;> simp [optionalMintState,mintedState,hp]

theorem optionalMint_config (s : State) (toAddr : Address) (amount : Nat) :
    (optionalMintState s toAddr amount).config = s.config := by
  by_cases hp : amount > 0 <;> simp [optionalMintState,mintedState,shareWrite,supplyWrite,hp]

theorem managementFee_success (s t : State) (elapsed fee : Nat)
    (hr : s.config.managementFeeRate < wordLimit) (he : elapsed < wordLimit)
    (h : _chargeManagementFee elapsed s = .ok (fee,t)) :
    ∃ net annual product m,
      net = totalSupply s - shareBalance s s.config.feeReceiver ∧
      annual = net * s.config.managementFeeRate ∧ annual < wordLimit ∧
      product = annual * elapsed ∧ product < wordLimit ∧
      fee = product / (bps * 31536000) ∧
      (show Tx Unit from do if fee > 0 then _mint s.config.feeReceiver fee) s = .ok ((),m) ∧
      totalSupply s + fee < wordLimit ∧
      t = {optionalMintState s s.config.feeReceiver fee with
        trace := (optionalMintState s s.config.feeReceiver fee).trace ++ [.management fee]} := by
  simp only [_chargeManagementFee] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg : st = s ∧ m0 = s := by
    change Except.ok (s,s) = Except.ok (st,m0) at hget
    exact Prod.mk.inj (Except.ok.inj hget).symm
  rw [hg.1,hg.2] at h1
  obtain ⟨net,m1,hn,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  obtain ⟨_,hnet,hm1⟩ := checkedSub_success _ _ _ _ _ (totalSupply_bounded s)
    (shareBalance_bounded s _) hn
  rw [hm1] at h2
  have hnB : net < wordLimit := by rw [hnet]; exact lt_of_le_of_lt (Nat.sub_le _ _) (totalSupply_bounded s)
  obtain ⟨annual,m2,ha,h3⟩ := tx_bind_ok _ _ _ _ _ h2
  obtain ⟨haB,haEq,hm2⟩ := checkedMul_success _ _ _ _ _ hnB hr ha
  rw [hm2] at h3
  obtain ⟨product,m3,hp,h4⟩ := tx_bind_ok _ _ _ _ _ h3
  obtain ⟨hpB,hpEq,hm3⟩ := checkedMul_success _ _ _ _ _ (by rw [haEq]; exact haB) he hp
  rw [hm3] at h4
  have h4' : ((show Tx Unit from do if product / (bps * 31536000) > 0 then
      _mint s.config.feeReceiver (product / (bps * 31536000))) >>= fun _ => do
      record (.management (product / (bps * 31536000)))
      pure (product / (bps * 31536000))) s = .ok (fee,t) := by
    split_ifs with hpos <;> simpa only [hpos,↓reduceIte] using h4
  obtain ⟨u,m,hm,h5⟩ := tx_bind_ok _ _ _ _ _ h4'
  cases u
  obtain ⟨u,z,hrecord,hret⟩ := tx_bind_ok _ _ _ _ _ h5
  have hz : z = {m with trace := m.trace ++ [.management (product / (bps * 31536000))]} := by
    rw [record_run] at hrecord
    exact (congrArg Prod.snd (Except.ok.inj hrecord)).symm
  have hreturn : fee = product / (bps * 31536000) ∧ t = z := by
    change Except.ok (product / (bps * 31536000),z) = Except.ok (fee,t) at hret
    exact Prod.mk.inj (Except.ok.inj hret).symm
  have hfB : fee < wordLimit := by rw [hreturn.1]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hpEq]; exact hpB)
  rw [← hreturn.1] at hm hz
  obtain ⟨hs,hmEq⟩ := optionalMint_success s m s.config.feeReceiver fee hfB hm
  refine ⟨net,annual,product,m,hnet,haEq,by rw [haEq]; exact haB,hpEq,by rw [hpEq]; exact hpB,hreturn.1,hm,hs,?_⟩
  rw [hreturn.2,hz,hmEq]

def moduleStateUpdate (s : State) (moduleAddr : Address) (cells : Nat → Nat) : State :=
  {s with external := {accountState := fun target k =>
    if target == moduleAddr.val then cells k else s.external.accountState target k}}

def performanceIssuedState (s : State) (price elapsed net fee : Nat) (cells : Nat → Nat) : State :=
  let callState := {moduleStateUpdate s s.config.performanceFeeModule cells with
    trace := s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee]}
  let issued := optionalMintState callState s.config.feeReceiver fee
  {issued with trace := issued.trace ++ [.performance fee]}

-- The responder witness is constrained by the REAL input world and all source
-- arguments. Zero module returns without adding a performance marker.
theorem performanceFee_success (env : Environment) (s t : State) (price elapsed fee : Nat)
    (h : _chargePerformanceFee env price elapsed s = .ok (fee,t)) :
    (s.config.performanceFeeModule = 0 ∧ fee = 0 ∧ t = s) ∨
    ∃ net cells m,
      s.config.performanceFeeModule ≠ 0 ∧
      net = totalSupply s - shareBalance s s.config.feeReceiver ∧
      env.hasCode s.config.performanceFeeModule = true ∧
      s.config.performanceFeeModule ≠ s.config.self ∧
      env.isToken s.config.performanceFeeModule = false ∧
      env.feeResponder
        ⟨s.config.performanceFeeModule,s.config.self,price,elapsed,s.config.performanceFeeRate,net⟩
        (s.external.accountState s.config.performanceFeeModule.val) = .ok (fee,cells) ∧
      fee < wordLimit ∧
      (show Tx Unit from do if fee > 0 then _mint s.config.feeReceiver fee)
        {moduleStateUpdate s s.config.performanceFeeModule cells with
          trace := s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee]}
          = .ok ((),m) ∧
      totalSupply s + fee < wordLimit ∧
      t = performanceIssuedState s price elapsed net fee cells := by
  simp only [_chargePerformanceFee] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg : st = s ∧ m0 = s := by
    change Except.ok (s,s) = Except.ok (st,m0) at hget
    exact Prod.mk.inj (Except.ok.inj hget).symm
  rw [hg.1,hg.2] at h1
  by_cases hz : s.config.performanceFeeModule = 0
  · simp only [hz,beq_self_eq_true,↓reduceIte,Pure.pure,StateT.pure,Except.pure,
      Except.ok.injEq,Prod.mk.injEq] at h1
    exact Or.inl ⟨hz,h1.1.symm,h1.2.symm⟩
  · have hzB : (s.config.performanceFeeModule == 0) = false := by simpa using hz
    simp only [hzB,Bool.false_eq_true,↓reduceIte] at h1
    obtain ⟨u,m00,hpure,h1a⟩ := tx_bind_ok _ _ _ _ _ h1
    have hm00 : m00 = s := by
      change Except.ok (PUnit.unit,s) = Except.ok (u,m00) at hpure
      exact (congrArg Prod.snd (Except.ok.inj hpure)).symm
    rw [hm00] at h1a
    obtain ⟨net,m1,hn,h2⟩ := tx_bind_ok _ _ _ _ _ h1a
    obtain ⟨_,hnet,hm1⟩ := checkedSub_success _ _ _ _ _ (totalSupply_bounded s)
      (shareBalance_bounded s _) hn
    rw [hm1] at h2
    obtain ⟨u,m2,hg1,h3⟩ := tx_bind_ok _ _ _ _ _ h2
    obtain ⟨hcode,hm2⟩ := guard_success _ _ _ _ _ hg1
    rw [hm2] at h3
    obtain ⟨u,m3,hg2,h4⟩ := tx_bind_ok _ _ _ _ _ h3
    obtain ⟨hdispatch,hm3⟩ := guard_success _ _ _ _ _ hg2
    rw [hm3] at h4
    have hd : s.config.performanceFeeModule ≠ s.config.self ∧
        env.isToken s.config.performanceFeeModule = false := by simpa using hdispatch
    cases hc : env.feeResponder
        ⟨s.config.performanceFeeModule,s.config.self,price,elapsed,s.config.performanceFeeRate,net⟩
        (s.external.accountState s.config.performanceFeeModule.val) with
    | error e =>
      simp [hc,MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift,
        Bind.bind,Except.bind] at h4
    | ok result =>
      rcases result with ⟨issued,cells⟩
      simp only [hc] at h4
      obtain ⟨u,m4,hg3,h5⟩ := tx_bind_ok _ _ _ _ _ h4
      obtain ⟨hbound,hm4⟩ := guard_success _ _ _ _ _ hg3
      have hb : issued < wordLimit := by simpa using hbound
      rw [hm4] at h5
      obtain ⟨u,m5,hwrite,h6⟩ := tx_bind_ok _ _ _ _ _ h5
      have hm5 : m5 = moduleStateUpdate s s.config.performanceFeeModule cells := by
        change Except.ok ((),moduleStateUpdate s s.config.performanceFeeModule cells) = Except.ok (u,m5) at hwrite
        exact (congrArg Prod.snd (Except.ok.inj hwrite)).symm
      rw [hm5] at h6
      obtain ⟨u,m6,hcall,h7⟩ := tx_bind_ok _ _ _ _ _ h6
      have hm6 : m6 = {moduleStateUpdate s s.config.performanceFeeModule cells with
          trace := s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net issued]} := by
        rw [record_run] at hcall
        exact (congrArg Prod.snd (Except.ok.inj hcall)).symm
      rw [hm6] at h7
      have h7' : ((show Tx Unit from do if issued > 0 then _mint s.config.feeReceiver issued) >>= fun _ => do
          record (.performance issued); pure issued)
          {moduleStateUpdate s s.config.performanceFeeModule cells with
            trace := s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net issued]}
          = .ok (fee,t) := by
        split_ifs with hp <;> simpa only [hp,↓reduceIte] using h7
      obtain ⟨u,m,hm,h8⟩ := tx_bind_ok _ _ _ _ _ h7'
      cases u
      obtain ⟨u,z,hrecord,hret⟩ := tx_bind_ok _ _ _ _ _ h8
      have hreturn : fee = issued ∧ t = z := by
        change Except.ok (issued,z) = Except.ok (fee,t) at hret
        exact Prod.mk.inj (Except.ok.inj hret).symm
      have hz : z = {m with trace := m.trace ++ [.performance issued]} := by
        rw [record_run] at hrecord
        exact (congrArg Prod.snd (Except.ok.inj hrecord)).symm
      have ho := optionalMint_success _ _ s.config.feeReceiver issued hb hm
      refine Or.inr ⟨net,cells,m,?_,hnet,hcode,hd.1,hd.2,?_,?_,?_,?_,?_⟩
      · exact ‹s.config.performanceFeeModule ≠ 0›
      · rw [hreturn.1]; exact hc
      · rw [hreturn.1]; exact hb
      · rw [hreturn.1]; exact hm
      · rw [hreturn.1]; exact ho.1
      · rw [hreturn.2,hz,ho.2]
        simp only [performanceIssuedState,hreturn.1]

def managementPhase (env : Environment) (cfg : Configuration) : Tx Unit := do
  if cfg.managementFeeRate > 0 then
    let elapsed ← checkedSub env.now (← get).managementFeeLastUpdate
    if elapsed > 21600 then
      modify fun s => {s with managementFeeLastUpdate := env.now}
      let _ ← _chargeManagementFee elapsed

def performancePhase (env : Environment) (cfg : Configuration) (asset : Address) (price : Nat) : Tx Unit := do
  if cfg.performanceFeeRate > 0 && (cfg.assets asset).isFeeModuleAsset then
    let elapsed ← checkedSub env.now (← get).performanceFeeLastUpdate
    if elapsed > 21600 then
      modify fun s => {s with performanceFeeLastUpdate := env.now}
      let _ ← _chargePerformanceFee env price elapsed

theorem tx_if_bind (p : Prop) [Decidable p] (c d : Tx α) (f : α → Tx β) :
    ((if p then c else d) >>= f) = if p then (c >>= f) else (d >>= f) := by
  split_ifs <;> rfl

theorem chargeFees_phase_equation (env : Environment) (asset : Address) (price : Nat) :
    _chargeFees env asset price = (do
      let cfg := (← get).config
      managementPhase env cfg
      performancePhase env cfg asset price) := by
  simp only [_chargeFees,managementPhase,performancePhase,bind_assoc]
  congr 1
  funext st
  split_ifs <;> simp only [bind_assoc,tx_if_bind,pure_bind]


theorem tx_get_state (s st t : State) (h : (get : Tx State) s = .ok (st,t)) :
    st = s ∧ t = s := by
  change Except.ok (s,s) = Except.ok (st,t) at h
  exact Prod.mk.inj (Except.ok.inj h).symm

theorem tx_pure_state (a : α) (s t : State) (b : α)
    (h : (pure a : Tx α) s = .ok (b,t)) : b = a ∧ t = s := by
  change Except.ok (a,s) = Except.ok (b,t) at h
  exact Prod.mk.inj (Except.ok.inj h).symm

def managementPrefixState (env : Environment) (s : State) : State :=
  let fee := ExpectedManagement s env.now
  if s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 then
    let issued := optionalMintState {s with managementFeeLastUpdate := env.now} s.config.feeReceiver fee
    {issued with trace := issued.trace ++ [.management fee]}
  else s

-- Exact first-phase result, including checked products and actual mint evidence.
-- The initial coherent ledger is needed later for the fee receiver balance, not
-- assumed as a net-supply equality.
theorem managementPhase_success (env : Environment) (s t : State)
    (hn : env.now < wordLimit) (ht : s.managementFeeLastUpdate < wordLimit)
    (hr : s.config.managementFeeRate < wordLimit)
    (h : managementPhase env s.config s = .ok ((),t)) :
    t = managementPrefixState env s ∧
    totalSupply s + ExpectedManagement s env.now < wordLimit ∧
    (s.config.managementFeeRate > 0 → s.managementFeeLastUpdate ≤ env.now) ∧
    (s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 →
      (totalSupply s - shareBalance s s.config.feeReceiver) * s.config.managementFeeRate < wordLimit ∧
      (totalSupply s - shareBalance s s.config.feeReceiver) * s.config.managementFeeRate *
        (env.now - s.managementFeeLastUpdate) < wordLimit ∧
      ∃ m, (show Tx Unit from do if ExpectedManagement s env.now > 0 then
          _mint s.config.feeReceiver (ExpectedManagement s env.now))
          {s with managementFeeLastUpdate := env.now} = .ok ((),m)) := by
  by_cases hrp : s.config.managementFeeRate > 0
  · simp only [managementPhase,hrp,↓reduceIte] at h
    obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
    have hg := tx_get_state _ _ _ hget
    rw [hg.1,hg.2] at h1
    obtain ⟨elapsed,m1,hsub,h2⟩ := tx_bind_ok _ _ _ _ _ h1
    obtain ⟨hbefore,helapsed,hm1⟩ := checkedSub_success _ _ _ _ _ hn ht hsub
    rw [hm1] at h2
    by_cases hactive : elapsed > 21600
    · simp only [hactive,↓reduceIte] at h2
      obtain ⟨u,m2,hupdate,h3⟩ := tx_bind_ok _ _ _ _ _ h2
      have hm2 : m2 = {s with managementFeeLastUpdate := env.now} := by
        change Except.ok ((),{s with managementFeeLastUpdate := env.now}) = Except.ok (u,m2) at hupdate
        exact (congrArg Prod.snd (Except.ok.inj hupdate)).symm
      rw [hm2] at h3
      obtain ⟨fee,m3,hfee,hret⟩ := tx_bind_ok _ _ _ _ _ h3
      have hfinal := (tx_pure_state () _ _ () hret).2
      obtain ⟨net,annual,product,m,hnet,ha,haB,hprod,hprodB,hfeq,hm,hfit,hresult⟩ :=
        managementFee_success {s with managementFeeLastUpdate := env.now} m3 elapsed fee hr
          (by rw [helapsed]; omega) hfee
      have hcond : s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 :=
        ⟨hrp,by rwa [helapsed] at hactive⟩
      have hfeeEq : fee = ExpectedManagement s env.now := by
        simp only [ExpectedManagement,hcond,↓reduceIte]
        rw [hfeq,hprod,ha,hnet,helapsed]
        rfl
      refine ⟨?_,?_,fun _ => hbefore,?_⟩
      · rw [hfinal,hresult,hfeeEq]
        simp [managementPrefixState,hcond]
      · simpa only [← hfeeEq,totalSupply] using hfit
      · intro _
        refine ⟨?_,?_,m,?_⟩
        · simpa only [ha,hnet,totalSupply,shareBalance] using haB
        · simpa only [hprod,ha,hnet,helapsed,totalSupply,shareBalance] using hprodB
        · simpa only [← hfeeEq] using hm
    · simp only [hactive,↓reduceIte] at h2
      have hfinal := (tx_pure_state PUnit.unit _ _ () h2).2
      have hcond : ¬(s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600) := by
        rw [helapsed] at hactive
        exact fun hc => hactive hc.2
      have hf : ExpectedManagement s env.now = 0 := by simp [ExpectedManagement,hcond]
      exact ⟨by simpa [managementPrefixState,hcond] using hfinal,
        by simpa [hf] using totalSupply_bounded s,fun _ => hbefore,fun hc => False.elim (hcond hc)⟩
  · simp only [managementPhase,hrp,↓reduceIte] at h
    have hfinal := (tx_pure_state PUnit.unit _ _ () h).2
    have hcond : ¬(s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600) :=
      fun hc => hrp hc.1
    have hf : ExpectedManagement s env.now = 0 := by simp [ExpectedManagement,hcond]
    exact ⟨by simpa [managementPrefixState,hcond] using hfinal,
      by simpa [hf] using totalSupply_bounded s,fun hc => False.elim (hrp hc),fun hc => False.elim (hcond hc)⟩

theorem optionalMint_frame (s t : State) (toAddr : Address) (amount : Nat) (asset : Address)
    (ha : amount < wordLimit)
    (h : (show Tx Unit from do if amount > 0 then _mint toAddr amount) s = .ok ((),t)) :
    CallerFrame s t asset := by
  by_cases hp : amount > 0
  · simp only [hp,↓reduceIte] at h
    exact mint_frame s t toAddr amount asset ha h
  · have ht := (optionalMint_success s t toAddr amount ha h).2
    simp only [optionalMintState,hp,↓reduceIte] at ht
    rw [ht]
    simp [CallerFrame]

-- Channels outside share accounting and fee clocks. Entire request records,
-- not merely payloads, are preserved by the fee prefix.
def FeeDataFrame (s t : State) : Prop :=
  t.config = s.config ∧ t.requests = s.requests ∧
  t.subscriptionAssets = s.subscriptionAssets ∧ t.pendingRequestsCount = s.pendingRequestsCount ∧
  t.lastSettledPrice = s.lastSettledPrice

theorem optionalMint_data (s : State) (toAddr : Address) (amount : Nat) :
    FeeDataFrame s (optionalMintState s toAddr amount) ∧
    (optionalMintState s toAddr amount).external = s.external ∧
    (optionalMintState s toAddr amount).managementFeeLastUpdate = s.managementFeeLastUpdate ∧
    (optionalMintState s toAddr amount).performanceFeeLastUpdate = s.performanceFeeLastUpdate := by
  by_cases hp : amount > 0 <;>
    simp [FeeDataFrame,optionalMintState,mintedState,shareWrite,supplyWrite,hp]

theorem managementPrefix_data (env : Environment) (s : State) :
    FeeDataFrame s (managementPrefixState env s) ∧
    (managementPrefixState env s).external = s.external ∧
    (managementPrefixState env s).performanceFeeLastUpdate = s.performanceFeeLastUpdate ∧
    (managementPrefixState env s).managementFeeLastUpdate =
      (if s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 then env.now else s.managementFeeLastUpdate) ∧
    (managementPrefixState env s).trace = s.trace ++
      if s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 then
        (if ExpectedManagement s env.now > 0 then [.mint s.config.feeReceiver (ExpectedManagement s env.now)] else []) ++
          [.management (ExpectedManagement s env.now)] else [] := by
  by_cases hactive : s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 <;>
    by_cases hf : ExpectedManagement s env.now > 0 <;>
    simp [managementPrefixState,FeeDataFrame,optionalMintState,mintedState,shareWrite,supplyWrite,
      hactive,hf,List.append_assoc]

theorem managementPhase_accounting (env : Environment) (s t : State)
    (hn : env.now < wordLimit) (ht : s.managementFeeLastUpdate < wordLimit)
    (hr : s.config.managementFeeRate < wordLimit) (hl : LedgerCoherent s)
    (h : managementPhase env s.config s = .ok ((),t)) :
    totalSupply t = totalSupply s + ExpectedManagement s env.now ∧
    (∀ x, shareBalance t x = shareBalance s x + if x = s.config.feeReceiver then ExpectedManagement s env.now else 0) ∧
    LedgerCoherent t ∧ (∀ asset, CallerFrame s t asset) := by
  have hc := managementPhase_success env s t hn ht hr h
  by_cases ha : s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600
  · obtain ⟨_,hprodB,m,hm⟩ := hc.2.2.2 ha
    have hgB : ExpectedManagement s env.now < wordLimit := by
      simp only [ExpectedManagement,if_pos ha]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hprodB
    have hmEq := (optionalMint_success _ _ s.config.feeReceiver _ hgB hm).2
    have he := optionalMint_effects {s with managementFeeLastUpdate := env.now} m s.config.feeReceiver
      (ExpectedManagement s env.now) hl hgB hm
    have htEq : t = {m with trace := m.trace ++ [.management (ExpectedManagement s env.now)]} := by
      rw [hc.1]
      simp only [managementPrefixState,if_pos ha,← hmEq]
    rw [htEq]
    refine ⟨he.1,he.2.1,he.2.2,?_⟩
    intro asset
    have hf := optionalMint_frame {s with managementFeeLastUpdate := env.now} m s.config.feeReceiver
      (ExpectedManagement s env.now) asset hgB hm
    simpa only [CallerFrame] using hf
  · have hg : ExpectedManagement s env.now = 0 := by simp [ExpectedManagement,ha]
    have htEq : t = s := by simpa [managementPrefixState,ha] using hc.1
    rw [htEq]
    simp [hg,hl,CallerFrame]

-- Actual active performance-phase execution and checked elapsed time. The clock
-- update happens even when the source module address is zero.
theorem performancePhase_success (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (ht : s.performanceFeeLastUpdate < wordLimit)
    (h : performancePhase env s.config asset price s = .ok ((),t)) :
    ((s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true →
      s.performanceFeeLastUpdate ≤ env.now) ∧
    (if (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true ∧
        env.now - s.performanceFeeLastUpdate > 21600 then
      ∃ fee, _chargePerformanceFee env price (env.now - s.performanceFeeLastUpdate)
        {s with performanceFeeLastUpdate := env.now} = .ok (fee,t)
    else t = s) := by
  by_cases he : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true
  · simp only [performancePhase,he,↓reduceIte] at h
    obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
    have hg := tx_get_state _ _ _ hget
    rw [hg.1,hg.2] at h1
    obtain ⟨elapsed,m1,hsub,h2⟩ := tx_bind_ok _ _ _ _ _ h1
    obtain ⟨hbefore,helapsed,hm1⟩ := checkedSub_success _ _ _ _ _ hn ht hsub
    rw [hm1] at h2
    refine ⟨fun _ => hbefore,?_⟩
    by_cases ha : elapsed > 21600
    · simp only [ha,↓reduceIte] at h2
      obtain ⟨u,m2,hupdate,h3⟩ := tx_bind_ok _ _ _ _ _ h2
      have hm2 : m2 = {s with performanceFeeLastUpdate := env.now} := by
        change Except.ok ((),{s with performanceFeeLastUpdate := env.now}) = Except.ok (u,m2) at hupdate
        exact (congrArg Prod.snd (Except.ok.inj hupdate)).symm
      rw [hm2] at h3
      obtain ⟨fee,m3,hfee,hret⟩ := tx_bind_ok _ _ _ _ _ h3
      have hfinal := (tx_pure_state () _ _ () hret).2
      have ha' : env.now - s.performanceFeeLastUpdate > 21600 := by rwa [helapsed] at ha
      simp only [he,ha',and_self,if_true]
      exact ⟨fee,by rw [← helapsed,hfinal]; exact hfee⟩
    · have ha' : ¬env.now - s.performanceFeeLastUpdate > 21600 := by rwa [helapsed] at ha
      simp only [ha,↓reduceIte] at h2
      simp only [he,ha',and_false,if_false]
      exact (tx_pure_state () _ _ () h2).2
  · simp only [performancePhase,he,↓reduceIte] at h
    exact ⟨fun hh => False.elim (he hh),by simpa only [he,Bool.false_eq_true,false_and,if_false] using (tx_pure_state () _ _ () h).2⟩

def managementTrace (env : Environment) (s : State) : List Effect :=
  if s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 then
    (if ExpectedManagement s env.now > 0 then [.mint s.config.feeReceiver (ExpectedManagement s env.now)] else []) ++
      [.management (ExpectedManagement s env.now)] else []

def managementTime (env : Environment) (s : State) : Nat :=
  if s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 then env.now else s.managementFeeLastUpdate

-- Merely a factorization of the independently specified expectedFeePrefix.
-- No responder success or accounting conclusion is assumed here.
def expectedPerformancePart (env : Environment) (s : State) (asset : Address) (price g : Nat)
    (mt : Nat) (feeTrace : List Effect) : Except String FeeReceipt := do
  let cfg := s.config
  let enabled := cfg.performanceFeeRate > 0 && (cfg.assets asset).isFeeModuleAsset
  let elapsed ← if enabled then natSub env.now s.performanceFeeLastUpdate else pure 0
  let active := enabled && elapsed > 21600
  let pt := if active then env.now else s.performanceFeeLastUpdate
  if !active || cfg.performanceFeeModule == 0 then
    return ⟨feeTrace,s.external,mt,pt⟩
  natCheck (env.hasCode cfg.performanceFeeModule && cfg.performanceFeeModule != cfg.self && !env.isToken cfg.performanceFeeModule)
  let net ← natSub (totalSupply s + g) (shareBalance s cfg.feeReceiver + g)
  let (fee,cells) ← env.feeResponder
    ⟨cfg.performanceFeeModule,cfg.self,price,elapsed,cfg.performanceFeeRate,net⟩
    (s.external.accountState cfg.performanceFeeModule.val)
  natCheck (fee < wordLimit && totalSupply s + g + fee < wordLimit)
  return ⟨feeTrace ++ [.moduleCall cfg.performanceFeeModule price elapsed cfg.performanceFeeRate net fee] ++
    (if fee > 0 then [.mint cfg.feeReceiver fee] else []) ++ [.performance fee],
    (moduleStateUpdate s cfg.performanceFeeModule cells).external,mt,pt⟩

theorem expectedFeePrefix_management_factor (env : Environment) (s m : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (ht : s.managementFeeLastUpdate < wordLimit)
    (hr : s.config.managementFeeRate < wordLimit) (hl : LedgerCoherent s)
    (h : managementPhase env s.config s = .ok ((),m)) :
    expectedFeePrefix env s asset price = expectedPerformancePart env s asset price
      (ExpectedManagement s env.now) (managementTime env s) (managementTrace env s) := by
  have hc := managementPhase_success env s m hn ht hr h
  have hnet := ledger_balance_le_supply s hl s.config.feeReceiver
  by_cases hrp : s.config.managementFeeRate > 0
  · have hbefore := hc.2.2.1 hrp
    by_cases ha : env.now - s.managementFeeLastUpdate > 21600
    · have hcond : s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600 := ⟨hrp,ha⟩
      obtain ⟨hannual,hproduct,_⟩ := hc.2.2.2 hcond
      have hgfit := hc.2.1
      simp only [ExpectedManagement,if_pos hcond] at hgfit
      simp [expectedFeePrefix,expectedPerformancePart,managementTrace,managementTime,
        ExpectedManagement,hrp,ha,natSub,natMul,natCheck,Bind.bind,Except.bind,Pure.pure,Except.pure,
        show ¬s.managementFeeLastUpdate > env.now by omega,
        show ¬shareBalance s s.config.feeReceiver > totalSupply s by omega,
        show ¬(totalSupply s - shareBalance s s.config.feeReceiver) * s.config.managementFeeRate ≥ wordLimit by omega,
        show ¬(totalSupply s - shareBalance s s.config.feeReceiver) * s.config.managementFeeRate *
          (env.now - s.managementFeeLastUpdate) ≥ wordLimit by omega,hgfit,moduleStateUpdate]
    · have hgfit := totalSupply_bounded s
      simp [expectedFeePrefix,expectedPerformancePart,managementTrace,managementTime,
        ExpectedManagement,hrp,ha,natSub,natCheck,Bind.bind,Except.bind,Pure.pure,Except.pure,
        show ¬s.managementFeeLastUpdate > env.now by omega,hgfit,moduleStateUpdate]
  · have hgfit := totalSupply_bounded s
    simp [expectedFeePrefix,expectedPerformancePart,managementTrace,managementTime,
      ExpectedManagement,hrp,natCheck,Bind.bind,Except.bind,Pure.pure,Except.pure,hgfit,moduleStateUpdate]

theorem performanceIssued_data (s : State) (price elapsed net fee : Nat) (cells : Nat → Nat) :
    FeeDataFrame s (performanceIssuedState s price elapsed net fee cells) ∧
    (performanceIssuedState s price elapsed net fee cells).external =
      (moduleStateUpdate s s.config.performanceFeeModule cells).external ∧
    (performanceIssuedState s price elapsed net fee cells).managementFeeLastUpdate = s.managementFeeLastUpdate ∧
    (performanceIssuedState s price elapsed net fee cells).performanceFeeLastUpdate = s.performanceFeeLastUpdate ∧
    (performanceIssuedState s price elapsed net fee cells).trace =
      s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee] ++
        (if fee > 0 then [.mint s.config.feeReceiver fee] else []) ++ [.performance fee] := by
  by_cases hf : fee > 0 <;>
    simp [FeeDataFrame,performanceIssuedState,optionalMintState,mintedState,shareWrite,supplyWrite,
      moduleStateUpdate,hf,List.append_assoc]

-- Universal receipt correspondence for the complete fee prefix. No restriction
-- on role aliases; coherence makes management issuance update supply AND fee
-- receiver balance before the responder's exact net-supply argument is computed.
theorem chargeFees_prefix (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (hmt : s.managementFeeLastUpdate < wordLimit)
    (hpt : s.performanceFeeLastUpdate < wordLimit) (hr : s.config.managementFeeRate < wordLimit)
    (hl : LedgerCoherent s)
    (h : _chargeFees env asset price s = .ok ((),t)) :
    ∃ receipt, expectedFeePrefix env s asset price = .ok receipt ∧
      t.trace = s.trace ++ receipt.trace ∧ t.external = receipt.world ∧
      t.managementFeeLastUpdate = receipt.managementTime ∧
      t.performanceFeeLastUpdate = receipt.performanceTime ∧ FeeDataFrame s t := by
  rw [chargeFees_phase_equation] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h1
  obtain ⟨u,m,hm,hp⟩ := tx_bind_ok _ _ _ _ _ h1
  cases u
  have hc := managementPhase_success env s m hn hmt hr hm
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  have hcfg : m.config = s.config := hd.1.1
  have hworld : m.external = s.external := hd.2.1
  have hptime : m.performanceFeeLastUpdate = s.performanceFeeLastUpdate := hd.2.2.1
  have hmtime : m.managementFeeLastUpdate = managementTime env s := hd.2.2.2.1
  have htrace : m.trace = s.trace ++ managementTrace env s := hd.2.2.2.2
  have he := managementPhase_accounting env s m hn hmt hr hl hm
  have hsup : totalSupply m = totalSupply s + ExpectedManagement s env.now := he.1
  have hrecv : shareBalance m s.config.feeReceiver = shareBalance s s.config.feeReceiver + ExpectedManagement s env.now := by
    simpa using he.2.1 s.config.feeReceiver
  rw [← hcfg] at hp
  have hpv := performancePhase_success env m t asset price hn (by rw [hptime]; exact hpt) hp
  have factor := expectedFeePrefix_management_factor env s m asset price hn hmt hr hl hm
  rw [factor]
  by_cases hen : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true
  · have hbefore : s.performanceFeeLastUpdate ≤ env.now := by
      rw [hptime] at hpv
      exact hpv.1 (by rw [hcfg]; exact hen)
    by_cases hactive : env.now - s.performanceFeeLastUpdate > 21600
    · have hpRun := hpv.2
      simp only [hcfg,hptime,hen,hactive,and_self,if_true] at hpRun
      obtain ⟨fee,hfee⟩ := hpRun
      have hfeeInfo := performanceFee_success env {m with performanceFeeLastUpdate := env.now} t price
        (env.now - s.performanceFeeLastUpdate) fee (by simpa only [hcfg] using hfee)
      rcases hfeeInfo with hzero | hissued
      · rcases hzero with ⟨hmodule,hfee0,htEq⟩
        have hz : s.config.performanceFeeModule = 0 := by simpa only [hcfg] using hmodule
        let receipt : FeeReceipt := ⟨managementTrace env s,s.external,managementTime env s,env.now⟩
        refine ⟨receipt,?_,?_,?_,?_,?_,?_⟩
        · simp [expectedPerformancePart,hen,hactive,hz,natSub,
            show ¬s.performanceFeeLastUpdate > env.now by omega,
            Bind.bind,Except.bind,Pure.pure,Except.pure,receipt]
        · rw [htEq]; exact htrace
        · rw [htEq]; exact hworld
        · rw [htEq]; exact hmtime
        · rw [htEq]
        · rw [htEq]; exact hd.1
      · obtain ⟨net,cells,z,hmodule,hnet,hcode,hself,htoken,hresponder,hfeeB,hmint,hfit,htEq⟩ := hissued
        have hz : s.config.performanceFeeModule ≠ 0 := by simpa only [hcfg] using hmodule
        have hnetEq : net = totalSupply s + ExpectedManagement s env.now -
            (shareBalance s s.config.feeReceiver + ExpectedManagement s env.now) := by
          change net = totalSupply m - shareBalance m m.config.feeReceiver at hnet
          rw [hcfg,hsup,hrecv] at hnet
          exact hnet
        have hres : env.feeResponder
            ⟨s.config.performanceFeeModule,s.config.self,price,env.now - s.performanceFeeLastUpdate,s.config.performanceFeeRate,net⟩
            (s.external.accountState s.config.performanceFeeModule.val) = .ok (fee,cells) := by
          simpa only [hcfg,hworld] using hresponder
        have hcde : env.hasCode s.config.performanceFeeModule = true := by simpa only [hcfg] using hcode
        have hnonself : s.config.performanceFeeModule ≠ s.config.self := by simpa only [hcfg] using hself
        have hntoken : env.isToken s.config.performanceFeeModule = false := by simpa only [hcfg] using htoken
        have hfit' : totalSupply s + ExpectedManagement s env.now + fee < wordLimit := by
          change totalSupply m + fee < wordLimit at hfit
          rwa [hsup] at hfit
        have hnetLe : shareBalance s s.config.feeReceiver + ExpectedManagement s env.now ≤
            totalSupply s + ExpectedManagement s env.now := by
          have hh := ledger_balance_le_supply s hl s.config.feeReceiver; omega
        let receipt : FeeReceipt :=
          ⟨managementTrace env s ++ [.moduleCall s.config.performanceFeeModule price (env.now - s.performanceFeeLastUpdate)
              s.config.performanceFeeRate net fee] ++ (if fee > 0 then [.mint s.config.feeReceiver fee] else []) ++ [.performance fee],
            (moduleStateUpdate s s.config.performanceFeeModule cells).external,managementTime env s,env.now⟩
        have hdata := performanceIssued_data {m with performanceFeeLastUpdate := env.now} price
          (env.now - s.performanceFeeLastUpdate) net fee cells
        rw [← htEq] at hdata
        refine ⟨receipt,?_,?_,?_,?_,?_,?_⟩
        · simp [expectedPerformancePart,hen,hactive,hz,natSub,natCheck,hcde,hnonself,hntoken,
            show ¬s.performanceFeeLastUpdate > env.now by omega,
            show ¬shareBalance s s.config.feeReceiver + ExpectedManagement s env.now >
              totalSupply s + ExpectedManagement s env.now by omega,
            ← hnetEq,hres,hfeeB,hfit',Bind.bind,Except.bind,Pure.pure,Except.pure,receipt]
        · rw [hdata.2.2.2.2]
          simp only [hcfg,htrace,receipt,List.append_assoc]
        · rw [hdata.2.1]
          simp only [moduleStateUpdate,hcfg,hworld,receipt]
        · rw [hdata.2.2.1]; exact hmtime
        · exact hdata.2.2.2.1
        · rcases hd.1 with ⟨hdcfg,hdreq,hdsub,hdcount,hdprice⟩
          rcases hdata.1 with ⟨htcfg,htreq,htsub,htcount,htprice⟩
          exact ⟨htcfg.trans hdcfg,htreq.trans hdreq,htsub.trans hdsub,htcount.trans hdcount,htprice.trans hdprice⟩
    · have hpRun := hpv.2
      simp only [hcfg,hptime,hen,hactive,and_false,if_false] at hpRun
      let receipt : FeeReceipt := ⟨managementTrace env s,s.external,managementTime env s,s.performanceFeeLastUpdate⟩
      refine ⟨receipt,?_,?_,?_,?_,?_,?_⟩
      · simp [expectedPerformancePart,hen,hactive,natSub,
          show ¬s.performanceFeeLastUpdate > env.now by omega,
          Bind.bind,Except.bind,Pure.pure,Except.pure,receipt]
      · rw [hpRun]; exact htrace
      · rw [hpRun]; exact hworld
      · rw [hpRun]; exact hmtime
      · rw [hpRun]; exact hptime
      · rw [hpRun]; exact hd.1
  · have hpRun := hpv.2
    simp only [hcfg,hptime,hen,false_and,if_false] at hpRun
    let receipt : FeeReceipt := ⟨managementTrace env s,s.external,managementTime env s,s.performanceFeeLastUpdate⟩
    refine ⟨receipt,?_,?_,?_,?_,?_,?_⟩
    · have henB : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = false :=
        Bool.eq_false_iff.mpr hen
      simp [expectedPerformancePart,henB,Bind.bind,Except.bind,Pure.pure,Except.pure,receipt]
    · rw [hpRun]; exact htrace
    · rw [hpRun]; exact hworld
    · rw [hpRun]; exact hmtime
    · rw [hpRun]; exact hptime
    · rw [hpRun]; exact hd.1

def FeeInvariant (env : Environment) (s : State) : Prop :=
  LedgerCoherent s ∧ ExternalApplicability env s ∧ RegisteredAllowanceRanges s

theorem optionalMint_invariant (env : Environment) (s t : State) (toAddr : Address) (amount : Nat)
    (hi : FeeInvariant env s) (ha : amount < wordLimit)
    (h : (show Tx Unit from do if amount > 0 then _mint toAddr amount) s = .ok ((),t)) :
    FeeInvariant env t := by
  have he := optionalMint_effects s t toAddr amount hi.1 ha h
  have ht := (optionalMint_success s t toAddr amount ha h).2
  have hd := optionalMint_data s toAddr amount
  rw [← ht] at hd
  refine ⟨he.2.2,?_,?_⟩
  · unfold ExternalApplicability
    rw [hd.1.1]
    have hb : assetBalance t = assetBalance s := by funext token owner; simp only [assetBalance,hd.2.1]
    rw [hb]
    exact hi.2.1
  · unfold RegisteredAllowanceRanges
    rw [hd.1.1]
    have hb : assetAllowance t = assetAllowance s := by funext token owner sp; simp only [assetAllowance,hd.2.1]
    rw [hb]
    exact hi.2.2

theorem performanceFee_closure (env : Environment) (s t : State) (price elapsed fee : Nat)
    (hi : FeeInvariant env s)
    (h : _chargePerformanceFee env price elapsed s = .ok (fee,t)) :
    FeeInvariant env t ∧ (∀ asset, CallerFrame s t asset) := by
  rcases performanceFee_success env s t price elapsed fee h with hzero | hissued
  · rw [hzero.2.2]
    exact ⟨hi,by intro asset; simp [CallerFrame]⟩
  · obtain ⟨net,cells,z,_,_,_,_,htoken,_,hfeeB,hmint,_,htEq⟩ := hissued
    let c : State := {moduleStateUpdate s s.config.performanceFeeModule cells with
      trace := s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee]}
    have hc : FeeInvariant env c :=
      ⟨hi.1,module_world_preserves_applicability s env hi.2.1 s.config.performanceFeeModule htoken cells,
        module_registered_ranges s env hi.2.1 hi.2.2 s.config.performanceFeeModule htoken cells⟩
    have hz := optionalMint_invariant env c z s.config.feeReceiver fee hc hfeeB hmint
    have hzEq := (optionalMint_success c z s.config.feeReceiver fee hfeeB hmint).2
    have htFinal : t = {z with trace := z.trace ++ [.performance fee]} := by
      rw [htEq]
      simp only [performanceIssuedState,c,← hzEq]
    rw [htFinal]
    refine ⟨hz,?_⟩
    intro asset
    have hf := optionalMint_frame c z s.config.feeReceiver fee asset hfeeB hmint
    simpa only [CallerFrame,c,moduleStateUpdate] using hf

theorem managementPhase_closure (env : Environment) (s t : State)
    (hn : env.now < wordLimit) (ht : s.managementFeeLastUpdate < wordLimit)
    (hr : s.config.managementFeeRate < wordLimit) (hi : FeeInvariant env s)
    (h : managementPhase env s.config s = .ok ((),t)) :
    FeeInvariant env t ∧ (∀ asset, CallerFrame s t asset) := by
  have ha := managementPhase_accounting env s t hn ht hr hi.1 h
  have hc := managementPhase_success env s t hn ht hr h
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  refine ⟨⟨ha.2.2.1,?_,?_⟩,ha.2.2.2⟩
  · unfold ExternalApplicability
    rw [hd.1.1]
    have hb : assetBalance t = assetBalance s := by funext token owner; simp only [assetBalance,hd.2.1]
    rw [hb]
    exact hi.2.1
  · unfold RegisteredAllowanceRanges
    rw [hd.1.1]
    have hb : assetAllowance t = assetAllowance s := by funext token owner sp; simp only [assetAllowance,hd.2.1]
    rw [hb]
    exact hi.2.2

theorem performancePhase_closure (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (ht : s.performanceFeeLastUpdate < wordLimit) (hi : FeeInvariant env s)
    (h : performancePhase env s.config asset price s = .ok ((),t)) :
    FeeInvariant env t ∧ (∀ a, CallerFrame s t a) := by
  have hc := performancePhase_success env s t asset price hn ht h
  by_cases ha : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true ∧
      env.now - s.performanceFeeLastUpdate > 21600
  · rw [if_pos ha] at hc
    obtain ⟨fee,hfee⟩ := hc.2
    have hf := performanceFee_closure env {s with performanceFeeLastUpdate := env.now} t price
      (env.now - s.performanceFeeLastUpdate) fee hi hfee
    exact hf
  · rw [if_neg ha] at hc
    rw [hc.2]
    exact ⟨hi,by intro a; simp [CallerFrame]⟩

theorem chargeFees_closure (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (hmt : s.managementFeeLastUpdate < wordLimit)
    (hpt : s.performanceFeeLastUpdate < wordLimit) (hr : s.config.managementFeeRate < wordLimit)
    (hi : FeeInvariant env s)
    (h : _chargeFees env asset price s = .ok ((),t)) :
    FeeInvariant env t ∧ (∀ a, CallerFrame s t a) := by
  rw [chargeFees_phase_equation] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h1
  obtain ⟨u,m,hm,hp⟩ := tx_bind_ok _ _ _ _ _ h1
  cases u
  have hmc := managementPhase_closure env s m hn hmt hr hi hm
  have hc := managementPhase_success env s m hn hmt hr hm
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  rw [← hd.1.1] at hp
  have hpc := performancePhase_closure env m t asset price hn (by rw [hd.2.2.1]; exact hpt) hmc.1 hp
  exact ⟨hpc.1,by intro a; exact callerFrame_trans s m t a (hmc.2 a) (hpc.2 a)⟩

#print axioms chargeFees_closure
#print axioms chargeFees_prefix
#print axioms expectedFeePrefix_management_factor
#print axioms managementPhase_accounting
#print axioms managementPrefix_data
#print axioms performancePhase_success
#print axioms managementPhase_success
#print axioms performanceFee_success
#print axioms optionalMint_success
#print axioms optionalMint_effects
#print axioms managementFee_success
end Benchmark.Cases.KPK.SharesSettlementAccounting
