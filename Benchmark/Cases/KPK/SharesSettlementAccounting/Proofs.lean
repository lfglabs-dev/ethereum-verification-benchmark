import Benchmark.Cases.KPK.SharesSettlementAccounting.TraceCertificates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000

-- Kernel proofs about the real transaction adapter and arbitrary finite traversal.
theorem rollback_of_error (c : Tx α) (s : State) (err : String)
    (h : c s = .error err) : (transaction c s).2 = s := by
  simp [transaction, h]

theorem transaction_success (c : Tx α) (s next : State) (a : α)
    (h : c s = .ok (a, next)) : (transaction c s).2 = next := by
  simp [transaction, h]

theorem iterate_append (body : Nat → Tx Unit) (xs ys : List Nat) :
    iterate body (xs ++ ys) = (do iterate body xs; iterate body ys) := by
  induction xs with
  | nil => simp [iterate]
  | cons x xs ih => simp [iterate, ih, bind_assoc]

-- Generic induction certificate is not itself a KPK accounting proof. The actual
-- source handler preservation obligations must be discharged independently.
theorem iterate_invariant (body : Nat → Tx Unit) (P : State → Prop)
    (step : ∀ id s next, P s → body id s = .ok ((), next) → P next)
    (ids : List Nat) (s next : State) (hs : P s)
    (h : iterate body ids s = .ok ((), next)) : P next := by
  induction ids generalizing s with
  | nil =>
      change Except.ok ((), s) = Except.ok ((), next) at h
      cases h
      exact hs
  | cons id ids ih =>
      simp only [iterate, Bind.bind, StateT.bind, Except.bind] at h
      cases hb : body id s with
      | error err => rw [hb] at h; cases h
      | ok result =>
          rcases result with ⟨u, mid⟩
          cases u
          have hn : P mid := step id s mid hs hb
          exact ih mid hn (by simpa only [hb] using h)

theorem self_share_effect (x a : Address) (amount : Nat) :
    shareEffect x (.share a a amount) = 0 := by
  simp [shareEffect]
theorem self_asset_effect (token x a : Address) (amount : Nat) :
    assetEffect token x (.asset token a a amount) = 0 := by
  simp [assetEffect]

-- A kernel-certified execution path retains EVERY ordered occurrence, including
-- duplicate IDs. It is evidence extracted from execution, not an accounting premise.
inductive HandlerPath (body : Nat → Tx Unit) : List Nat → State → State → Prop where
  | nil (s : State) : HandlerPath body [] s s
  | cons (id : Nat) (ids : List Nat) (s mid next : State)
      (step : body id s = .ok ((),mid)) (rest : HandlerPath body ids mid next) :
      HandlerPath body (id::ids) s next

theorem iterate_success_path (body : Nat → Tx Unit) (ids : List Nat) (s next : State)
    (h : iterate body ids s = .ok ((),next)) : HandlerPath body ids s next := by
  induction ids generalizing s with
  | nil =>
    change Except.ok ((),s) = Except.ok ((),next) at h
    cases h
    exact HandlerPath.nil _
  | cons id ids ih =>
    simp only [iterate] at h
    obtain ⟨u,mid,hb,ht⟩ := tx_bind_ok _ _ _ _ _ h
    cases u
    exact HandlerPath.cons id ids s mid next hb (ih mid ht)

theorem two_array_success_paths (env : Environment) (approved rejected : List Nat)
    (asset : Address) (price : Nat) (s next : State)
    (h : (do
      _processApproved env approved asset price
      _processRejected env rejected asset) s = .ok ((),next)) :
    ∃ mid, HandlerPath (approveOne env asset price) approved s mid ∧
      HandlerPath (rejectOne env asset) rejected mid next := by
  obtain ⟨u,mid,ha,hr⟩ := tx_bind_ok _ _ _ _ _ h
  cases u
  exact ⟨mid,iterate_success_path _ _ _ _ ha,iterate_success_path _ _ _ _ hr⟩

theorem tx_get_success (s st t : State) (h : (get : Tx State) s = .ok (st,t)) :
    st = s ∧ t = s := by
  change Except.ok (s,s) = Except.ok (st,t) at h
  exact Prod.mk.inj (Except.ok.inj h).symm

-- Successful execution exposes the actual phase states, rather than presupposing
-- fee correctness or the desired settlement result.
theorem processRequests_success_phases (env : Environment) (approved rejected : List Nat)
    (asset : Address) (price : Nat) (s next : State)
    (h : processRequests env approved rejected asset price s = .ok ((),next)) :
    ∃ v f a r,
      s.config.operators env.sender = true ∧
      _validatePriceDeviation asset price s = .ok ((),v) ∧
      _chargeFees env asset price v = .ok ((),f) ∧
      HandlerPath (approveOne env asset price) approved f a ∧
      HandlerPath (rejectOne env asset) rejected a r ∧
      next = {r with lastSettledPrice := fun x => if x == asset then price else r.lastSettledPrice x} := by
  simp only [processRequests] at h
  obtain ⟨st,m,hg,h1⟩ := tx_bind_ok _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := tx_get_success _ _ _ hg
  obtain ⟨u,m,hg,h2⟩ := tx_bind_ok _ _ _ _ _ h1
  obtain ⟨hop,hm⟩ := guard_success _ _ _ _ _ hg
  rw [hm] at h2
  obtain ⟨u,v,hv,h3⟩ := tx_bind_ok _ _ _ _ _ h2
  cases u
  obtain ⟨u,f,hf,h4⟩ := tx_bind_ok _ _ _ _ _ h3
  cases u
  obtain ⟨u,a,ha,h5⟩ := tx_bind_ok _ _ _ _ _ h4
  cases u
  obtain ⟨u,r,hr,h6⟩ := tx_bind_ok _ _ _ _ _ h5
  cases u
  have hn : next = {r with lastSettledPrice := fun x => if x == asset then price else r.lastSettledPrice x} := by
    change Except.ok ((), {r with lastSettledPrice := fun x => if x == asset then price else r.lastSettledPrice x}) = Except.ok ((),next) at h6
    exact (congrArg Prod.snd (Except.ok.inj h6)).symm
  exact ⟨v,f,a,r,hop,hv,hf,iterate_success_path _ _ _ _ ha,
    iterate_success_path _ _ _ _ hr,hn⟩

-- The fee receipt starts from the ORIGINAL input state: successful price
-- validation is identity, so initial ranges/coherence legitimately feed Fees.
theorem processRequests_initial_fee (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hprice : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    ∃ f a r receipt,
      expectedFeePrefix env s asset price = .ok receipt ∧
      f.trace = receipt.trace ∧ f.external = receipt.world ∧
      f.managementFeeLastUpdate = receipt.managementTime ∧
      f.performanceFeeLastUpdate = receipt.performanceTime ∧
      FeeDataFrame s f ∧ FeeInvariant env f ∧ (∀ x, CallerFrame s f x) ∧
      HandlerPath (approveOne env asset price) approved f a ∧
      HandlerPath (rejectOne env asset) rejected a r ∧
      t = {r with lastSettledPrice := fun x => if x == asset then price else r.lastSettledPrice x} := by
  rcases hw with ⟨htrace,hl,hrecords,hn,hzero,hnow,hself,hsafe,hrecv,hmrate,hrrate,hprate,hmt,hpt,hlast,
    hcounters,hassets,hbalances,hallowances,houtside,hrequests,hescrow,hredescrow⟩
  obtain ⟨v,f,a,r,_,hv,hf,ha,hr,ht⟩ := processRequests_success_phases env approved rejected asset price s t h
  have hvEq := validatePriceDeviation_success asset price s v hprice (hlast asset) hv
  rw [hvEq] at hf
  have hrate : s.config.managementFeeRate < wordLimit := by
    have hlarge : 2000 < wordLimit := by norm_num [wordLimit]
    omega
  obtain ⟨receipt,hreceipt,hftrace,hworld,hftime,hptime,hdata⟩ := chargeFees_prefix env s f asset price
    hnow hmt hpt hrate hl hf
  have hregistered : RegisteredAllowanceRanges s := by
    intro token owner spender _ _; exact hallowances token owner spender
  have hclosed := chargeFees_closure env s f asset price hnow hmt hpt hrate ⟨hl,hap,hregistered⟩ hf
  refine ⟨f,a,r,receipt,hreceipt,?_,hworld,hftime,hptime,hdata,hclosed.1,hclosed.2,ha,hr,ht⟩
  simpa only [htrace,List.nil_append] using hftrace

#print axioms processRequests_initial_fee
#print axioms processRequests_success_phases
#print axioms iterate_success_path
#print axioms two_array_success_paths

theorem handlerPath_recordRun (env : Environment) (body : Nat → Tx Unit) (n : Nat)
    (step : ∀ id s t, Structural env s n → body id s = .ok ((),t) → RecordTransition env s t n id)
    (ids : List Nat) (s t : State) (hi : Structural env s n)
    (h : HandlerPath body ids s t) : RecordRun env s t n ids := by
  induction h with
  | nil s => exact recordRun_nil env s n hi
  | cons id ids s mid t hb hr ih =>
    have hs := step id s mid hi hb
    exact recordRun_cons env s mid t n id ids hs (ih hs.closed)

-- Universal full-process record/frame component. This is deliberately named as a
-- component; the complete sums/decisions/world conjunction is proved below by settlement_accounting.
theorem processRequests_record_integrity (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    RecordsConsistent t n ∧ FeeInvariant env t ∧ t.config = s.config ∧
    CallerFrame s t asset ∧ t.lastSettledPrice asset = price ∧
    (∀ id, Payload (s.requests id) (t.requests id)) ∧
    (∀ id, (s.requests id).requestStatus ≠ .pending → t.requests id = s.requests id) ∧
    ∃ receipt suffix, expectedFeePrefix env s asset price = .ok receipt ∧
      t.trace = receipt.trace ++ suffix ∧ (∀ e, e ∈ suffix → isFeeMarker e = false) ∧
      (consumed suffix).Nodup ∧
      (∀ id, id ∈ consumed suffix → id ∈ approved ∨ id ∈ rejected) ∧
      (∀ id, id ∈ consumed suffix → (s.requests id).requestStatus = .pending) ∧
      (∀ id, id ∈ consumed suffix → (t.requests id).requestStatus ≠ .pending) ∧
      (∀ id, id ∉ consumed suffix → t.requests id = s.requests id) ∧
      t.managementFeeLastUpdate = receipt.managementTime ∧
      t.performanceFeeLastUpdate = receipt.performanceTime := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨f,a,r,receipt,hreceipt,hftrace,hworld,hmtime,hptime,hdata,hf,hframe,ha,hr,ht⟩ :=
    processRequests_initial_fee env s t n approved rejected asset price hw hap hp h
  have hfs := feeData_structural env s f n hs hdata hf
  have happroved := handlerPath_recordRun env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h) approved f a hfs ha
  have hrejected := handlerPath_recordRun env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h) rejected a r happroved.closed hr
  have hrun := recordRun_trans env f a r n approved rejected happroved hrejected
  obtain ⟨suffix,htrace,hmarker,hnodup,hsubset,hpayload,hterminal,hpending,hfinal,huntouched⟩ := hrun.suffix
  have hreqF : f.requests = s.requests := hdata.2.1
  have hreqT : t.requests = r.requests := by rw [ht]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,receipt,suffix,hreceipt,?_,hmarker,hnodup,?_,?_,?_,?_,?_,?_⟩
  · rw [ht]; exact hrun.closed.2.1
  · rw [ht]; exact hrun.closed.1
  · rw [ht,hrun.config,hdata.1]
  · have hfr := callerFrame_trans s f r asset (hframe asset) (hrun.caller asset)
    rw [ht]
    rcases hfr with ⟨hprice,rest⟩
    refine ⟨?_,rest⟩
    intro other ho
    simp only [show (other == asset) = false by simpa using ho]
    exact hprice other ho
  · rw [ht]; simp
  · intro id
    rw [hreqT]
    simpa only [hreqF] using hpayload id
  · intro id hid
    rw [hreqT]
    have hh := hterminal id (by rwa [hreqF])
    simpa only [hreqF] using hh
  · rw [ht,htrace,hftrace]
  · intro id hid
    exact List.mem_append.mp (hsubset id hid)
  · intro id hid
    simpa only [hreqF] using hpending id hid
  · intro id hid
    rw [hreqT]; exact hfinal id hid
  · intro id hid
    rw [hreqT]
    simpa only [hreqF] using huntouched id hid
  · rw [ht,hrun.management,hmtime]
  · rw [ht,hrun.performance,hptime]

#print axioms handlerPath_recordRun
#print axioms processRequests_record_integrity

theorem handlerPath_success (body : Nat → Tx Unit) (ids : List Nat) (s t : State)
    (h : HandlerPath body ids s t) : iterate body ids s = .ok ((),t) := by
  induction h with
  | nil s => rfl
  | cons id ids s mid t hb hr ih =>
    simp only [iterate,Bind.bind,StateT.bind,Except.bind,hb]
    exact ih

theorem processRequests_decisions (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    ∃ receipt suffix, expectedFeePrefix env s asset price = .ok receipt ∧
      t.trace = receipt.trace ++ suffix ∧
      actualDecisions suffix = expectedDecisions s env.now asset approved rejected := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨f,a,r,receipt,hreceipt,hftrace,hworld,hmtime,hptime,hdata,hf,hframe,ha,hr,ht⟩ :=
    processRequests_initial_fee env s t n approved rejected asset price hw hap hp h
  have hfs := feeData_structural env s f n hs hdata hf
  have hah := handlerPath_success _ _ _ _ ha
  have hrh := handlerPath_success _ _ _ _ hr
  have hboth : (do _processApproved env approved asset price; _processRejected env rejected asset) f = .ok ((),r) := by
    simp only [_processApproved,Bind.bind,StateT.bind,Except.bind,hah]
    exact hrh
  obtain ⟨suffix,htrace,hdec⟩ := two_arrays_decisions env f r n price asset approved rejected hfs hp hboth
  refine ⟨receipt,suffix,hreceipt,?_,?_⟩
  · rw [ht,htrace,hftrace]
  · have hsel : ∀ ap ids statuses, selectDecisions f env.now asset ap ids statuses = selectDecisions s env.now asset ap ids statuses := by
      intro ap ids statuses
      apply selectDecisions_payload
      intro id
      rw [hdata.2.1]
      simp [Payload]
    simpa only [expectedDecisions,hdata.2.1,hsel] using hdec

#print axioms handlerPath_success
#print axioms processRequests_decisions

theorem processRequests_feeCorrect (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    FeeCorrect env s t asset price := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨f,a,r,receipt,hreceipt,hftrace,hworld,hmtime,hptime,hdata,hf,hframe,ha,hr,ht⟩ :=
    processRequests_initial_fee env s t n approved rejected asset price hw hap hp h
  have hfs := feeData_structural env s f n hs hdata hf
  have ar := handlerPath_recordRun env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h) approved f a hfs ha
  have rr := handlerPath_recordRun env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h) rejected a r ar.closed hr
  have aw := iterate_world env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h)
    (by intro id s t hi h; exact approveOne_world env s t n id price asset hi hp h) approved f a hfs (handlerPath_success _ _ _ _ ha)
  have rw := iterate_world env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h)
    (by intro id s t hi h; exact rejectOne_world env s t n id asset hi h) rejected a r ar.closed (handlerPath_success _ _ _ _ hr)
  obtain ⟨suffix,htrace,hreplay⟩ := worldRun_trans f a r ar.config aw rw
  have full := recordRun_trans env f a r n approved rejected ar rr
  obtain ⟨recordsSuffix,hrecords,hmarker,_⟩ := full.suffix
  have heq : recordsSuffix = suffix := List.append_cancel_left (hrecords.symm.trans htrace)
  rw [heq] at hmarker
  refine ⟨receipt,suffix,hreceipt,?_,hmarker,?_,?_,?_⟩
  · rw [ht,htrace,hftrace]
  · rw [ht,full.management,hmtime]
  · rw [ht,full.performance,hptime]
  · rw [ht,hreplay,hdata.1,hworld]

#print axioms processRequests_feeCorrect

theorem processRequests_balanced (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    actualPayments t.trace = expectedPayments s.config t.trace ∧ Balanced s t := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨v,f,a,r,_,hv,hf,ha,hr,ht⟩ := processRequests_success_phases env approved rejected asset price s t h
  have hvEq := validatePriceDeviation_success asset price s v hp (hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 asset) hv
  rw [hvEq] at hf
  have hnow := hw.2.2.2.2.2.1
  have hmt := hw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpt := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrate : s.config.managementFeeRate < wordLimit := by
    have hsmall := hw.2.2.2.2.2.2.2.2.2.1
    have hlarge : 2000 < wordLimit := by norm_num [wordLimit]
    omega
  have fdata := chargeFees_prefix env s f asset price hnow hmt hpt hrate hw.2.1 hf
  obtain ⟨receipt,_,_,_,_,_,hd⟩ := fdata
  have fc := chargeFees_closure env s f asset price hnow hmt hpt hrate hs.1 hf
  have hfs := feeData_structural env s f n hs hd fc.1
  have fe := chargeFees_effect env s f asset price hnow hmt hpt hrate hs.1 hf
  have ar := handlerPath_recordRun env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h) approved f a hfs ha
  have ae := iterate_effect env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h)
    (by intro id s t hi h; exact approveOne_effect env s t n id price asset hi hp h) approved f a hfs (handlerPath_success _ _ _ _ ha)
  have re := iterate_effect env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h)
    (by intro id s t hi h; exact rejectOne_effect env s t n id asset hi h) rejected a r ar.closed (handlerPath_success _ _ _ _ hr)
  obtain ⟨suffix,htrace,hpay,hsupply,hshares,hassets⟩ := effectRun_trans s f r hd.1 fe (effectRun_trans f a r ar.config ae re)
  have htr : t.trace = suffix := by rw [ht,htrace,hw.1,List.nil_append]
  refine ⟨by rwa [htr],?_,?_,?_⟩
  · rw [htr,ht]; exact hsupply
  · intro x; rw [htr,ht]; exact hshares x
  · intro token x hreg; rw [htr,ht]; exact hassets token x hreg.1 hreg.2

#print axioms processRequests_balanced
theorem processRequests_allowance (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    AllowanceAccounting s t := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨v,f,a,r,_,hv,hf,ha,hr,ht⟩ := processRequests_success_phases env approved rejected asset price s t h
  have hvEq := validatePriceDeviation_success asset price s v hp (hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 asset) hv
  rw [hvEq] at hf
  have hnow := hw.2.2.2.2.2.1
  have hmt := hw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpt := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrate : s.config.managementFeeRate < wordLimit := by
    have hsmall := hw.2.2.2.2.2.2.2.2.2.1
    have hlarge : 2000 < wordLimit := by norm_num [wordLimit]
    omega
  have fdata := chargeFees_prefix env s f asset price hnow hmt hpt hrate hw.2.1 hf
  obtain ⟨receipt,_,_,_,_,_,hd⟩ := fdata
  have fc := chargeFees_closure env s f asset price hnow hmt hpt hrate hs.1 hf
  have hfs := feeData_structural env s f n hs hd fc.1
  have fe := chargeFees_allow env s f asset price hnow hmt hpt hrate hs.1 hf
  have ar := handlerPath_recordRun env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h) approved f a hfs ha
  have ae := iterate_allow env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h)
    (by intro id s t hi h; exact approveOne_allow env s t n id price asset hi hp h) approved f a hfs (handlerPath_success _ _ _ _ ha)
  have re := iterate_allow env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h)
    (by intro id s t hi h; exact rejectOne_allow env s t n id asset hi h) rejected a r ar.closed (handlerPath_success _ _ _ _ hr)
  obtain ⟨suffix,htrace,hallow⟩ := allowRun_trans s f r hd.1 hs.1.2.2 fe (allowRun_trans f a r ar.config hfs.1.2.2 ae re)
  have htr : t.trace = suffix := by rw [ht,htrace,hw.1,List.nil_append]
  intro token owner spender hreg hnz
  rw [htr,ht]
  have hdebit : (debitSum s.config suffix token owner spender : Int) =
      (suffix.map fun e => match e with
        | .redemption _ rr _ _ payout => if token = rr.asset ∧ owner = s.config.portfolioSafe ∧ spender = s.config.self then (payout : Int) else 0
        | _ => 0).sum := by
    clear htrace hallow htr
    induction suffix with
    | nil => rfl
    | cons e es ih =>
      cases e <;> simp [debitSum] at ih ⊢
      all_goals exact ih
  have hh := hallow token owner spender hreg hnz
  rw [hdebit] at hh
  simp only [assetAllowance] at hh ⊢
  split_ifs at hh ⊢ with hinf
  · exact hh
  · rw [hh]
    congr 2

#print axioms processRequests_allowance
theorem processRequests_trace_correct (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    ∀ e, e ∈ t.trace → ConversionCorrect s.config price e ∧ TraceRequestCorrect s t e := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨v,f,a,r,_,hv,hf,ha,hr,ht⟩ := processRequests_success_phases env approved rejected asset price s t h
  have hvEq := validatePriceDeviation_success asset price s v hp (hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 asset) hv
  rw [hvEq] at hf
  have hnow := hw.2.2.2.2.2.1
  have hmt := hw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpt := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrate : s.config.managementFeeRate < wordLimit := by
    have hsmall := hw.2.2.2.2.2.2.2.2.2.1
    have hlarge : 2000 < wordLimit := by norm_num [wordLimit]
    omega
  have fdata := chargeFees_prefix env s f asset price hnow hmt hpt hrate hw.2.1 hf
  obtain ⟨receipt,_,_,_,_,_,hd⟩ := fdata
  have fc := chargeFees_closure env s f asset price hnow hmt hpt hrate hs.1 hf
  have hfs := feeData_structural env s f n hs hd fc.1
  have ar := handlerPath_recordRun env (approveOne env asset price) n
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h) approved f a hfs ha
  have ae := iterate_correct env (approveOne env asset price) n price
    (by intro id s t hi h; exact approveOne_record env s t n id price asset hi hp h)
    (by intro id s t hi h; exact approveOne_correct env s t n id price asset hi hp h) approved f a hfs (handlerPath_success _ _ _ _ ha)
  have re := iterate_correct env (rejectOne env asset) n price
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h)
    (by intro id s t hi h; exact rejectOne_correct env s t n id price asset hi h) rejected a r ar.closed (handlerPath_success _ _ _ _ hr)
  have rr := handlerPath_recordRun env (rejectOne env asset) n
    (by intro id s t hi h; exact rejectOne_record env s t n id asset hi h) rejected a r ar.closed hr
  obtain ⟨_,_,_,_,_,hpA,hsA,_⟩ := ar.suffix
  obtain ⟨_,_,_,_,_,_,hsR,_⟩ := rr.suffix
  rw [ar.config] at re
  obtain ⟨suffix,htrace,hcert⟩ := correctRun_trans f.config price f a r hpA hsA hsR ae re
  obtain ⟨fees,hfees,honly⟩ := chargeFees_feeTrace env s f asset price hnow hmt hpt hrate hf
  have htr : t.trace = fees ++ suffix := by rw [ht,htrace,hfees,hw.1,List.nil_append]
  intro e he
  rw [htr] at he
  rcases List.mem_append.mp he with he | he
  · have hh := honly e he
    cases e <;> simp_all [feeOnly,ConversionCorrect,TraceRequestCorrect]
  · obtain ⟨hc,hreq,hpending⟩ := hcert e he
    refine ⟨by simpa only [hd.1] using hc,?_⟩
    have hreqF : f.requests = s.requests := hd.2.1
    have hreqT : t.requests = r.requests := by rw [ht]
    cases e <;> simp only [TraceRequestCorrect,hreqF,hreqT] at hreq ⊢ <;> exact hreq

#print axioms processRequests_trace_correct

theorem processRequests_receipt_feeOnly (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t))
    (receipt : FeeReceipt) (hreceipt : expectedFeePrefix env s asset price = .ok receipt) :
    ∀ e, e ∈ receipt.trace → feeOnly e := by
  have hs := wellFormed_structural env s n hw hap
  obtain ⟨v,f,a,r,_,hv,hf,_,_,_⟩ := processRequests_success_phases env approved rejected asset price s t h
  rw [validatePriceDeviation_success asset price s v hp (hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 asset) hv] at hf
  have hn := hw.2.2.2.2.2.1
  have hm := hw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hr : s.config.managementFeeRate < wordLimit := by
    have hsmall := hw.2.2.2.2.2.2.2.2.2.1
    have hlarge : 2000 < wordLimit := by norm_num [wordLimit]
    omega
  obtain ⟨other,ho,htrace,_,_,_,_⟩ := chargeFees_prefix env s f asset price hn hm ht hr hw.2.1 hf
  have heq : other = receipt := Except.ok.inj (ho.symm.trans hreceipt)
  obtain ⟨fees,hfees,honly⟩ := chargeFees_feeTrace env s f asset price hn hm ht hr hf
  have htr : fees = receipt.trace := by rw [heq,hw.1,List.nil_append] at htrace; rw [hw.1,List.nil_append] at hfees; exact hfees.symm.trans htrace
  rwa [htr] at honly

theorem trace_consumed_status (before after : State) (xs : List Effect)
    (hc : ∀ e, e ∈ xs → TraceRequestCorrect before after e) :
    ∀ id, id ∈ consumed xs → (after.requests id).requestStatus = .processed ∨ (after.requests id).requestStatus = .rejected := by
  induction xs with
  | nil => simp [consumed]
  | cons e es ih =>
    have he := hc e (by simp)
    have hr := ih (by intro e he; exact hc e (by simp [he]))
    intro id hid
    cases e <;> simp only [consumed,List.nil_append,List.cons_append,List.mem_cons] at hid
    all_goals first | exact hr id hid | (rcases hid with rfl | hid)
    all_goals first | exact hr id hid | exact Or.inl he.2.2 | exact Or.inr he.2

/-- Complete accounting conjunction for actual processRequests execution. The
premises are exactly the generated task's original applicability/range premises;
all component facts are derived from successful source execution. -/
theorem settlement_accounting (env : Environment) (s t : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat)
    (hw : WellFormed env s n) (hap : ExternalApplicability env s) (hp : price < wordLimit)
    (h : processRequests env approved rejected asset price s = .ok ((),t)) :
    SettlementAccounting env s t n approved rejected asset price := by
  obtain ⟨hrc,_,hcfg,hcaller,hprice,hpayload,hterminal,receipt,suffix,hreceipt,htrace,hmarker,hnodup,hsubset,_,_,huntouched,_⟩ :=
    processRequests_record_integrity env s t n approved rejected asset price hw hap hp h
  have hfees := processRequests_receipt_feeOnly env s t n approved rejected asset price hw hap hp h receipt hreceipt
  have hcons : consumed t.trace = consumed suffix := by rw [htrace,consumed_append,feeOnly_consumed receipt.trace hfees,List.nil_append]
  obtain ⟨other,rest,ho,htr,hdec⟩ := processRequests_decisions env s t n approved rejected asset price hw hap hp h
  have hother : other = receipt := Except.ok.inj (ho.symm.trans hreceipt)
  have hrest : rest = suffix := by rw [hother] at htr; exact List.append_cancel_left (htr.symm.trans htrace)
  have hdecision : actualDecisions t.trace = expectedDecisions s env.now asset approved rejected := by
    rw [htrace,actualDecisions_append,feeOnly_decisions receipt.trace hfees,List.nil_append]
    simpa only [hrest] using hdec
  have hbalance := processRequests_balanced env s t n approved rejected asset price hw hap hp h
  have hcorrect := processRequests_trace_correct env s t n approved rejected asset price hw hap hp h
  refine ⟨hdecision,processRequests_feeCorrect env s t n approved rejected asset price hw hap hp h,
    hcaller,hbalance.1,hbalance.2,processRequests_allowance env s t n approved rejected asset price hw hap hp h,
    hrc,?_,?_,hcorrect,hpayload,?_,?_,?_,hcfg,hprice⟩
  · rwa [hcons]
  · intro id hid; exact hsubset id (by rwa [hcons] at hid)
  · intro id hid; exact congrArg UserRequest.requestStatus (hterminal id hid)
  · exact trace_consumed_status s t t.trace (by intro e he; exact (hcorrect e he).2)
  · intro id hid; exact huntouched id (by rwa [hcons] at hid)

#print axioms settlement_accounting

#print axioms Mint_floor_bounds
#print axioms Out_floor_bounds
#print axioms rollback_of_error
#print axioms transaction_success
#print axioms iterate_append
#print axioms iterate_invariant
end Benchmark.Cases.KPK.SharesSettlementAccounting
