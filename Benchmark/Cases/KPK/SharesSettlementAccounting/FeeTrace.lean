import Benchmark.Cases.KPK.SharesSettlementAccounting.AllowanceTrace

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def feeOnly : Effect → Prop
  | .mint _ _ | .management _ | .performance _ | .moduleCall _ _ _ _ _ _ => True
  | _ => False

def FeeTraceRun (s t : State) : Prop :=
  ∃ suffix, t.trace = s.trace ++ suffix ∧ (∀ e, e ∈ suffix → feeOnly e)

theorem feeTraceRun_nil (s : State) : FeeTraceRun s s := ⟨[],by simp,by simp⟩

theorem feeTraceRun_trans (s m t : State) (h1 : FeeTraceRun s m) (h2 : FeeTraceRun m t) : FeeTraceRun s t := by
  obtain ⟨first,hfirst,h1⟩ := h1
  obtain ⟨second,hsecond,h2⟩ := h2
  exact ⟨first ++ second,by rw [hsecond,hfirst,List.append_assoc],by intro e he; rcases List.mem_append.mp he with he | he; exact h1 e he; exact h2 e he⟩

theorem managementPhase_feeTrace (env : Environment) (s t : State)
    (hn : env.now < wordLimit) (ht : s.managementFeeLastUpdate < wordLimit)
    (hr : s.config.managementFeeRate < wordLimit)
    (h : managementPhase env s.config s = .ok ((),t)) : FeeTraceRun s t := by
  have hc := managementPhase_success env s t hn ht hr h
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  refine ⟨managementTrace env s,hd.2.2.2.2,?_⟩
  intro e he
  unfold managementTrace at he
  split_ifs at he <;> simp only [List.mem_cons,List.not_mem_nil,List.mem_append,false_or,or_false,or_assoc] at he
  all_goals rcases he with rfl | rfl <;> trivial

theorem performanceFee_feeTrace (env : Environment) (s t : State) (price elapsed fee : Nat)
    (h : _chargePerformanceFee env price elapsed s = .ok (fee,t)) : FeeTraceRun s t := by
  rcases performanceFee_success env s t price elapsed fee h with hz | hm
  · rw [hz.2.2]; exact feeTraceRun_nil s
  · obtain ⟨net,cells,m,_,_,_,_,_,_,hfeeB,hmint,_,ht⟩ := hm
    rw [ht]
    refine ⟨[.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee] ++ (if fee > 0 then [.mint s.config.feeReceiver fee] else []) ++ [.performance fee],?_,?_⟩
    · simp only [performanceIssuedState,optionalMint_trace,moduleStateUpdate,List.append_assoc]
    · intro e he
      split_ifs at he <;> simp only [List.mem_cons,List.not_mem_nil,List.mem_append,false_or,or_false,or_assoc] at he
      all_goals rcases he with rfl | rfl | rfl <;> trivial

theorem performancePhase_feeTrace (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (ht : s.performanceFeeLastUpdate < wordLimit)
    (h : performancePhase env s.config asset price s = .ok ((),t)) : FeeTraceRun s t := by
  have hc := performancePhase_success env s t asset price hn ht h
  by_cases ha : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true ∧ env.now - s.performanceFeeLastUpdate > 21600
  · rw [if_pos ha] at hc
    obtain ⟨fee,hfee⟩ := hc.2
    exact performanceFee_feeTrace env {s with performanceFeeLastUpdate := env.now} t price (env.now - s.performanceFeeLastUpdate) fee hfee
  · rw [if_neg ha] at hc
    rw [hc.2]; exact feeTraceRun_nil s

theorem chargeFees_feeTrace (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (hmt : s.managementFeeLastUpdate < wordLimit)
    (hpt : s.performanceFeeLastUpdate < wordLimit) (hr : s.config.managementFeeRate < wordLimit)
    (h : _chargeFees env asset price s = .ok ((),t)) : FeeTraceRun s t := by
  rw [chargeFees_phase_equation] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h1
  obtain ⟨u,m,hm,hp⟩ := tx_bind_ok _ _ _ _ _ h1
  cases u
  have hc := managementPhase_success env s m hn hmt hr hm
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  rw [← hd.1.1] at hp
  exact feeTraceRun_trans s m t (managementPhase_feeTrace env s m hn hmt hr hm)
    (performancePhase_feeTrace env m t asset price hn (by rw [hd.2.2.1]; exact hpt) hp)

theorem feeOnly_decisions (xs : List Effect) (h : ∀ e, e ∈ xs → feeOnly e) : actualDecisions xs = [] := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hr := ih (by intro e he; exact h e (by simp [he]))
    cases e <;> simp_all [feeOnly,actualDecisions]

theorem feeOnly_consumed (xs : List Effect) (h : ∀ e, e ∈ xs → feeOnly e) : consumed xs = [] := by
  rw [consumed_decisions,feeOnly_decisions xs h]; rfl

theorem feeOnly_debit (cfg : Configuration) (xs : List Effect) (h : ∀ e, e ∈ xs → feeOnly e)
    (token owner spender : Address) : debitSum cfg xs token owner spender = 0 := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hr := ih (by intro e he; exact h e (by simp [he]))
    cases e <;> simp_all [feeOnly,debitSum]

#print axioms chargeFees_feeTrace

theorem performanceFee_allowance_frame (env : Environment) (s t : State) (price elapsed fee : Nat)
    (hi : FeeInvariant env s) (h : _chargePerformanceFee env price elapsed s = .ok (fee,t)) :
    ∀ token owner spender, (s.config.assets token).asset = token → token ≠ 0 →
      assetAllowance t token owner spender = assetAllowance s token owner spender := by
  rcases performanceFee_success env s t price elapsed fee h with hz | hm
  · rw [hz.2.2]; intro _ _ _ _ _; rfl
  · obtain ⟨net,cells,m,_,_,_,_,htoken,_,_,_,_,ht⟩ := hm
    intro token owner spender hreg hnz
    rw [ht]
    simp only [performanceIssuedState,assetAllowance]
    have hx := module_registered_allowance_frame s env hi.2.1 s.config.performanceFeeModule token owner spender htoken hreg hnz cells
    by_cases hfee : fee > 0
    · simpa only [optionalMintState,if_pos hfee,mintedState,shareWrite,supplyWrite,assetAllowance,moduleStateUpdate] using hx
    · simpa only [optionalMintState,if_neg hfee,assetAllowance,moduleStateUpdate] using hx

theorem performancePhase_allowance_frame (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (ht : s.performanceFeeLastUpdate < wordLimit) (hi : FeeInvariant env s)
    (h : performancePhase env s.config asset price s = .ok ((),t)) :
    ∀ token owner spender, (s.config.assets token).asset = token → token ≠ 0 →
      assetAllowance t token owner spender = assetAllowance s token owner spender := by
  have hc := performancePhase_success env s t asset price hn ht h
  by_cases ha : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true ∧ env.now - s.performanceFeeLastUpdate > 21600
  · rw [if_pos ha] at hc
    obtain ⟨fee,hfee⟩ := hc.2
    exact performanceFee_allowance_frame env {s with performanceFeeLastUpdate := env.now} t price (env.now - s.performanceFeeLastUpdate) fee hi hfee
  · rw [if_neg ha] at hc
    rw [hc.2]; intro _ _ _ _ _; rfl

theorem chargeFees_allowance_frame (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (hmt : s.managementFeeLastUpdate < wordLimit)
    (hpt : s.performanceFeeLastUpdate < wordLimit) (hr : s.config.managementFeeRate < wordLimit)
    (hi : FeeInvariant env s)
    (h : _chargeFees env asset price s = .ok ((),t)) :
    ∀ token owner spender, (s.config.assets token).asset = token → token ≠ 0 →
      assetAllowance t token owner spender = assetAllowance s token owner spender := by
  rw [chargeFees_phase_equation] at h
  obtain ⟨st,m0,hget,h1⟩ := tx_bind_ok _ _ _ _ _ h
  have hg := tx_get_state _ _ _ hget
  rw [hg.1,hg.2] at h1
  obtain ⟨u,m,hm,hp⟩ := tx_bind_ok _ _ _ _ _ h1
  cases u
  have hc := managementPhase_success env s m hn hmt hr hm
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  rw [← hd.1.1] at hp
  have hiM := (managementPhase_closure env s m hn hmt hr hi hm).1
  have hpA := performancePhase_allowance_frame env m t asset price hn (by rw [hd.2.2.1]; exact hpt) hiM hp
  intro token owner spender hreg hnz
  rw [hpA token owner spender (by rwa [hd.1.1]) hnz]
  simp only [assetAllowance,hd.2.1]

theorem chargeFees_allow (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (hmt : s.managementFeeLastUpdate < wordLimit)
    (hpt : s.performanceFeeLastUpdate < wordLimit) (hr : s.config.managementFeeRate < wordLimit)
    (hi : FeeInvariant env s) (h : _chargeFees env asset price s = .ok ((),t)) : AllowRun s t := by
  obtain ⟨suffix,htrace,honly⟩ := chargeFees_feeTrace env s t asset price hn hmt hpt hr h
  have hf := chargeFees_allowance_frame env s t asset price hn hmt hpt hr hi h
  refine ⟨suffix,htrace,?_⟩
  intro token owner spender hreg hnz
  rw [hf token owner spender hreg hnz]
  split_ifs <;> simp [feeOnly_debit s.config suffix honly token owner spender, *]

#print axioms chargeFees_allow
end Benchmark.Cases.KPK.SharesSettlementAccounting
