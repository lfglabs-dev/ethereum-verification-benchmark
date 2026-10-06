import Benchmark.Cases.KPK.SharesSettlementAccounting.TraceEffects

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem managementPhase_effect (env : Environment) (s t : State)
    (hn : env.now < wordLimit) (ht : s.managementFeeLastUpdate < wordLimit)
    (hr : s.config.managementFeeRate < wordLimit) (hi : FeeInvariant env s)
    (h : managementPhase env s.config s = .ok ((),t)) : EffectRun s t := by
  have hc := managementPhase_success env s t hn ht hr h
  have he := managementPhase_accounting env s t hn ht hr hi.1 h
  have hd := managementPrefix_data env s
  rw [← hc.1] at hd
  have htrace : t.trace = s.trace ++ managementTrace env s := hd.2.2.2.2
  have hpays : expectedPayments s.config (managementTrace env s) =
      if ExpectedManagement s env.now > 0 then [.mint s.config.feeReceiver (ExpectedManagement s env.now)] else [] := by
    unfold managementTrace
    by_cases ha : s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600
    · rw [if_pos ha]
      by_cases hg : ExpectedManagement s env.now > 0 <;> simp [expectedPayments,hg]
    · rw [if_neg ha]
      simp [expectedPayments,ExpectedManagement,ha]
  refine ⟨managementTrace env s,htrace,?_,?_,?_,?_⟩
  · rw [hpays]
    unfold managementTrace
    by_cases ha : s.config.managementFeeRate > 0 ∧ env.now - s.managementFeeLastUpdate > 21600
    · rw [if_pos ha]
      by_cases hg : ExpectedManagement s env.now > 0 <;> simp [actualPayments,hg]
    · rw [if_neg ha]; simp [actualPayments,ExpectedManagement,ha]
  · rw [he.1,hpays]
    by_cases hg : ExpectedManagement s env.now > 0
    · simp [hg,supplyEffect,Int.natCast_add]
    · have hz : ExpectedManagement s env.now = 0 := by omega
      simp [hg,hz]
  · intro x
    rw [he.2.1 x,hpays]
    by_cases hg : ExpectedManagement s env.now > 0
    · simp [hg,shareEffect,indicator,Int.natCast_add]
    · have hz : ExpectedManagement s env.now = 0 := by omega
      simp [hg,hz]
  · intro token x _ _
    have hb : assetBalance t token x = assetBalance s token x := by simp only [assetBalance,hd.2.1]
    rw [hb,hpays]
    split_ifs <;> simp [assetEffect]

theorem performanceFee_effect (env : Environment) (s t : State) (price elapsed fee : Nat)
    (hi : FeeInvariant env s)
    (h : _chargePerformanceFee env price elapsed s = .ok (fee,t)) : EffectRun s t := by
  rcases performanceFee_success env s t price elapsed fee h with hz | hm
  · rw [hz.2.2]; exact effectRun_nil s
  · obtain ⟨net,cells,m,_,_,_,_,htoken,_,hfeeB,hmint,_,ht⟩ := hm
    let c : State := {moduleStateUpdate s s.config.performanceFeeModule cells with trace := s.trace ++ [.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee]}
    have he := optionalMint_effects c m s.config.feeReceiver fee hi.1 hfeeB hmint
    have hmeq := (optionalMint_success c m s.config.feeReceiver fee hfeeB hmint).2
    have ht' : t = {m with trace := m.trace ++ [.performance fee]} := by
      rw [ht]; simp only [performanceIssuedState,c,← hmeq]
    have hx : ∀ token x, (s.config.assets token).asset = token → token ≠ 0 → assetBalance c token x = assetBalance s token x := by
      intro token x hreg hnz
      have hne : token ≠ s.config.performanceFeeModule := by
        intro hh
        have hb := (hi.2.1 token hreg hnz).2.1
        rw [hh,htoken] at hb
        contradiction
      have hval : token.val ≠ s.config.performanceFeeModule.val := by
        intro he; exact hne (Verity.Core.Address.ext he)
      simp [assetBalance,c,moduleStateUpdate,hval]
    have hd := optionalMint_data c s.config.feeReceiver fee
    rw [← hmeq] at hd
    have htrace : t.trace = s.trace ++ ([.moduleCall s.config.performanceFeeModule price elapsed s.config.performanceFeeRate net fee] ++ (if fee > 0 then [.mint s.config.feeReceiver fee] else []) ++ [.performance fee]) := by
      rw [ht',hmeq,optionalMint_trace]
      simp only [c,List.append_assoc]
    refine ⟨_,htrace,?_,?_,?_,?_⟩
    · split_ifs with hf <;> simp [actualPayments,expectedPayments,hf]
    · rw [ht']
      change (totalSupply m : Int) - totalSupply s = _
      rw [he.1]
      change ((totalSupply s + fee : Nat) : Int) - totalSupply s = _
      by_cases hf : fee > 0
      · simp [expectedPayments,supplyEffect,hf,Int.natCast_add]
      · have hz : fee = 0 := by omega
        simp [expectedPayments,supplyEffect,hf,hz]
    · intro x
      rw [ht']
      change (shareBalance m x : Int) - shareBalance s x = _
      rw [he.2.1 x]
      change ((shareBalance s x + if x = s.config.feeReceiver then fee else 0 : Nat) : Int) - shareBalance s x = _
      by_cases hf : fee > 0
      · simp [expectedPayments,shareEffect,indicator,hf,Int.natCast_add]
      · have hz : fee = 0 := by omega
        simp [expectedPayments,shareEffect,indicator,hf,hz]
    · intro token x hreg hnz
      have hb : assetBalance t token x = assetBalance s token x := by
        rw [ht']; simp only [assetBalance,hd.2.1]
        exact hx token x hreg hnz
      rw [hb]
      split_ifs with hf <;> simp [expectedPayments,assetEffect,hf]


theorem performancePhase_effect (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (ht : s.performanceFeeLastUpdate < wordLimit) (hi : FeeInvariant env s)
    (h : performancePhase env s.config asset price s = .ok ((),t)) : EffectRun s t := by
  have hc := performancePhase_success env s t asset price hn ht h
  by_cases ha : (s.config.performanceFeeRate > 0 && (s.config.assets asset).isFeeModuleAsset) = true ∧ env.now - s.performanceFeeLastUpdate > 21600
  · rw [if_pos ha] at hc
    obtain ⟨fee,hfee⟩ := hc.2
    exact performanceFee_effect env {s with performanceFeeLastUpdate := env.now} t price (env.now - s.performanceFeeLastUpdate) fee hi hfee
  · rw [if_neg ha] at hc
    rw [hc.2]; exact effectRun_nil s

theorem chargeFees_effect (env : Environment) (s t : State) (asset : Address) (price : Nat)
    (hn : env.now < wordLimit) (hmt : s.managementFeeLastUpdate < wordLimit)
    (hpt : s.performanceFeeLastUpdate < wordLimit) (hr : s.config.managementFeeRate < wordLimit)
    (hi : FeeInvariant env s)
    (h : _chargeFees env asset price s = .ok ((),t)) : EffectRun s t := by
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
  have hme := managementPhase_effect env s m hn hmt hr hi hm
  have hpe := performancePhase_effect env m t asset price hn (by rw [hd.2.2.1]; exact hpt) hmc.1 hp
  exact effectRun_trans s m t hd.1.1 hme hpe

#print axioms managementPhase_effect
#print axioms performanceFee_effect
#print axioms chargeFees_effect
end Benchmark.Cases.KPK.SharesSettlementAccounting
