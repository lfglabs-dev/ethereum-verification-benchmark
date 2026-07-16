import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity
open Verity.EVM.Uint256

def StatePreserving {α : Type} (m : Contract α) : Prop :=
  ∀ s, m.runState s = s

/-- Mapping writes may change decoded map fields, but not scalar storage. -/
private def StoragePreserving {α : Type} (m : Contract α) : Prop :=
  ∀ s, (m.runState s).storage = s.storage

/-- CFA accounting writes only the decoded account slots 0 through 4.  This
frame deliberately keeps the Host/source mapping environment available at the
touched endpoints without expanding the public wrappers symbolically. -/
private def AccountEnvironmentPreserving {α : Type} (m : Contract α) : Prop :=
  ∀ s slotIndex account, 4 < slotIndex →
    (m.runState s).storageMap slotIndex account = s.storageMap slotIndex account

private theorem account_environment_preserving_bind {α β : Type} (m : Contract α)
    (f : α → Contract β) (hm : AccountEnvironmentPreserving m)
    (hf : ∀ a, AccountEnvironmentPreserving (f a)) :
    AccountEnvironmentPreserving (Verity.bind m f) := by
  intro s slotIndex account hslot
  unfold Contract.runState Verity.bind
  cases h : m s
  next a t =>
    have ht : t.storageMap slotIndex account = s.storageMap slotIndex account := by
      have hs := hm s slotIndex account hslot
      simpa [Contract.runState, h] using hs
    cases htail : f a t
    next b u =>
      have hu : u.storageMap slotIndex account = t.storageMap slotIndex account := by
        have htail' := hf a t slotIndex account hslot
        simpa [Contract.runState, htail] using htail'
      simpa [Contract.runState, h, htail] using hu.trans ht
    next msg u => simp [Contract.runState, h, htail]
  next msg t => simp [Contract.runState, h]

private theorem account_environment_preserving_require (cond : Bool) (msg : String) :
    AccountEnvironmentPreserving (Verity.require cond msg) := by
  intro s slotIndex account hslot
  cases cond <;> rfl

private theorem account_environment_preserving_pure {α : Type} (a : α) :
    AccountEnvironmentPreserving (Verity.pure a : Contract α) := by
  intro s slotIndex account hslot
  rfl

private theorem account_environment_preserving_getStorage (sl : StorageSlot Uint256) :
    AccountEnvironmentPreserving (getStorage sl) := by
  intro s slotIndex account hslot
  rfl

private theorem account_environment_preserving_getMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) :
    AccountEnvironmentPreserving (getMapping sl key) := by
  intro s slotIndex account hslot
  rfl

private theorem account_environment_preserving_getMapping2
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) :
    AccountEnvironmentPreserving (getMapping2 sl left right) := by
  intro s slotIndex account hslot
  rfl

private theorem account_environment_preserving_setMapping2
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) (value : Uint256) :
    AccountEnvironmentPreserving (setMapping2 sl left right value) := by
  intro s slotIndex account hslot
  rfl

private theorem account_environment_preserving_setMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256)
    (hwrite : sl.slot ≤ 4) :
    AccountEnvironmentPreserving (setMapping sl key value) := by
  intro s slotIndex account hslot
  have hne : slotIndex ≠ sl.slot := by omega
  change (if slotIndex == sl.slot && account == key then value else s.storageMap slotIndex account) =
    s.storageMap slotIndex account
  simp [hne]

private theorem state_preserving_account_environment {α : Type} {m : Contract α}
    (h : StatePreserving m) : AccountEnvironmentPreserving m := by
  intro s slotIndex account hslot
  exact congrFun (congrFun (congrArg ContractState.storageMap (h s)) slotIndex) account

private def EndpointEnvironmentFrame (base post : ContractState) : Prop :=
  post.storage = base.storage ∧
  ∀ slotIndex account, 4 < slotIndex →
    post.storageMap slotIndex account = base.storageMap slotIndex account

private theorem endpoint_environment_frame_of_preserving {α : Type} (m : Contract α)
    (hstorage : StoragePreserving m) (hmaps : AccountEnvironmentPreserving m) (s : ContractState) :
    EndpointEnvironmentFrame s (m.runState s) :=
  ⟨hstorage s, hmaps s⟩

private theorem storage_preserving_bind {α β : Type} (m : Contract α) (f : α → Contract β)
    (hm : StoragePreserving m) (hf : ∀ a, StoragePreserving (f a)) :
    StoragePreserving (Verity.bind m f) := by
  intro s
  unfold Contract.runState Verity.bind
  cases h : m s
  next a t =>
    have ht : t.storage = s.storage := by
      have hs := hm s
      simp [Contract.runState, h] at hs
      exact hs
    cases htail : f a t
    next b u =>
      have hu : u.storage = t.storage := by
        have htail' := hf a t
        simpa [Contract.runState, htail] using htail'
      simpa [Contract.runState, h, htail] using hu.trans ht
    next msg u => simp [Contract.runState, h, htail]
  next msg t => simp [Contract.runState, h]

private theorem storage_preserving_require (cond : Bool) (msg : String) :
    StoragePreserving (Verity.require cond msg) := by
  intro s
  cases cond <;> rfl

private theorem storage_preserving_pure {α : Type} (a : α) :
    StoragePreserving (Verity.pure a : Contract α) := by
  intro s
  rfl

private theorem storage_preserving_getStorage (sl : StorageSlot Uint256) :
    StoragePreserving (getStorage sl) := by
  intro s
  rfl

private theorem storage_preserving_getMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) :
    StoragePreserving (getMapping sl key) := by
  intro s
  rfl

private theorem storage_preserving_getMapping2
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) :
    StoragePreserving (getMapping2 sl left right) := by
  intro s
  rfl

private theorem storage_preserving_setMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) :
    StoragePreserving (setMapping sl key value) := by
  intro s
  rfl

private theorem storage_preserving_setMapping2
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) (value : Uint256) :
    StoragePreserving (setMapping2 sl left right value) := by
  intro s
  rfl

private theorem state_preserving_storage {α : Type} {m : Contract α}
    (h : StatePreserving m) : StoragePreserving m := by
  intro s
  exact congrArg ContractState.storage (h s)

private theorem preserving_bind {α β : Type} (m : Contract α) (f : α → Contract β)
    (hm : StatePreserving m) (hf : ∀ a, StatePreserving (f a)) :
    StatePreserving (Verity.bind m f) := by
  intro s
  unfold Contract.runState Verity.bind
  cases h : m s
  next a t =>
    have ht : t = s := by
      have hs := hm s
      simp [Contract.runState, h] at hs
      exact hs
    subst t
    simpa [Contract.runState] using hf a s
  next msg t => rfl

private theorem preserving_require (cond : Bool) (msg : String) :
    StatePreserving (Verity.require cond msg) := by
  intro s
  cases cond <;> simp [Verity.require, Contract.runState]

private theorem preserving_pure {α : Type} (a : α) : StatePreserving (Verity.pure a : Contract α) := by
  intro s
  rfl

private theorem preserving_getStorage (sl : StorageSlot Uint256) :
    StatePreserving (getStorage sl) := by
  intro s
  simp [getStorage, Contract.runState]

private theorem preserving_getMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) :
    StatePreserving (getMapping sl key) := by
  intro s
  simp [getMapping, Contract.runState]

private theorem preserving_getMapping2
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) :
    StatePreserving (getMapping2 sl left right) := by
  intro s
  simp [getMapping2, Contract.runState]

private theorem canonical_preserving (account : Address) :
    StatePreserving (SuperfluidCFA._requireCanonicalAccount account) := by
  unfold SuperfluidCFA._requireCanonicalAccount
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro timestamp
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro rate
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro deposit
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro owed
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  exact preserving_require _ _

private theorem canonical_storage_preserving (account : Address) :
    StoragePreserving (SuperfluidCFA._requireCanonicalAccount account) := by
  unfold SuperfluidCFA._requireCanonicalAccount
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  exact storage_preserving_require _ _

private theorem success_exists {α : Type} (r : ContractResult α)
    (h : r.isSuccess = true) :
    ∃ a s, r = ContractResult.success a s := by
  cases r with
  | success a s => exact ⟨a, s, rfl⟩
  | _ => simp [ContractResult.isSuccess] at h

private theorem unit_success_eq {c : Contract Unit} {s : ContractState}
    (h : (c.run s).isSuccess = true) :
    c.run s = ContractResult.success () (c.run s).snd := by
  rcases success_exists (c.run s) h with ⟨a, s', hs⟩
  cases a
  simpa [hs]

private theorem bind_success_elim {α β : Type}
    (m : Contract α) (k : α → Contract β) (s t : ContractState) (b : β)
    (h : (Verity.bind m k).run s = ContractResult.success b t) :
    ∃ a s₁, m.run s = ContractResult.success a s₁ ∧
      (k a).run s₁ = ContractResult.success b t := by
  have hraw := Contract.eq_of_run_success h
  unfold Verity.bind at hraw
  cases hm : m s with
  | success a s₁ =>
      refine ⟨a, s₁, ?_, ?_⟩
      · simp [Contract.run, hm]
      · have hkraw : k a s₁ = ContractResult.success b t := by
          simpa [hm] using hraw
        simpa [Contract.run, hkraw]
  | _ => simp [hm] at hraw

private theorem preserving_bind_tail {α β : Type}
    (m : Contract α) (k : α → Contract β) (s t : ContractState) (b : β)
    (hm : StatePreserving m)
    (h : (Verity.bind m k).run s = ContractResult.success b t) :
    ∃ a, (k a).run s = ContractResult.success b t := by
  rcases bind_success_elim m k s t b h with ⟨a, s₁, hrun, htail⟩
  have hs₁ : s₁ = s := by
    have hp := hm s
    rw [Contract.runState_eq_snd_run, hrun] at hp
    simpa using hp
  subst s₁
  exact ⟨a, htail⟩

private theorem success_state_eq {α : Type} (m : Contract α) (s t : ContractState) (a : α)
    (h : m.run s = ContractResult.success a t) :
    t = m.runState s := by
  rw [Contract.runState_eq_snd_run, h]
  rfl

private theorem getMapping_value_of_success
    (sl : StorageSlot (Address → Uint256)) (key : Address)
    (s t : ContractState) (value : Uint256)
    (h : (getMapping sl key).run s = ContractResult.success value t) :
    value = s.storageMap sl.slot key := by
  have hraw := Contract.eq_of_run_success h
  change ContractResult.success (s.storageMap sl.slot key) s =
    ContractResult.success value t at hraw
  injection hraw with hvalue _
  exact hvalue.symm

private theorem settle_success
    (s t : ContractState) (account : Address) (delta : Uint256)
    (h : (SuperfluidCFA._settleBalance account delta).run s =
      ContractResult.success () t) :
    t = (setMapping SuperfluidCFA.sharedSettledBalances account
      (add (s.storageMap 0 account) delta)).runState s := by
  by_cases hsign : ((s.storageMap 0 account <
      57896044618658097711785492504343953926634992332820282019728792003956564819968) =
    (delta < 57896044618658097711785492504343953926634992332820282019728792003956564819968))
  by_cases hover : ((add (s.storageMap 0 account) delta <
      57896044618658097711785492504343953926634992332820282019728792003956564819968) =
    (delta < 57896044618658097711785492504343953926634992332820282019728792003956564819968))
  all_goals simp_all [SuperfluidCFA._settleBalance, SuperfluidCFA.sharedSettledBalances,
    Verity.bind, Bind.bind, Verity.require, getMapping, setMapping,
    Verity.pure, Pure.pure, Contract.run, Contract.runState]

private theorem settle_storage_preserving (account : Address) (delta : Uint256) :
    StoragePreserving (SuperfluidCFA._settleBalance account delta) := by
  unfold SuperfluidCFA._settleBalance
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  dsimp
  split
  · apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    exact storage_preserving_setMapping _ _ _
  · apply storage_preserving_bind
    · exact storage_preserving_pure _
    intro _
    exact storage_preserving_setMapping _ _ _

private theorem settle_account_environment_preserving (account : Address) (delta : Uint256) :
    AccountEnvironmentPreserving (SuperfluidCFA._settleBalance account delta) := by
  unfold SuperfluidCFA._settleBalance
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  dsimp
  split
  · apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    exact account_environment_preserving_setMapping _ _ _ (by decide)
  · apply account_environment_preserving_bind
    · exact account_environment_preserving_pure _
    intro _
    exact account_environment_preserving_setMapping _ _ _ (by decide)

private def updateBeforeSettle
    (account : Address) (currentTimestamp : Uint256) : Contract (Uint256 × Uint256) := do
  SuperfluidCFA._requireCanonicalAccount account
  let oldTimestamp ← getMapping SuperfluidCFA.accountTimestamps account
  let oldNetFlowRateWord ← getMapping SuperfluidCFA.accountNetFlowRates account
  require (currentTimestamp <= 4294967295) "BENCHMARK_CANONICAL_TIMESTAMP_SCOPE"
  require (currentTimestamp >= oldTimestamp) "CFA_TIMESTAMP_UNDERFLOW"
  Verity.pure (oldTimestamp, oldNetFlowRateWord)

private theorem updateBeforeSettle_preserving (account : Address) (currentTimestamp : Uint256) :
    StatePreserving (updateBeforeSettle account currentTimestamp) := by
  unfold updateBeforeSettle
  apply preserving_bind
  · exact canonical_preserving _
  intro _
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro oldTimestamp
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro oldRate
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  exact preserving_pure _

private def updateFinishTail
    (account : Address) (rateDelta depositDelta owedDelta timestamp oldRate : Uint256) : Contract Unit := do
  let newNetFlowRateWord := add oldRate rateDelta
  require (newNetFlowRateWord <= 39614081257132168796771975167 ||
    newNetFlowRateWord >= 115792089237316195423570985008687907853269984665600949958200451839116357664768)
    "CFA_NET_FLOW_RATE_OVERFLOW"
  setMapping SuperfluidCFA.accountNetFlowRates account newNetFlowRateWord
  setMapping SuperfluidCFA.accountTimestamps account timestamp
  let oldDepositWord ← getMapping SuperfluidCFA.accountDeposits account
  let newDepositWord := add oldDepositWord depositDelta
  require (newDepositWord < 79228162514264337593543950336)
    "BENCHMARK_ACCOUNT_DEPOSIT_NO_FIELD_OVERLAP_SCOPE"
  let storedDepositWord := mul
    (mod (div newDepositWord 4294967296) 18446744073709551616) 4294967296
  setMapping SuperfluidCFA.accountDeposits account storedDepositWord
  let oldOwedDepositWord ← getMapping SuperfluidCFA.accountOwedDeposits account
  let newOwedDepositWord := add oldOwedDepositWord owedDelta
  require (newOwedDepositWord < 79228162514264337593543950336)
    "BENCHMARK_ACCOUNT_OWED_NO_FIELD_OVERLAP_SCOPE"
  let storedOwedDepositWord := mul
    (mod (div newOwedDepositWord 4294967296) 18446744073709551616) 4294967296
  setMapping SuperfluidCFA.accountOwedDeposits account storedOwedDepositWord

private def updateAfterSettle
    (account : Address) (flowRateDelta depositDelta owedDepositDelta currentTimestamp oldTimestamp oldRate : Uint256) :
    Contract Unit := do
  let elapsed := sub currentTimestamp oldTimestamp
  let dynamicBalanceWord := mul elapsed oldRate
  if dynamicBalanceWord != 0 then
    SuperfluidCFA._settleBalance account dynamicBalanceWord
  else
    Verity.pure ()
  updateFinishTail account flowRateDelta depositDelta owedDepositDelta currentTimestamp oldRate

private theorem setMapping_runState_read
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) (s : ContractState)
    (readSlot : Nat) (query : Address) :
    ((setMapping sl key value).runState s).storageMap readSlot query =
      if readSlot == sl.slot && query == key then value else s.storageMap readSlot query := rfl

private theorem setMapping_read_success
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256)
    (s t : ContractState) (readSlot : Nat) (query : Address)
    (h : (setMapping sl key value).run s = ContractResult.success () t) :
    t.storageMap readSlot query =
      if readSlot == sl.slot && query == key then value else s.storageMap readSlot query := by
  rw [success_state_eq _ _ _ _ h]
  exact setMapping_runState_read _ _ _ _ _ _

private theorem setMapping_read_other_success
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256)
    (s t : ContractState) (readSlot : Nat) (query : Address) (hquery : query ≠ key)
    (h : (setMapping sl key value).run s = ContractResult.success () t) :
    t.storageMap readSlot query = s.storageMap readSlot query := by
  rw [setMapping_read_success sl key value s t readSlot query h]
  simp [hquery]

private theorem setMapping_read_not_slot_success
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256)
    (s t : ContractState) (readSlot : Nat) (query : Address) (hslot : readSlot ≠ sl.slot)
    (h : (setMapping sl key value).run s = ContractResult.success () t) :
    t.storageMap readSlot query = s.storageMap readSlot query := by
  rw [setMapping_read_success sl key value s t readSlot query h]
  simp [hslot]

private theorem updateBeforeSettle_success
    (s t : ContractState) (account : Address) (timestamp : Uint256) (pair : Uint256 × Uint256)
    (h : (updateBeforeSettle account timestamp).run s = ContractResult.success pair t) :
    pair = (s.storageMap 2 account, s.storageMap 1 account) ∧ t = s := by
  unfold updateBeforeSettle at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldTimestamp, s₁, hgetTimestamp, h⟩
  have hs₁ : s₁ = s := success_state_eq _ _ _ _ hgetTimestamp
  have holdTimestamp : oldTimestamp = s.storageMap 2 account :=
    getMapping_value_of_success SuperfluidCFA.accountTimestamps account _ _ _ hgetTimestamp
  subst s₁
  subst oldTimestamp
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldRate, s₂, hgetRate, h⟩
  have hs₂ : s₂ = s := success_state_eq _ _ _ _ hgetRate
  have holdRate : oldRate = s.storageMap 1 account :=
    getMapping_value_of_success SuperfluidCFA.accountNetFlowRates account _ _ _ hgetRate
  subst s₂
  subst oldRate
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  have hraw := Contract.eq_of_run_success h
  change ContractResult.success (s.storageMap 2 account, s.storageMap 1 account) s =
    ContractResult.success pair t at hraw
  injection hraw with hpair hstate
  exact ⟨hpair.symm, hstate.symm⟩

private def UpdateFinishObs
    (base post : ContractState) (account : Address) (rateDelta timestamp oldRate : Uint256) : Prop :=
  post.storageMap 0 account = base.storageMap 0 account ∧
  post.storageMap 1 account = add oldRate rateDelta ∧
  post.storageMap 2 account = timestamp ∧
  ∀ slotIndex query, query ≠ account →
    post.storageMap slotIndex query = base.storageMap slotIndex query

private def updateFinish
    (account : Address) (rateDelta depositDelta owedDelta timestamp oldRate : Uint256) : Contract Unit :=
  updateFinishTail account rateDelta depositDelta owedDelta timestamp oldRate

private theorem updateFinish_observations
    (s t : ContractState) (account : Address)
    (rateDelta depositDelta owedDelta timestamp oldRate : Uint256)
    (h :
      (Verity.bind
        (require (add oldRate rateDelta <= 39614081257132168796771975167 ||
          add oldRate rateDelta >= 115792089237316195423570985008687907853269984665600949958200451839116357664768)
          "CFA_NET_FLOW_RATE_OVERFLOW")
        (fun _ => do
          setMapping SuperfluidCFA.accountNetFlowRates account (add oldRate rateDelta)
          setMapping SuperfluidCFA.accountTimestamps account timestamp
          let oldDepositWord ← getMapping SuperfluidCFA.accountDeposits account
          let newDepositWord := add oldDepositWord depositDelta
          require (newDepositWord < 79228162514264337593543950336)
            "BENCHMARK_ACCOUNT_DEPOSIT_NO_FIELD_OVERLAP_SCOPE"
          let storedDepositWord := mul
            (mod (div newDepositWord 4294967296) 18446744073709551616) 4294967296
          setMapping SuperfluidCFA.accountDeposits account storedDepositWord
          let oldOwedDepositWord ← getMapping SuperfluidCFA.accountOwedDeposits account
          let newOwedDepositWord := add oldOwedDepositWord owedDelta
          require (newOwedDepositWord < 79228162514264337593543950336)
            "BENCHMARK_ACCOUNT_OWED_NO_FIELD_OVERLAP_SCOPE"
          let storedOwedDepositWord := mul
            (mod (div newOwedDepositWord 4294967296) 18446744073709551616) 4294967296
          setMapping SuperfluidCFA.accountOwedDeposits account storedOwedDepositWord)).run s =
        ContractResult.success () t) :
    UpdateFinishObs s t account rateDelta timestamp oldRate := by
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨wRate, sRate, hrate, h⟩
  cases wRate
  rcases bind_success_elim _ _ _ _ _ h with ⟨wTimestamp, sTimestamp, htimestamp, h⟩
  cases wTimestamp
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨wDeposit, sDeposit, hdeposit, h⟩
  cases wDeposit
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, hfinal⟩
  unfold UpdateFinishObs
  constructor
  · calc
      t.storageMap 0 account = sDeposit.storageMap 0 account := by
        simpa [SuperfluidCFA.accountOwedDeposits] using
          setMapping_read_not_slot_success SuperfluidCFA.accountOwedDeposits account _ _ _ 0 account (by decide) hfinal
      _ = sTimestamp.storageMap 0 account := by
        simpa [SuperfluidCFA.accountDeposits] using
          setMapping_read_not_slot_success SuperfluidCFA.accountDeposits account _ _ _ 0 account (by decide) hdeposit
      _ = sRate.storageMap 0 account := by
        simpa [SuperfluidCFA.accountTimestamps] using
          setMapping_read_not_slot_success SuperfluidCFA.accountTimestamps account _ _ _ 0 account (by decide) htimestamp
      _ = s.storageMap 0 account := by
        simpa [SuperfluidCFA.accountNetFlowRates] using
          setMapping_read_not_slot_success SuperfluidCFA.accountNetFlowRates account _ _ _ 0 account (by decide) hrate
  constructor
  · calc
      t.storageMap 1 account = sDeposit.storageMap 1 account := by
        simpa [SuperfluidCFA.accountOwedDeposits] using
          setMapping_read_not_slot_success SuperfluidCFA.accountOwedDeposits account _ _ _ 1 account (by decide) hfinal
      _ = sTimestamp.storageMap 1 account := by
        simpa [SuperfluidCFA.accountDeposits] using
          setMapping_read_not_slot_success SuperfluidCFA.accountDeposits account _ _ _ 1 account (by decide) hdeposit
      _ = sRate.storageMap 1 account := by
        simpa [SuperfluidCFA.accountTimestamps] using
          setMapping_read_not_slot_success SuperfluidCFA.accountTimestamps account _ _ _ 1 account (by decide) htimestamp
      _ = add oldRate rateDelta := by
        simpa [SuperfluidCFA.accountNetFlowRates] using
          setMapping_read_success SuperfluidCFA.accountNetFlowRates account (add oldRate rateDelta) s sRate 1 account hrate
  constructor
  · calc
      t.storageMap 2 account = sDeposit.storageMap 2 account := by
        simpa [SuperfluidCFA.accountOwedDeposits] using
          setMapping_read_not_slot_success SuperfluidCFA.accountOwedDeposits account _ _ _ 2 account (by decide) hfinal
      _ = sTimestamp.storageMap 2 account := by
        simpa [SuperfluidCFA.accountDeposits] using
          setMapping_read_not_slot_success SuperfluidCFA.accountDeposits account _ _ _ 2 account (by decide) hdeposit
      _ = timestamp := by
        simpa [SuperfluidCFA.accountTimestamps] using
          setMapping_read_success SuperfluidCFA.accountTimestamps account timestamp sRate sTimestamp 2 account htimestamp
  intro slotIndex query hquery
  calc
    t.storageMap slotIndex query = sDeposit.storageMap slotIndex query :=
      setMapping_read_other_success SuperfluidCFA.accountOwedDeposits account _ _ _ slotIndex query hquery hfinal
    _ = sTimestamp.storageMap slotIndex query :=
      setMapping_read_other_success SuperfluidCFA.accountDeposits account _ _ _ slotIndex query hquery hdeposit
    _ = sRate.storageMap slotIndex query :=
      setMapping_read_other_success SuperfluidCFA.accountTimestamps account _ _ _ slotIndex query hquery htimestamp
    _ = s.storageMap slotIndex query :=
      setMapping_read_other_success SuperfluidCFA.accountNetFlowRates account _ _ _ slotIndex query hquery hrate

private def UpdateAfterObs
    (base post : ContractState) (account : Address)
    (rateDelta timestamp oldTimestamp oldRate : Uint256) : Prop :=
  cfaProjectionAt post account timestamp =
    add (base.storageMap 0 account) (mul (sub timestamp oldTimestamp) oldRate) ∧
  post.storageMap 1 account = add oldRate rateDelta ∧
  ∀ slotIndex query, query ≠ account →
    post.storageMap slotIndex query = base.storageMap slotIndex query

private theorem updateAfter_zero_observations
    (s t : ContractState) (account : Address)
    (rateDelta depositDelta owedDelta timestamp oldTimestamp oldRate : Uint256)
    (hdynamic : mul (sub timestamp oldTimestamp) oldRate = 0)
    (hfinish : UpdateFinishObs s t account rateDelta timestamp oldRate) :
    UpdateAfterObs s t account rateDelta timestamp oldTimestamp oldRate := by
  unfold UpdateAfterObs
  refine ⟨?_, hfinish.2.1, hfinish.2.2.2⟩
  have hzero : sub timestamp timestamp = 0 := Verity.Core.Uint256.sub_self timestamp
  have hmul : mul 0 (t.storageMap 1 account) = 0 := Verity.Core.Uint256.zero_mul _
  simp [cfaProjectionAt, hfinish.1, hfinish.2.2.1, hdynamic, hzero, hmul]

private theorem updateAfter_nonzero_observations
    (s s₁ t : ContractState) (account : Address)
    (rateDelta depositDelta owedDelta timestamp oldTimestamp oldRate : Uint256)
    (hsettle : (SuperfluidCFA._settleBalance account (mul (sub timestamp oldTimestamp) oldRate)).run s =
      ContractResult.success () s₁)
    (hfinish : UpdateFinishObs s₁ t account rateDelta timestamp oldRate) :
    UpdateAfterObs s t account rateDelta timestamp oldTimestamp oldRate := by
  have hs₁ := settle_success s s₁ account (mul (sub timestamp oldTimestamp) oldRate) hsettle
  have hsettledBalance : s₁.storageMap 0 account =
      add (s.storageMap 0 account) (mul (sub timestamp oldTimestamp) oldRate) := by
    rw [hs₁]
    simpa [SuperfluidCFA.sharedSettledBalances] using
      setMapping_runState_read SuperfluidCFA.sharedSettledBalances account
        (add (s.storageMap 0 account) (mul (sub timestamp oldTimestamp) oldRate)) s 0 account
  have hsettledFrame : ∀ slotIndex query, query ≠ account →
      s₁.storageMap slotIndex query = s.storageMap slotIndex query := by
    intro slotIndex query hquery
    rw [hs₁]
    simpa [hquery] using
      setMapping_runState_read SuperfluidCFA.sharedSettledBalances account
        (add (s.storageMap 0 account) (mul (sub timestamp oldTimestamp) oldRate)) s slotIndex query
  unfold UpdateAfterObs
  refine ⟨?_, hfinish.2.1, ?_⟩
  · have hzero : sub timestamp timestamp = 0 := Verity.Core.Uint256.sub_self timestamp
    have hmul : mul 0 (t.storageMap 1 account) = 0 := Verity.Core.Uint256.zero_mul _
    have hadd : add (add (s.storageMap 0 account)
        (mul (sub timestamp oldTimestamp) oldRate)) 0 =
        add (s.storageMap 0 account) (mul (sub timestamp oldTimestamp) oldRate) :=
      Verity.Core.Uint256.add_zero _
    simp [cfaProjectionAt, hfinish.1, hfinish.2.2.1, hsettledBalance, hzero, hmul, hadd]
  intro slotIndex query hquery
  exact (hfinish.2.2.2 slotIndex query hquery).trans (hsettledFrame slotIndex query hquery)

private def UpdateObs
    (base post : ContractState) (account : Address)
    (rateDelta timestamp : Uint256) : Prop :=
  cfaProjectionAt post account timestamp = cfaProjectionAt base account timestamp ∧
  post.storageMap 1 account = add (base.storageMap 1 account) rateDelta ∧
  ∀ slotIndex query, query ≠ account →
    post.storageMap slotIndex query = base.storageMap slotIndex query

private theorem updateAccountFlowState_observations
    (s t : ContractState) (account : Address)
    (rateDelta depositDelta owedDelta timestamp : Uint256)
    (h : (SuperfluidCFA._updateAccountFlowState
      account rateDelta depositDelta owedDelta timestamp).run s = ContractResult.success () t) :
    UpdateObs s t account rateDelta timestamp := by
  unfold SuperfluidCFA._updateAccountFlowState at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldTimestamp, s₁, hgetTimestamp, h⟩
  have hs₁ : s₁ = s := success_state_eq _ _ _ _ hgetTimestamp
  have holdTimestamp : oldTimestamp = s.storageMap 2 account :=
    getMapping_value_of_success SuperfluidCFA.accountTimestamps account _ _ _ hgetTimestamp
  subst s₁
  subst oldTimestamp
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldRate, s₂, hgetRate, h⟩
  have hs₂ : s₂ = s := success_state_eq _ _ _ _ hgetRate
  have holdRate : oldRate = s.storageMap 1 account :=
    getMapping_value_of_success SuperfluidCFA.accountNetFlowRates account _ _ _ hgetRate
  subst s₂
  subst oldRate
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, hafter⟩
  by_cases hbranch :
      (mul (sub timestamp (s.storageMap 2 account)) (s.storageMap 1 account) != 0) = true
  · rw [if_pos hbranch] at hafter
    rcases bind_success_elim _ _ _ _ _ hafter with ⟨settled, s₃, hsettle, htail⟩
    cases settled
    have hfinish := updateFinish_observations s₃ t account rateDelta depositDelta owedDelta timestamp
      (s.storageMap 1 account) htail
    have hafter' := updateAfter_nonzero_observations s s₃ t account rateDelta depositDelta owedDelta timestamp
      (s.storageMap 2 account) (s.storageMap 1 account) hsettle hfinish
    unfold UpdateObs
    refine ⟨?_, hafter'.2.1, hafter'.2.2⟩
    simpa [cfaProjectionAt] using hafter'.1
  · rw [if_neg hbranch] at hafter
    have hdynamic : mul (sub timestamp (s.storageMap 2 account)) (s.storageMap 1 account) = 0 := by
      by_contra hzero
      apply hbranch
      simp [hzero]
    rcases preserving_bind_tail _ _ _ _ _ (preserving_pure ()) hafter with ⟨_, htail⟩
    have hfinish := updateFinish_observations s t account rateDelta depositDelta owedDelta timestamp
      (s.storageMap 1 account) htail
    have hafter' := updateAfter_zero_observations s t account rateDelta depositDelta owedDelta timestamp
      (s.storageMap 2 account) (s.storageMap 1 account) hdynamic hfinish
    unfold UpdateObs
    refine ⟨?_, hafter'.2.1, hafter'.2.2⟩
    simpa [cfaProjectionAt] using hafter'.1

private theorem updateAccountFlowState_timestamp_bound
    (s t : ContractState) (account : Address) (rateDelta depositDelta owedDelta timestamp : Uint256)
    (h : (SuperfluidCFA._updateAccountFlowState
      account rateDelta depositDelta owedDelta timestamp).run s = ContractResult.success () t) :
    timestamp ≤ 4294967295 := by
  unfold SuperfluidCFA._updateAccountFlowState at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, _, hrequire, _⟩
  have hcond :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (timestamp <= 4294967295) "BENCHMARK_CANONICAL_TIMESTAMP_SCOPE" _
      (by rw [hrequire]; rfl)
  simpa using hcond

private def Map2Preserving {α : Type} (m : Contract α) : Prop :=
  ∀ s, (m.runState s).storageMap2 = s.storageMap2

private theorem map2_preserving_bind {α β : Type} (m : Contract α) (f : α → Contract β)
    (hm : Map2Preserving m) (hf : ∀ a, Map2Preserving (f a)) :
    Map2Preserving (Verity.bind m f) := by
  intro s
  unfold Contract.runState Verity.bind
  cases h : m s
  next a t =>
    have ht : t.storageMap2 = s.storageMap2 := by
      have hs := hm s
      simp [Contract.runState, h] at hs
      exact hs
    cases htail : f a t
    next b u =>
      have hu : u.storageMap2 = t.storageMap2 := by
        have htail' := hf a t
        simpa [Contract.runState, htail] using htail'
      simpa [Contract.runState, h, htail] using hu.trans ht
    next msg u => simp [Contract.runState, h, htail]
  next msg t => simp [Contract.runState, h]

private theorem map2_preserving_require (cond : Bool) (msg : String) :
    Map2Preserving (Verity.require cond msg) := by
  intro s
  cases cond <;> rfl

private theorem map2_preserving_pure {α : Type} (a : α) :
    Map2Preserving (Verity.pure a : Contract α) := by
  intro s
  rfl

private theorem map2_preserving_getMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) :
    Map2Preserving (getMapping sl key) := by
  intro s
  rfl

private theorem map2_preserving_getMapping2
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) :
    Map2Preserving (getMapping2 sl left right) := by
  intro s
  rfl

private theorem map2_preserving_setMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) :
    Map2Preserving (setMapping sl key value) := by
  intro s
  rfl

private theorem canonical_map2_preserving (account : Address) :
    Map2Preserving (SuperfluidCFA._requireCanonicalAccount account) := by
  unfold SuperfluidCFA._requireCanonicalAccount
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  exact map2_preserving_require _ _

private theorem settle_map2_preserving (account : Address) (delta : Uint256) :
    Map2Preserving (SuperfluidCFA._settleBalance account delta) := by
  unfold SuperfluidCFA._settleBalance
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  dsimp
  split
  · apply map2_preserving_bind
    · exact map2_preserving_require _ _
    intro _
    exact map2_preserving_setMapping _ _ _
  · apply map2_preserving_bind
    · exact map2_preserving_pure _
    intro _
    exact map2_preserving_setMapping _ _ _

private theorem updateFinish_map2_preserving
    (account : Address) (rateDelta depositDelta owedDelta timestamp oldRate : Uint256) :
    Map2Preserving (updateFinishTail account rateDelta depositDelta owedDelta timestamp oldRate) := by
  unfold updateFinishTail
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_setMapping _ _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_setMapping _ _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_setMapping _ _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  exact map2_preserving_setMapping _ _ _

private theorem updateFinish_storage_preserving
    (account : Address) (rateDelta depositDelta owedDelta timestamp oldRate : Uint256) :
    StoragePreserving (updateFinishTail account rateDelta depositDelta owedDelta timestamp oldRate) := by
  unfold updateFinishTail
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  exact storage_preserving_setMapping _ _ _

private theorem updateFinish_account_environment_preserving
    (account : Address) (rateDelta depositDelta owedDelta timestamp oldRate : Uint256) :
    AccountEnvironmentPreserving
      (updateFinishTail account rateDelta depositDelta owedDelta timestamp oldRate) := by
  unfold updateFinishTail
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping _ _ _ (by decide)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping _ _ _ (by decide)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping _ _ _ (by decide)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  exact account_environment_preserving_setMapping _ _ _ (by decide)

private theorem updateAccountFlowState_map2_preserving
    (account : Address) (rateDelta depositDelta owedDelta timestamp : Uint256) :
    Map2Preserving (SuperfluidCFA._updateAccountFlowState
      account rateDelta depositDelta owedDelta timestamp) := by
  unfold SuperfluidCFA._updateAccountFlowState
  apply map2_preserving_bind
  · exact canonical_map2_preserving _
  intro oldTimestamp
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro oldRate
  apply map2_preserving_bind
  · exact map2_preserving_getMapping _ _
  intro oldRate
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  apply map2_preserving_bind
  · exact map2_preserving_require _ _
  intro _
  dsimp
  split
  · apply map2_preserving_bind
    · exact settle_map2_preserving _ _
    intro _
    simpa [updateFinishTail] using updateFinish_map2_preserving account rateDelta depositDelta owedDelta timestamp oldRate
  · apply map2_preserving_bind
    · exact map2_preserving_pure _
    intro _
    simpa [updateFinishTail] using updateFinish_map2_preserving account rateDelta depositDelta owedDelta timestamp oldRate

private theorem updateAccountFlowState_storage_preserving
    (account : Address) (rateDelta depositDelta owedDelta timestamp : Uint256) :
    StoragePreserving (SuperfluidCFA._updateAccountFlowState
      account rateDelta depositDelta owedDelta timestamp) := by
  unfold SuperfluidCFA._updateAccountFlowState
  apply storage_preserving_bind
  · exact canonical_storage_preserving _
  intro oldTimestamp
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro oldRate
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro oldRate
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  dsimp
  split
  · apply storage_preserving_bind
    · exact settle_storage_preserving _ _
    intro _
    simpa [updateFinishTail] using
      updateFinish_storage_preserving account rateDelta depositDelta owedDelta timestamp oldRate
  · apply storage_preserving_bind
    · exact storage_preserving_pure _
    intro _
    simpa [updateFinishTail] using
      updateFinish_storage_preserving account rateDelta depositDelta owedDelta timestamp oldRate

private theorem updateAccountFlowState_account_environment_preserving
    (account : Address) (rateDelta depositDelta owedDelta timestamp : Uint256) :
    AccountEnvironmentPreserving (SuperfluidCFA._updateAccountFlowState
      account rateDelta depositDelta owedDelta timestamp) := by
  unfold SuperfluidCFA._updateAccountFlowState
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro oldTimestamp
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro oldRate
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro oldRate
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  dsimp
  split
  · apply account_environment_preserving_bind
    · exact settle_account_environment_preserving _ _
    intro _
    simpa [updateFinishTail] using
      updateFinish_account_environment_preserving account rateDelta depositDelta owedDelta timestamp oldRate
  · apply account_environment_preserving_bind
    · exact account_environment_preserving_pure _
    intro _
    simpa [updateFinishTail] using
      updateFinish_account_environment_preserving account rateDelta depositDelta owedDelta timestamp oldRate

private theorem getMapping2_value_of_success
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address)
    (s t : ContractState) (value : Uint256)
    (h : (getMapping2 sl left right).run s = ContractResult.success value t) :
    value = s.storageMap2 sl.slot left right := by
  have hraw := Contract.eq_of_run_success h
  change ContractResult.success (s.storageMap2 sl.slot left right) s =
    ContractResult.success value t at hraw
  injection hraw with hvalue _
  exact hvalue.symm

private theorem setMapping2_read_success
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) (value : Uint256)
    (s t : ContractState) (readSlot : Nat) (queryLeft queryRight : Address)
    (h : (setMapping2 sl left right value).run s = ContractResult.success () t) :
    t.storageMap2 readSlot queryLeft queryRight =
      if readSlot == sl.slot && queryLeft == left && queryRight == right then value
      else s.storageMap2 readSlot queryLeft queryRight := by
  rw [success_state_eq _ _ _ _ h]
  rfl

private theorem setMapping2_read_not_slot_success
    (sl : StorageSlot (Address → Address → Uint256)) (left right : Address) (value : Uint256)
    (s t : ContractState) (readSlot : Nat) (queryLeft queryRight : Address) (hslot : readSlot ≠ sl.slot)
    (h : (setMapping2 sl left right value).run s = ContractResult.success () t) :
    t.storageMap2 readSlot queryLeft queryRight = s.storageMap2 readSlot queryLeft queryRight := by
  rw [setMapping2_read_success sl left right value s t readSlot queryLeft queryRight h]
  simp [hslot]

private def FlowWriteObs
    (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit oldOwed timestamp : Uint256) : Prop :=
  post.storageMap = base.storageMap ∧
  post.storageMap2 5 sender receiver =
    (if (newRate != 0 && newRate <= 39614081257132168796771975167) = true then timestamp else 0) ∧
  post.storageMap2 6 sender receiver = newRate ∧
  post.storageMap2 7 sender receiver =
    mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296 ∧
  post.storageMap2 8 sender receiver = oldOwed ∧
  post.storageMap2 9 sender receiver = base.storageMap2 9 sender receiver ∧
  post.storageMap2 27 sender receiver = base.storageMap2 27 sender receiver

private def writeFlowFields
    (sender receiver : Address) (newRate newDeposit oldOwed timestamp : Uint256) : Contract Unit := do
  if newRate != 0 && newRate <= 39614081257132168796771975167 then
    setMapping2 SuperfluidCFA.flowTimestamps sender receiver timestamp
  else
    setMapping2 SuperfluidCFA.flowTimestamps sender receiver 0
  setMapping2 SuperfluidCFA.flowRates sender receiver newRate
  setMapping2 SuperfluidCFA.flowDeposits sender receiver
    (mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296)
  setMapping2 SuperfluidCFA.flowOwedDeposits sender receiver oldOwed

private theorem writeFlowFields_storage_preserving
    (sender receiver : Address) (newRate newDeposit oldOwed timestamp : Uint256) :
    StoragePreserving (writeFlowFields sender receiver newRate newDeposit oldOwed timestamp) := by
  unfold writeFlowFields
  split
  all_goals
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    exact storage_preserving_setMapping2 _ _ _ _

private theorem writeFlowFields_account_environment_preserving
    (sender receiver : Address) (newRate newDeposit oldOwed timestamp : Uint256) :
    AccountEnvironmentPreserving
      (writeFlowFields sender receiver newRate newDeposit oldOwed timestamp) := by
  unfold writeFlowFields
  split
  all_goals
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    exact account_environment_preserving_setMapping2 _ _ _ _

private theorem flowWrite_observations
    (s t : ContractState) (sender receiver : Address)
    (newRate newDeposit oldOwed timestamp : Uint256)
    (h : (writeFlowFields sender receiver newRate newDeposit oldOwed timestamp).run s =
        ContractResult.success () t) :
    FlowWriteObs s t sender receiver newRate newDeposit oldOwed timestamp := by
  unfold writeFlowFields at h
  by_cases htime : (newRate != 0 && newRate <= 39614081257132168796771975167) = true
  · rw [if_pos htime] at h
    have htime' : newRate ≠ 0 ∧ newRate ≤ 39614081257132168796771975167 := by
      simpa using htime
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, sTime, htimeWrite, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, sRate, hrateWrite, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, sDeposit, hdepositWrite, howedWrite⟩
    unfold FlowWriteObs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [success_state_eq _ _ _ _ howedWrite, success_state_eq _ _ _ _ hdepositWrite,
        success_state_eq _ _ _ _ hrateWrite, success_state_eq _ _ _ _ htimeWrite]
      rfl
    · calc
        t.storageMap2 5 sender receiver = sDeposit.storageMap2 5 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 5 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 5 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 5 sender receiver (by decide) hdepositWrite
        _ = sTime.storageMap2 5 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowRates sender receiver newRate _ _ 5 sender receiver (by decide) hrateWrite
        _ = timestamp := by
          simpa [SuperfluidCFA.flowTimestamps] using
            setMapping2_read_success SuperfluidCFA.flowTimestamps sender receiver timestamp s sTime 5 sender receiver htimeWrite
        _ = _ := by rw [if_pos htime]
    · calc
        t.storageMap2 6 sender receiver = sDeposit.storageMap2 6 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 6 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 6 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 6 sender receiver (by decide) hdepositWrite
        _ = newRate := by
          simpa [SuperfluidCFA.flowRates] using
            setMapping2_read_success SuperfluidCFA.flowRates sender receiver newRate sTime sRate 6 sender receiver hrateWrite
    · calc
        t.storageMap2 7 sender receiver = sDeposit.storageMap2 7 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 7 sender receiver (by decide) howedWrite
        _ = _ := by
          simpa [SuperfluidCFA.flowDeposits] using
            setMapping2_read_success SuperfluidCFA.flowDeposits sender receiver _ sRate sDeposit 7 sender receiver hdepositWrite
    · simpa [SuperfluidCFA.flowOwedDeposits] using
        setMapping2_read_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed sDeposit t 8 sender receiver howedWrite
    · calc
        t.storageMap2 9 sender receiver = sDeposit.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 9 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 9 sender receiver (by decide) hdepositWrite
        _ = sTime.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowRates sender receiver newRate _ _ 9 sender receiver (by decide) hrateWrite
        _ = s.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowTimestamps sender receiver timestamp _ _ 9 sender receiver (by decide) htimeWrite
    · calc
        t.storageMap2 27 sender receiver = sDeposit.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 27 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 27 sender receiver (by decide) hdepositWrite
        _ = sTime.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowRates sender receiver newRate _ _ 27 sender receiver (by decide) hrateWrite
        _ = s.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowTimestamps sender receiver timestamp _ _ 27 sender receiver (by decide) htimeWrite
  · rw [if_neg htime] at h
    have htime' : ¬(newRate ≠ 0 ∧ newRate ≤ 39614081257132168796771975167) := by
      simpa using htime
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, sTime, htimeWrite, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, sRate, hrateWrite, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, sDeposit, hdepositWrite, howedWrite⟩
    unfold FlowWriteObs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [success_state_eq _ _ _ _ howedWrite, success_state_eq _ _ _ _ hdepositWrite,
        success_state_eq _ _ _ _ hrateWrite, success_state_eq _ _ _ _ htimeWrite]
      rfl
    · calc
        t.storageMap2 5 sender receiver = sDeposit.storageMap2 5 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 5 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 5 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 5 sender receiver (by decide) hdepositWrite
        _ = sTime.storageMap2 5 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowRates sender receiver newRate _ _ 5 sender receiver (by decide) hrateWrite
        _ = 0 := by simpa [SuperfluidCFA.flowTimestamps] using
          setMapping2_read_success SuperfluidCFA.flowTimestamps sender receiver 0 s sTime 5 sender receiver htimeWrite
        _ = _ := by rw [if_neg htime]
    · calc
        t.storageMap2 6 sender receiver = sDeposit.storageMap2 6 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 6 sender receiver (by decide) howedWrite
        _ = newRate := by
          calc
            sDeposit.storageMap2 6 sender receiver = sRate.storageMap2 6 sender receiver :=
              setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 6 sender receiver (by decide) hdepositWrite
            _ = newRate := by simpa [SuperfluidCFA.flowRates] using
              setMapping2_read_success SuperfluidCFA.flowRates sender receiver newRate sTime sRate 6 sender receiver hrateWrite
    · calc
        t.storageMap2 7 sender receiver = sDeposit.storageMap2 7 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 7 sender receiver (by decide) howedWrite
        _ = _ := by simpa [SuperfluidCFA.flowDeposits] using
          setMapping2_read_success SuperfluidCFA.flowDeposits sender receiver _ sRate sDeposit 7 sender receiver hdepositWrite
    · simpa [SuperfluidCFA.flowOwedDeposits] using
        setMapping2_read_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed sDeposit t 8 sender receiver howedWrite
    · calc
        t.storageMap2 9 sender receiver = sDeposit.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 9 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 9 sender receiver (by decide) hdepositWrite
        _ = sTime.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowRates sender receiver newRate _ _ 9 sender receiver (by decide) hrateWrite
        _ = s.storageMap2 9 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowTimestamps sender receiver 0 _ _ 9 sender receiver (by decide) htimeWrite
    · calc
        t.storageMap2 27 sender receiver = sDeposit.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowOwedDeposits sender receiver oldOwed _ _ 27 sender receiver (by decide) howedWrite
        _ = sRate.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowDeposits sender receiver _ _ _ 27 sender receiver (by decide) hdepositWrite
        _ = sTime.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowRates sender receiver newRate _ _ 27 sender receiver (by decide) hrateWrite
        _ = s.storageMap2 27 sender receiver :=
          setMapping2_read_not_slot_success SuperfluidCFA.flowTimestamps sender receiver 0 _ _ 27 sender receiver (by decide) htimeWrite

private theorem add_sub_assoc (a b c : Uint256) : a + (b - c) = (a + b) - c := by
  have lhs_eq : (a + (b - c)) + c = a + b := by
    rw [Verity.Core.Uint256.add_assoc]
    rw [Verity.Core.Uint256.sub_add_cancel_left]
  have rhs_eq : ((a + b) - c) + c = a + b :=
    Verity.Core.Uint256.sub_add_cancel_left (add a b) c
  exact Verity.Core.Uint256.add_right_cancel (by rw [lhs_eq, rhs_eq])

private theorem opposite_rate_deltas_cancel (a b oldRate newRate : Uint256) :
    (a + (oldRate - newRate)) + (b + (newRate - oldRate)) = a + b := by
  have hdelta : (oldRate - newRate) + (newRate - oldRate) = 0 := by
    calc
      (oldRate - newRate) + (newRate - oldRate) =
          ((oldRate - newRate) + newRate) - oldRate := by
            exact add_sub_assoc _ _ _
      _ = oldRate - oldRate := by rw [Verity.Core.Uint256.sub_add_cancel_left]
      _ = 0 := Verity.Core.Uint256.sub_self oldRate
  calc
    (a + (oldRate - newRate)) + (b + (newRate - oldRate)) =
        (a + b) + ((oldRate - newRate) + (newRate - oldRate)) := by
          calc
            (a + (oldRate - newRate)) + (b + (newRate - oldRate)) =
                a + ((oldRate - newRate) + (b + (newRate - oldRate))) := by
                  rw [Verity.Core.Uint256.add_assoc]
            _ = a + (((oldRate - newRate) + b) + (newRate - oldRate)) := by
                  rw [Verity.Core.Uint256.add_assoc]
            _ = a + ((b + (oldRate - newRate)) + (newRate - oldRate)) := by
                  rw [Verity.Core.Uint256.add_comm (oldRate - newRate) b]
            _ = a + (b + ((oldRate - newRate) + (newRate - oldRate))) := by
                  rw [Verity.Core.Uint256.add_assoc]
            _ = (a + b) + ((oldRate - newRate) + (newRate - oldRate)) := by
                  rw [Verity.Core.Uint256.add_assoc]
    _ = a + b := by rw [hdelta, Verity.Core.Uint256.add_zero]

private def ChangeFlowObs
    (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp : Uint256) : Prop :=
  pairCfaProjectionAt post sender receiver timestamp =
    pairCfaProjectionAt base sender receiver timestamp ∧
  pairNetFlowRate post sender receiver = pairNetFlowRate base sender receiver ∧
  (∀ slotIndex query, query ≠ sender → query ≠ receiver →
    post.storageMap slotIndex query = base.storageMap slotIndex query) ∧
  post.storageMap2 5 sender receiver =
    (if (newRate != 0 && newRate <= 39614081257132168796771975167) = true then timestamp else 0) ∧
  post.storageMap2 6 sender receiver = newRate ∧
  post.storageMap2 7 sender receiver =
    mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296 ∧
  post.storageMap2 8 sender receiver = base.storageMap2 8 sender receiver ∧
  post.storageMap2 9 sender receiver = base.storageMap2 9 sender receiver ∧
  post.storageMap2 27 sender receiver = base.storageMap2 27 sender receiver ∧
  timestamp ≤ 4294967295

private theorem changeFlow_observations
    (s t : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp : Uint256) (hdistinct : sender ≠ receiver)
    (h : (SuperfluidCFA._changeFlow sender receiver newRate newDeposit timestamp).run s =
      ContractResult.success () t) :
    ChangeFlowObs s t sender receiver newRate newDeposit timestamp := by
  unfold SuperfluidCFA._changeFlow at h
  simp only [Bind.bind] at h
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldRate, sRate0, hgetRate, h⟩
  have hsRate0 : sRate0 = s := success_state_eq _ _ _ _ hgetRate
  have holdRate : oldRate = s.storageMap2 6 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowRates sender receiver _ _ _ hgetRate
  subst sRate0
  subst oldRate
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldDeposit, sDeposit0, hgetDeposit, h⟩
  have hsDeposit0 : sDeposit0 = s := success_state_eq _ _ _ _ hgetDeposit
  have holdDeposit : oldDeposit = s.storageMap2 7 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowDeposits sender receiver _ _ _ hgetDeposit
  subst sDeposit0
  subst oldDeposit
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldOwed, sOwed0, hgetOwed, h⟩
  have hsOwed0 : sOwed0 = s := success_state_eq _ _ _ _ hgetOwed
  have holdOwed : oldOwed = s.storageMap2 8 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowOwedDeposits sender receiver _ _ _ hgetOwed
  subst sOwed0
  subst oldOwed
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  have hsplit : ∃ sWrites,
      (writeFlowFields sender receiver newRate newDeposit
        (s.storageMap2 8 sender receiver) timestamp).run s = ContractResult.success () sWrites ∧
      (Verity.bind
        (SuperfluidCFA._updateAccountFlowState sender
          (sub (s.storageMap2 6 sender receiver) newRate)
          (add (sub newDeposit (s.storageMap2 7 sender receiver)) (s.storageMap2 8 sender receiver)) 0 timestamp)
        (fun _ => SuperfluidCFA._updateAccountFlowState receiver
          (sub newRate (s.storageMap2 6 sender receiver)) 0 0 timestamp)).run sWrites =
        ContractResult.success () t := by
    split at h
    next htime =>
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sTime, htimeWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sRate, hrateWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sDeposit, hdepositWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sWrites, howedWrite, htail⟩
      have hsTime := success_state_eq _ _ _ _ htimeWrite
      have hsRate := success_state_eq _ _ _ _ hrateWrite
      have hsDeposit := success_state_eq _ _ _ _ hdepositWrite
      have hsWrites := success_state_eq _ _ _ _ howedWrite
      subst sTime
      subst sRate
      subst sDeposit
      refine ⟨sWrites, ?_, htail⟩
      unfold writeFlowFields
      rw [if_pos (by simpa using htime)]
      rw [hsWrites]
      rfl
    next htime =>
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sTime, htimeWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sRate, hrateWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sDeposit, hdepositWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sWrites, howedWrite, htail⟩
      have hsTime := success_state_eq _ _ _ _ htimeWrite
      have hsRate := success_state_eq _ _ _ _ hrateWrite
      have hsDeposit := success_state_eq _ _ _ _ hdepositWrite
      have hsWrites := success_state_eq _ _ _ _ howedWrite
      subst sTime
      subst sRate
      subst sDeposit
      refine ⟨sWrites, ?_, htail⟩
      unfold writeFlowFields
      rw [if_neg (by simpa using htime)]
      rw [hsWrites]
      rfl
  rcases hsplit with ⟨sWrites, hwrite, h⟩
  have hwriteObs := flowWrite_observations s sWrites sender receiver newRate newDeposit
    (s.storageMap2 8 sender receiver) timestamp hwrite
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, sSender, hsender, hreceiver⟩
  have hsenderObs := updateAccountFlowState_observations sWrites sSender sender
    (sub (s.storageMap2 6 sender receiver) newRate)
    (add (sub newDeposit (s.storageMap2 7 sender receiver)) (s.storageMap2 8 sender receiver)) 0 timestamp hsender
  have hreceiverObs := updateAccountFlowState_observations sSender t receiver
    (sub newRate (s.storageMap2 6 sender receiver)) 0 0 timestamp hreceiver
  have hsenderMap2 : sSender.storageMap2 = sWrites.storageMap2 := by
    rw [success_state_eq _ _ _ _ hsender]
    exact updateAccountFlowState_map2_preserving _ _ _ _ _ _
  have hreceiverMap2 : t.storageMap2 = sSender.storageMap2 := by
    rw [success_state_eq _ _ _ _ hreceiver]
    exact updateAccountFlowState_map2_preserving _ _ _ _ _ _
  unfold ChangeFlowObs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pairCfaProjectionAt
    calc
      add (cfaProjectionAt t sender timestamp) (cfaProjectionAt t receiver timestamp) =
          add (cfaProjectionAt sSender sender timestamp) (cfaProjectionAt sSender receiver timestamp) := by
            rw [hreceiverObs.1]
            simp [cfaProjectionAt,
              hreceiverObs.2.2 0 sender hdistinct,
              hreceiverObs.2.2 1 sender hdistinct,
              hreceiverObs.2.2 2 sender hdistinct]
      _ = add (cfaProjectionAt sWrites sender timestamp) (cfaProjectionAt sWrites receiver timestamp) := by
            rw [hsenderObs.1]
            simp [cfaProjectionAt, hsenderObs.2.2 0 receiver (Ne.symm hdistinct),
              hsenderObs.2.2 1 receiver (Ne.symm hdistinct),
              hsenderObs.2.2 2 receiver (Ne.symm hdistinct)]
      _ = add (cfaProjectionAt s sender timestamp) (cfaProjectionAt s receiver timestamp) := by
            simpa [cfaProjectionAt, hwriteObs.1]
  · unfold pairNetFlowRate
    have hsenderFinal : t.storageMap 1 sender = sSender.storageMap 1 sender :=
      hreceiverObs.2.2 1 sender hdistinct
    rw [hsenderFinal, hreceiverObs.2.1, hsenderObs.2.1]
    have hreceiverRate : sSender.storageMap 1 receiver = sWrites.storageMap 1 receiver :=
      hsenderObs.2.2 1 receiver (Ne.symm hdistinct)
    rw [hreceiverRate, hwriteObs.1]
    exact opposite_rate_deltas_cancel _ _ _ _
  · intro slotIndex query hquerySender hqueryReceiver
    calc
      t.storageMap slotIndex query = sSender.storageMap slotIndex query :=
        hreceiverObs.2.2 slotIndex query hqueryReceiver
      _ = sWrites.storageMap slotIndex query :=
        hsenderObs.2.2 slotIndex query hquerySender
      _ = s.storageMap slotIndex query := by rw [hwriteObs.1]
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.2.2.2
  · exact updateAccountFlowState_timestamp_bound sWrites sSender sender
      (sub (s.storageMap2 6 sender receiver) newRate)
      (add (sub newDeposit (s.storageMap2 7 sender receiver)) (s.storageMap2 8 sender receiver)) 0
      timestamp hsender

private theorem opposite_rate_deltas_sequential_cancel (a oldRate newRate : Uint256) :
    add (add a (sub oldRate newRate)) (sub newRate oldRate) = a := by
  have hdelta : add (sub oldRate newRate) (sub newRate oldRate) = 0 := by
    simpa using opposite_rate_deltas_cancel 0 0 oldRate newRate
  calc
    add (add a (sub oldRate newRate)) (sub newRate oldRate) =
        add a (add (sub oldRate newRate) (sub newRate oldRate)) := by
          exact Verity.Core.Uint256.add_assoc _ _ _
    _ = a := by rw [hdelta]; exact Verity.Core.Uint256.add_zero _

private theorem changeFlow_self_observations
    (s t : ContractState) (sender : Address)
    (newRate newDeposit timestamp : Uint256)
    (h : (SuperfluidCFA._changeFlow sender sender newRate newDeposit timestamp).run s =
      ContractResult.success () t) :
    ChangeFlowObs s t sender sender newRate newDeposit timestamp := by
  unfold SuperfluidCFA._changeFlow at h
  simp only [Bind.bind] at h
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldRate, sRate0, hgetRate, h⟩
  have hsRate0 : sRate0 = s := success_state_eq _ _ _ _ hgetRate
  have holdRate : oldRate = s.storageMap2 6 sender sender :=
    getMapping2_value_of_success SuperfluidCFA.flowRates sender sender _ _ _ hgetRate
  subst sRate0
  subst oldRate
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldDeposit, sDeposit0, hgetDeposit, h⟩
  have hsDeposit0 : sDeposit0 = s := success_state_eq _ _ _ _ hgetDeposit
  have holdDeposit : oldDeposit = s.storageMap2 7 sender sender :=
    getMapping2_value_of_success SuperfluidCFA.flowDeposits sender sender _ _ _ hgetDeposit
  subst sDeposit0
  subst oldDeposit
  rcases bind_success_elim _ _ _ _ _ h with ⟨oldOwed, sOwed0, hgetOwed, h⟩
  have hsOwed0 : sOwed0 = s := success_state_eq _ _ _ _ hgetOwed
  have holdOwed : oldOwed = s.storageMap2 8 sender sender :=
    getMapping2_value_of_success SuperfluidCFA.flowOwedDeposits sender sender _ _ _ hgetOwed
  subst sOwed0
  subst oldOwed
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  have hsplit : ∃ sWrites,
      (writeFlowFields sender sender newRate newDeposit
        (s.storageMap2 8 sender sender) timestamp).run s = ContractResult.success () sWrites ∧
      (Verity.bind
        (SuperfluidCFA._updateAccountFlowState sender
          (sub (s.storageMap2 6 sender sender) newRate)
          (add (sub newDeposit (s.storageMap2 7 sender sender)) (s.storageMap2 8 sender sender)) 0 timestamp)
        (fun _ => SuperfluidCFA._updateAccountFlowState sender
          (sub newRate (s.storageMap2 6 sender sender)) 0 0 timestamp)).run sWrites =
        ContractResult.success () t := by
    split at h
    next htime =>
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sTime, htimeWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sRate, hrateWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sDeposit, hdepositWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sWrites, howedWrite, htail⟩
      have hsTime := success_state_eq _ _ _ _ htimeWrite
      have hsRate := success_state_eq _ _ _ _ hrateWrite
      have hsDeposit := success_state_eq _ _ _ _ hdepositWrite
      have hsWrites := success_state_eq _ _ _ _ howedWrite
      subst sTime
      subst sRate
      subst sDeposit
      refine ⟨sWrites, ?_, htail⟩
      unfold writeFlowFields
      rw [if_pos (by simpa using htime)]
      rw [hsWrites]
      rfl
    next htime =>
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sTime, htimeWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sRate, hrateWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sDeposit, hdepositWrite, h⟩
      rcases bind_success_elim _ _ _ _ _ h with ⟨⟨⟩, sWrites, howedWrite, htail⟩
      have hsTime := success_state_eq _ _ _ _ htimeWrite
      have hsRate := success_state_eq _ _ _ _ hrateWrite
      have hsDeposit := success_state_eq _ _ _ _ hdepositWrite
      have hsWrites := success_state_eq _ _ _ _ howedWrite
      subst sTime
      subst sRate
      subst sDeposit
      refine ⟨sWrites, ?_, htail⟩
      unfold writeFlowFields
      rw [if_neg (by simpa using htime)]
      rw [hsWrites]
      rfl
  rcases hsplit with ⟨sWrites, hwrite, h⟩
  have hwriteObs := flowWrite_observations s sWrites sender sender newRate newDeposit
    (s.storageMap2 8 sender sender) timestamp hwrite
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, sSender, hsender, hreceiver⟩
  have hsenderObs := updateAccountFlowState_observations sWrites sSender sender
    (sub (s.storageMap2 6 sender sender) newRate)
    (add (sub newDeposit (s.storageMap2 7 sender sender)) (s.storageMap2 8 sender sender)) 0 timestamp hsender
  have hreceiverObs := updateAccountFlowState_observations sSender t sender
    (sub newRate (s.storageMap2 6 sender sender)) 0 0 timestamp hreceiver
  have hsenderMap2 : sSender.storageMap2 = sWrites.storageMap2 := by
    rw [success_state_eq _ _ _ _ hsender]
    exact updateAccountFlowState_map2_preserving _ _ _ _ _ _
  have hreceiverMap2 : t.storageMap2 = sSender.storageMap2 := by
    rw [success_state_eq _ _ _ _ hreceiver]
    exact updateAccountFlowState_map2_preserving _ _ _ _ _ _
  unfold ChangeFlowObs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pairCfaProjectionAt
    rw [hreceiverObs.1, hsenderObs.1]
    simpa [cfaProjectionAt, hwriteObs.1]
  · unfold pairNetFlowRate
    have hfinalRate : t.storageMap 1 sender = s.storageMap 1 sender := by
      rw [hreceiverObs.2.1, hsenderObs.2.1, hwriteObs.1]
      exact opposite_rate_deltas_sequential_cancel _ _ _
    rw [hfinalRate]
  · intro slotIndex query hquerySender hqueryReceiver
    calc
      t.storageMap slotIndex query = sSender.storageMap slotIndex query :=
        hreceiverObs.2.2 slotIndex query hqueryReceiver
      _ = sWrites.storageMap slotIndex query :=
        hsenderObs.2.2 slotIndex query hquerySender
      _ = s.storageMap slotIndex query := by rw [hwriteObs.1]
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.2.2.1
  · rw [hreceiverMap2, hsenderMap2]
    exact hwriteObs.2.2.2.2.2.2
  · exact updateAccountFlowState_timestamp_bound sWrites sSender sender
      (sub (s.storageMap2 6 sender sender) newRate)
      (add (sub newDeposit (s.storageMap2 7 sender sender)) (s.storageMap2 8 sender sender)) 0
      timestamp hsender

private theorem changeFlow_storage_preserving
    (sender receiver : Address) (newRate newDeposit timestamp : Uint256) :
    StoragePreserving (SuperfluidCFA._changeFlow sender receiver newRate newDeposit timestamp) := by
  unfold SuperfluidCFA._changeFlow
  apply storage_preserving_bind
  · exact storage_preserving_getMapping2 _ _ _
  intro oldRate
  apply storage_preserving_bind
  · exact storage_preserving_getMapping2 _ _ _
  intro oldDeposit
  apply storage_preserving_bind
  · exact storage_preserving_getMapping2 _ _ _
  intro oldOwed
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  dsimp
  split
  all_goals
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_setMapping2 _ _ _ _
    intro _
    apply storage_preserving_bind
    · exact updateAccountFlowState_storage_preserving _ _ _ _ _
    intro _
    exact updateAccountFlowState_storage_preserving _ _ _ _ _

private theorem changeFlow_account_environment_preserving
    (sender receiver : Address) (newRate newDeposit timestamp : Uint256) :
    AccountEnvironmentPreserving
      (SuperfluidCFA._changeFlow sender receiver newRate newDeposit timestamp) := by
  unfold SuperfluidCFA._changeFlow
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping2 _ _ _
  intro oldRate
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping2 _ _ _
  intro oldDeposit
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping2 _ _ _
  intro oldOwed
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  dsimp
  split
  all_goals
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_setMapping2 _ _ _ _
    intro _
    apply account_environment_preserving_bind
    · exact updateAccountFlowState_account_environment_preserving _ _ _ _ _
    intro _
    exact updateAccountFlowState_account_environment_preserving _ _ _ _ _

/-! Public-wrapper read-only components.  Keeping these separate lets the
outer proofs expose only the successful `_changeFlow` transition. -/

private theorem sourceEnvironment_preserving
    (sender receiver : Address) (liquidationPeriod minimumDeposit : Uint256) :
    StatePreserving (SuperfluidCFA._requireSourceEnvironment
      sender receiver liquidationPeriod minimumDeposit) := by
  unfold SuperfluidCFA._requireSourceEnvironment
  apply preserving_bind
  · exact preserving_getStorage _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getStorage _
  intro _
  apply preserving_bind
  · exact preserving_getStorage _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  exact preserving_require _ _

private theorem directOuterHostContext_preserving (sender : Address) :
    StatePreserving (SuperfluidCFA._requireDirectOuterHostContext sender) := by
  unfold SuperfluidCFA._requireDirectOuterHostContext
  apply preserving_bind
  · exact preserving_getStorage _
  intro _
  apply preserving_bind
  · exact preserving_getStorage _
  intro _
  apply preserving_bind
  · exact preserving_getStorage _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  exact preserving_require _ _

private theorem emptyFlow_preserving (sender receiver : Address) :
    StatePreserving (SuperfluidCFA._requireEmptyFlow sender receiver) := by
  unfold SuperfluidCFA._requireEmptyFlow
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  exact preserving_require _ _

private theorem emptyFlow_zero_owed_of_success
    (s t : ContractState) (sender receiver : Address)
    (h : (SuperfluidCFA._requireEmptyFlow sender receiver).run s =
      ContractResult.success () t) :
    s.storageMap2 8 sender receiver = 0 := by
  unfold SuperfluidCFA._requireEmptyFlow at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping2 _ _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping2 _ _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping2 _ _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping2 _ _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨owed, owedState, hgetOwed, h⟩
  have hvalue : owed = s.storageMap2 8 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowOwedDeposits sender receiver _ _ _ hgetOwed
  have howedState : owedState = s := success_state_eq _ _ _ _ hgetOwed
  subst owedState
  subst owed
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  have hcond := Verity.Proofs.Stdlib.Automation.require_success_implies_cond
    (s.storageMap2 8 sender receiver == 0) "CFA_EMPTY_FLOW_OWED" s
    (by rw [h]; rfl)
  simpa using hcond

private theorem existingZeroOwedFlow_preserving (sender receiver : Address) :
    StatePreserving (SuperfluidCFA._requireExistingZeroOwedFlow sender receiver) := by
  unfold SuperfluidCFA._requireExistingZeroOwedFlow
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping2 _ _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  exact preserving_require _ _

private theorem existingZeroOwedFlow_success_exists
    (s t : ContractState) (sender receiver : Address)
    (h : (SuperfluidCFA._requireExistingZeroOwedFlow sender receiver).run s =
      ContractResult.success () t) :
    s.storageMap2 9 sender receiver = 1 ∧
      s.storageMap2 6 sender receiver ≠ 0 ∧
      s.storageMap2 6 sender receiver ≤ 39614081257132168796771975167 ∧
      s.storageMap2 8 sender receiver = 0 ∧
      t = s := by
  have ht : t = s := by
    rw [success_state_eq _ _ _ _ h]
    exact existingZeroOwedFlow_preserving sender receiver s
  unfold SuperfluidCFA._requireExistingZeroOwedFlow at h
  simp only [Bind.bind] at h
  rcases bind_success_elim _ _ _ _ _ h with ⟨existsWord, s₁, hget, h⟩
  have hs₁ : s₁ = s := success_state_eq _ _ _ _ hget
  have hvalue : existsWord = s.storageMap2 9 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowExists sender receiver _ _ _ hget
  subst s₁
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping2 _ _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨rateWord, s₂, hgetRate, h⟩
  have hs₂ : s₂ = s := success_state_eq _ _ _ _ hgetRate
  have hrateValue : rateWord = s.storageMap2 6 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowRates sender receiver _ _ _ hgetRate
  subst s₂
  subst rateWord
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping2 _ _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨owedWord, s₃, hgetOwed, h⟩
  have hs₃ : s₃ = s := success_state_eq _ _ _ _ hgetOwed
  have howedValue : owedWord = s.storageMap2 8 sender receiver :=
    getMapping2_value_of_success SuperfluidCFA.flowOwedDeposits sender receiver _ _ _ hgetOwed
  subst s₃
  subst owedWord
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, existsState, hexistsReq, h⟩
  have hexistsState : existsState = s := by
    rw [success_state_eq _ _ _ _ hexistsReq]
    exact preserving_require _ _ s
  have hcond : (existsWord == 1) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (existsWord == 1) "CFA_FLOW_DOES_NOT_EXIST" s (by rw [hexistsReq]; rfl)
  have hexists : existsWord = 1 := by simpa using hcond
  subst existsState
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, rateState, hrateReq, h⟩
  have hrateState : rateState = s := by
    rw [success_state_eq _ _ _ _ hrateReq]
    exact preserving_require _ _ s
  have hrateCond :
      (s.storageMap2 6 sender receiver != 0 &&
        s.storageMap2 6 sender receiver <= 39614081257132168796771975167) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (s.storageMap2 6 sender receiver != 0 &&
        s.storageMap2 6 sender receiver <= 39614081257132168796771975167)
      "CFA_FLOW_RATE_PACKING" s (by rw [hrateReq]; rfl)
  have hrate : s.storageMap2 6 sender receiver ≠ 0 ∧
      s.storageMap2 6 sender receiver ≤ 39614081257132168796771975167 := by
    simpa using hrateCond
  subst rateState
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  have howedCond : (s.storageMap2 8 sender receiver == 0) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (s.storageMap2 8 sender receiver == 0) "CFA_NON_APP_OWED_DEPOSIT" s
      (by rw [h]; rfl)
  have howed : s.storageMap2 8 sender receiver = 0 := by simpa using howedCond
  exact ⟨hvalue.symm.trans hexists, hrate.1, hrate.2, howed, ht⟩

private theorem sourceAppCreditBase_preserving (flowRate liquidationPeriod : Uint256) :
    StatePreserving (SuperfluidCFA._calculateSourceAppCreditBase flowRate liquidationPeriod) := by
  unfold SuperfluidCFA._calculateSourceAppCreditBase
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  dsimp
  split
  · exact preserving_pure _
  · split <;> exact preserving_pure _

private theorem sourceDeposit_preserving
    (flowRate liquidationPeriod minimumDeposit : Uint256) :
    StatePreserving (SuperfluidCFA._calculateSourceDeposit
      flowRate liquidationPeriod minimumDeposit) := by
  unfold SuperfluidCFA._calculateSourceDeposit
  apply preserving_bind
  · exact sourceAppCreditBase_preserving _ _
  intro _
  dsimp
  split <;> exact preserving_pure _

private theorem availableNonnegative_preserving (account : Address) (timestamp : Uint256) :
    StatePreserving (SuperfluidCFA._requireCfaOnlyAvailableNonnegative account timestamp) := by
  unfold SuperfluidCFA._requireCfaOnlyAvailableNonnegative
  apply preserving_bind
  · exact canonical_preserving _
  intro _
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro _
  apply preserving_bind
  · exact preserving_getMapping _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  apply preserving_bind
  · exact preserving_require _ _
  intro _
  dsimp
  split
  · apply preserving_bind
    · exact preserving_require _ _
    intro _
    apply preserving_bind
    · exact preserving_require _ _
    intro _
    exact preserving_require _ _
  · apply preserving_bind
    · exact preserving_pure _
    intro _
    apply preserving_bind
    · exact preserving_require _ _
    intro _
    exact preserving_require _ _

private theorem createFlowNonApp_storage_preserving
    (sender receiver : Address) (newRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    StoragePreserving (SuperfluidCFA.createFlowNonApp sender receiver newRate liquidationPeriod
      minimumDeposit timestamp) := by
  unfold SuperfluidCFA.createFlowNonApp
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (directOuterHostContext_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (emptyFlow_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceDeposit_preserving _ _ _)
  intro newDeposit
  apply storage_preserving_bind
  · exact changeFlow_storage_preserving _ _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping2 _ _ _ _
  intro _
  exact state_preserving_storage (availableNonnegative_preserving _ _)

private theorem createFlowNonApp_account_environment_preserving
    (sender receiver : Address) (newRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    AccountEnvironmentPreserving (SuperfluidCFA.createFlowNonApp sender receiver newRate
      liquidationPeriod minimumDeposit timestamp) := by
  unfold SuperfluidCFA.createFlowNonApp
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (directOuterHostContext_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (emptyFlow_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceDeposit_preserving _ _ _)
  intro newDeposit
  apply account_environment_preserving_bind
  · exact changeFlow_account_environment_preserving _ _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping2 _ _ _ _
  intro _
  exact state_preserving_account_environment (availableNonnegative_preserving _ _)

private theorem updateFlowNonApp_storage_preserving
    (sender receiver : Address) (newRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    StoragePreserving (SuperfluidCFA.updateFlowNonApp sender receiver newRate liquidationPeriod
      minimumDeposit timestamp) := by
  unfold SuperfluidCFA.updateFlowNonApp
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (directOuterHostContext_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (existingZeroOwedFlow_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceDeposit_preserving _ _ _)
  intro newDeposit
  apply storage_preserving_bind
  · exact changeFlow_storage_preserving _ _ _ _ _
  intro _
  exact state_preserving_storage (availableNonnegative_preserving _ _)

private theorem updateFlowNonApp_account_environment_preserving
    (sender receiver : Address) (newRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    AccountEnvironmentPreserving (SuperfluidCFA.updateFlowNonApp sender receiver newRate
      liquidationPeriod minimumDeposit timestamp) := by
  unfold SuperfluidCFA.updateFlowNonApp
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (directOuterHostContext_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (existingZeroOwedFlow_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceDeposit_preserving _ _ _)
  intro newDeposit
  apply account_environment_preserving_bind
  · exact changeFlow_account_environment_preserving _ _ _ _ _
  intro _
  exact state_preserving_account_environment (availableNonnegative_preserving _ _)

private theorem deleteFlowNonAppBySender_storage_preserving
    (sender receiver : Address) (timestamp : Uint256) :
    StoragePreserving (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp) := by
  unfold SuperfluidCFA.deleteFlowNonAppBySender
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getStorage _
  intro liquidationPeriod
  apply storage_preserving_bind
  · exact storage_preserving_getStorage _
  intro minimumDeposit
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (directOuterHostContext_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (existingZeroOwedFlow_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (availableNonnegative_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact changeFlow_storage_preserving _ _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping2 _ _ _ _
  intro _
  exact state_preserving_storage (availableNonnegative_preserving _ _)

private theorem deleteFlowNonAppBySender_account_environment_preserving
    (sender receiver : Address) (timestamp : Uint256) :
    AccountEnvironmentPreserving
      (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp) := by
  unfold SuperfluidCFA.deleteFlowNonAppBySender
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getStorage _
  intro liquidationPeriod
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getStorage _
  intro minimumDeposit
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (directOuterHostContext_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (existingZeroOwedFlow_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (availableNonnegative_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact changeFlow_account_environment_preserving _ _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping2 _ _ _ _
  intro _
  exact state_preserving_account_environment (availableNonnegative_preserving _ _)

private theorem packed_rate_positive (rate : Uint256)
    (hvalid : rate != 0 && rate <= 39614081257132168796771975167) :
    packFlowData 0 rate 0 0 > 0 := by
  have ⟨hrne, hrle⟩ : rate ≠ 0 ∧ rate ≤ 39614081257132168796771975167 := by
    simpa using hvalid
  have hrvalne : rate.val ≠ 0 := by
    intro hzero
    apply hrne
    apply Verity.Core.Uint256.ext
    simpa using hzero
  have hrpos : 0 < rate.val := Nat.pos_of_ne_zero hrvalne
  have hrle' : rate.val ≤ 39614081257132168796771975167 := by
    simpa [Verity.Core.Uint256.le_def] using hrle
  have hrate : rate.val < 79228162514264337593543950336 := by omega
  have hprod : rate.val * 340282366920938463463374607431768211456 <
      Verity.Core.Uint256.modulus := by
    rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    omega
  have hrmod : rate.val % Verity.Core.Uint256.modulus = rate.val :=
    Nat.mod_eq_of_lt rate.isLt
  have hfieldVal : (79228162514264337593543950336 : Uint256).val =
      79228162514264337593543950336 := by
    change 79228162514264337593543950336 % Verity.Core.Uint256.modulus =
      79228162514264337593543950336
    exact Nat.mod_eq_of_lt (by
      rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      norm_num)
  have hscaleVal : (340282366920938463463374607431768211456 : Uint256).val =
      340282366920938463463374607431768211456 := by
    change 340282366920938463463374607431768211456 % Verity.Core.Uint256.modulus =
      340282366920938463463374607431768211456
    exact Nat.mod_eq_of_lt (by
      rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      norm_num)
  have hpack : packFlowData 0 rate 0 0 =
      mul (mod rate 79228162514264337593543950336) 340282366920938463463374607431768211456 := by
    unfold packFlowData
    simp [Verity.Core.Uint256.add, Verity.Core.Uint256.mul, Verity.Core.Uint256.div,
      Verity.Core.Uint256.mod, Verity.Core.Uint256.ofNat]
  rw [hpack]
  change 0 <
    (rate.val % (79228162514264337593543950336 : Uint256).val %
      Verity.Core.Uint256.modulus *
      (340282366920938463463374607431768211456 : Uint256).val) %
      Verity.Core.Uint256.modulus
  rw [hfieldVal, hscaleVal, Nat.mod_eq_of_lt hrate, hrmod,
    Nat.mod_eq_of_lt hprod]
  exact Nat.mul_pos hrpos (by norm_num)

/-- The decoded deposit field occupies only bits 32 through 95. -/
private theorem stored_flow_deposit_lt (deposit : Uint256) :
    mul (mod (div deposit 4294967296) 18446744073709551616) 4294967296 <
      79228162514264337593543950336 := by
  have hmodulus : Verity.Core.Uint256.modulus =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  have hfield : (79228162514264337593543950336 : Uint256).val =
      79228162514264337593543950336 := by
    change 79228162514264337593543950336 % Verity.Core.Uint256.modulus =
      79228162514264337593543950336
    rw [hmodulus]
  have hdivisor : (4294967296 : Uint256).val = 4294967296 := by
    change 4294967296 % Verity.Core.Uint256.modulus = 4294967296
    rw [hmodulus]
  have hfieldModulus : (18446744073709551616 : Uint256).val = 18446744073709551616 := by
    change 18446744073709551616 % Verity.Core.Uint256.modulus = 18446744073709551616
    rw [hmodulus]
  unfold mul mod div
  simp [Verity.Core.Uint256.mul, Verity.Core.Uint256.mod, Verity.Core.Uint256.div,
    Verity.Core.Uint256.ofNat]
  rw [hfield, hdivisor, hfieldModulus]
  simp only [if_neg (by norm_num : 18446744073709551616 ≠ 0),
    if_neg (by norm_num : 4294967296 ≠ 0)]
  have hfieldValue : deposit.val / 4294967296 % Verity.Core.Uint256.modulus %
      18446744073709551616 < 18446744073709551616 :=
    Nat.mod_lt _ (by norm_num)
  have hfieldNoWrap : deposit.val / 4294967296 % Verity.Core.Uint256.modulus %
      18446744073709551616 % Verity.Core.Uint256.modulus =
      deposit.val / 4294967296 % Verity.Core.Uint256.modulus % 18446744073709551616 := by
    apply Nat.mod_eq_of_lt
    rw [hmodulus]
    omega
  rw [hfieldNoWrap]
  have hproduct : (deposit.val / 4294967296 % Verity.Core.Uint256.modulus %
      18446744073709551616) * 4294967296 < Verity.Core.Uint256.modulus := by
    rw [hmodulus]
    omega
  rw [Nat.mod_eq_of_lt hproduct]
  omega

/-- Under the canonical uint32/int96/uint64 field bounds, a positive rate
contributes a nonzero, non-overlapping packed-flow word. -/
private theorem packed_flow_positive
    (timestamp rate deposit : Uint256)
    (htimestamp : timestamp ≤ 4294967295)
    (hrateNe : rate ≠ 0)
    (hrateLe : rate ≤ 39614081257132168796771975167)
    (hdeposit : deposit < 79228162514264337593543950336) :
    packFlowData timestamp rate deposit 0 > 0 := by
  have htimestampVal : timestamp.val ≤ 4294967295 := by
    simpa [Verity.Core.Uint256.le_def] using htimestamp
  have hrateValNe : rate.val ≠ 0 := by
    intro hzero
    apply hrateNe
    apply Verity.Core.Uint256.ext
    simpa using hzero
  have hrateVal : rate.val ≤ 39614081257132168796771975167 := by
    simpa [Verity.Core.Uint256.le_def] using hrateLe
  have hdepositVal : deposit.val < 79228162514264337593543950336 := by
    simpa [Verity.Core.Uint256.lt_def] using hdeposit
  have hmodulus : Verity.Core.Uint256.modulus =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  have htimestampScale :
      (26959946667150639794667015087019630673637144422540572481103610249216 : Uint256).val =
        26959946667150639794667015087019630673637144422540572481103610249216 := by
    change 26959946667150639794667015087019630673637144422540572481103610249216 %
      Verity.Core.Uint256.modulus = 26959946667150639794667015087019630673637144422540572481103610249216
    rw [hmodulus]
  have hfield : (79228162514264337593543950336 : Uint256).val =
      79228162514264337593543950336 := by
    change 79228162514264337593543950336 % Verity.Core.Uint256.modulus =
      79228162514264337593543950336
    rw [hmodulus]
  have hrateScale : (340282366920938463463374607431768211456 : Uint256).val =
      340282366920938463463374607431768211456 := by
    change 340282366920938463463374607431768211456 % Verity.Core.Uint256.modulus =
      340282366920938463463374607431768211456
    rw [hmodulus]
  have hdepositDivisor : (4294967296 : Uint256).val = 4294967296 := by
    change 4294967296 % Verity.Core.Uint256.modulus = 4294967296
    rw [hmodulus]
  have hdepositScale : (18446744073709551616 : Uint256).val = 18446744073709551616 := by
    change 18446744073709551616 % Verity.Core.Uint256.modulus = 18446744073709551616
    rw [hmodulus]
  have hrateLtField : rate.val < 79228162514264337593543950336 := by omega
  have hdepositDivLt : deposit.val / 4294967296 < 18446744073709551616 := by omega
  have htotalLt : timestamp.val * 26959946667150639794667015087019630673637144422540572481103610249216 +
      (rate.val * 340282366920938463463374607431768211456 +
        (deposit.val / 4294967296) * 18446744073709551616) < Verity.Core.Uint256.modulus := by
    rw [hmodulus]
    omega
  unfold packFlowData
  simp [Verity.Core.Uint256.add, Verity.Core.Uint256.mul, Verity.Core.Uint256.div,
    Verity.Core.Uint256.mod, Verity.Core.Uint256.ofNat]
  rw [htimestampScale, hfield, hrateScale, hdepositDivisor, hdepositScale]
  simp only [if_neg (by norm_num : 79228162514264337593543950336 ≠ 0),
    if_neg (by norm_num : 4294967296 ≠ 0)]
  rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] at *
  have hrateMod : rate.val % 2 ^ 256 = rate.val := by
    apply Nat.mod_eq_of_lt
    omega
  have hdepositMod : deposit.val / 4294967296 % 2 ^ 256 = deposit.val / 4294967296 := by
    apply Nat.mod_eq_of_lt
    omega
  rw [Nat.mod_eq_of_lt hrateLtField, hrateMod, hdepositMod,
    Nat.mod_eq_of_lt htotalLt]
  exact Nat.pos_of_ne_zero (by omega)

private theorem sourcePost_of_model_frame
    (source : PinnedSourceState) (base post : ContractState) (sender receiver : Address)
    (hmodel : sourceModelRelation source base sender receiver)
    (hpackedExists :
      packFlowData (post.storageMap2 5 sender receiver) (post.storageMap2 6 sender receiver)
        (post.storageMap2 7 sender receiver) (post.storageMap2 8 sender receiver) > 0 ↔
      post.storageMap2 9 sender receiver = 1)
    (hkey : post.storageMap2 27 sender receiver = base.storageMap2 27 sender receiver)
    (hstorage : post.storage = base.storage)
    (hmaps : ∀ slotIndex account, 4 < slotIndex →
      post.storageMap slotIndex account = base.storageMap slotIndex account) :
    sourcePostRelation source post sender receiver := by
  rcases hmodel with ⟨_, _, _, _, _, _, hkeyBase, hcfaBase, hcfaOne, hgovLiquidationBase,
    hgovMinimumBase, hhostIsAppSenderBase, hhostIsAppReceiverBase, hhostIsJailedBase,
    hhostBeforeCreatedBase, hhostAfterCreatedBase, hhostCreditUsedBase, hhostLevelBase,
    hhostActorBase, hhostAppAddressBase, hhostContextBase, hhostDeleteEnabledBase,
    hhostNestedBase, hhostTokenMatchesBase, hhostCreditGrantedBase, hhostAdditionalCreditBase,
    hhostSelfDeletingBase, houterDirectBase, houterTokenBase, houterActorBase⟩
  have hkeyPost : source.flowKeyMatches sender receiver = post.storageMap2 27 sender receiver :=
    hkeyBase.trans hkey.symm
  have hcfaPost : source.cfaOnlyActiveAgreement = post.storage 26 :=
    hcfaBase.trans (congrFun hstorage 26).symm
  have hgovLiquidationPost : source.governanceLiquidationPeriod = post.storage 24 :=
    hgovLiquidationBase.trans (congrFun hstorage 24).symm
  have hgovMinimumPost : source.governanceMinimumDeposit = post.storage 25 :=
    hgovMinimumBase.trans (congrFun hstorage 25).symm
  have hhostIsAppSender : source.hostIsApp sender = post.storageMap 10 sender :=
    hhostIsAppSenderBase.trans (hmaps 10 sender (by decide)).symm
  have hhostIsAppReceiver : source.hostIsApp receiver = post.storageMap 10 receiver :=
    hhostIsAppReceiverBase.trans (hmaps 10 receiver (by decide)).symm
  have hhostIsJailed : source.hostIsJailed receiver = post.storageMap 11 receiver :=
    hhostIsJailedBase.trans (hmaps 11 receiver (by decide)).symm
  have hhostBeforeCreated : source.hostBeforeCreatedNoop receiver = post.storageMap 12 receiver :=
    hhostBeforeCreatedBase.trans (hmaps 12 receiver (by decide)).symm
  have hhostAfterCreated : source.hostAfterCreatedEnabled receiver = post.storageMap 13 receiver :=
    hhostAfterCreatedBase.trans (hmaps 13 receiver (by decide)).symm
  have hhostCreditUsed : source.hostCallbackCreditUsed receiver = post.storageMap 14 receiver :=
    hhostCreditUsedBase.trans (hmaps 14 receiver (by decide)).symm
  have hhostLevel : source.hostCallbackLevel receiver = post.storageMap 15 receiver :=
    hhostLevelBase.trans (hmaps 15 receiver (by decide)).symm
  have hhostActor : source.hostCallbackActor receiver = post.storageMap 16 receiver :=
    hhostActorBase.trans (hmaps 16 receiver (by decide)).symm
  have hhostAppAddress : source.hostCallbackAppAddress receiver = post.storageMap 17 receiver :=
    hhostAppAddressBase.trans (hmaps 17 receiver (by decide)).symm
  have hhostContext : source.hostIsAppCallbackContext receiver = post.storageMap 18 receiver :=
    hhostContextBase.trans (hmaps 18 receiver (by decide)).symm
  have hhostDeleteEnabled : source.hostContextualDeleteEnabled receiver = post.storageMap 19 receiver :=
    hhostDeleteEnabledBase.trans (hmaps 19 receiver (by decide)).symm
  have hhostNested : source.hostNestedCallbackSuppressed receiver = post.storageMap 20 receiver :=
    hhostNestedBase.trans (hmaps 20 receiver (by decide)).symm
  have hhostTokenMatches : source.hostAppCreditTokenMatches receiver = post.storageMap 21 receiver :=
    hhostTokenMatchesBase.trans (hmaps 21 receiver (by decide)).symm
  have hhostCreditGranted : source.hostAppCreditGranted receiver = post.storageMap 22 receiver :=
    hhostCreditGrantedBase.trans (hmaps 22 receiver (by decide)).symm
  have hhostAdditionalCredit : source.hostAdditionalAppCredit receiver = post.storageMap 23 receiver :=
    hhostAdditionalCreditBase.trans (hmaps 23 receiver (by decide)).symm
  have hhostSelfDeleting : source.hostIsSelfDeletingFlowApp receiver = post.storageMap 28 receiver :=
    hhostSelfDeletingBase.trans (hmaps 28 receiver (by decide)).symm
  have houterDirect : source.hostOuterIsDirectCallContext = post.storage 29 :=
    houterDirectBase.trans (congrFun hstorage 29).symm
  have houterToken : source.hostOuterAppCreditToken = post.storage 30 :=
    houterTokenBase.trans (congrFun hstorage 30).symm
  have houterActor : source.hostOuterActor = post.storage 31 :=
    houterActorBase.trans (congrFun hstorage 31).symm
  simp [sourcePostRelation, sourceModelRelation, repackSourcePost]
  aesop

private theorem pinned_source_path_storage26
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (timestamp : Uint256)
    (h : pinnedSourcePathRelation source s sender receiver timestamp) :
    s.storage 26 = 1 := by
  have hmodel := h.1
  simp [sourceModelRelation] at hmodel
  aesop

private def WrapperFlowObs
    (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp existsWord : Uint256) : Prop :=
  ∃ changed,
    ChangeFlowObs base changed sender receiver newRate newDeposit timestamp ∧
    post = (setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState changed ∧
    base.storageMap2 8 sender receiver = 0

private theorem createFlowNonApp_observations
    (s t : ContractState) (sender receiver : Address)
    (newRate liquidationPeriod minimumDeposit timestamp : Uint256)
    (h : (SuperfluidCFA.createFlowNonApp sender receiver newRate liquidationPeriod
      minimumDeposit timestamp).run s = ContractResult.success () t) :
    ∃ newDeposit, WrapperFlowObs s t sender receiver newRate newDeposit timestamp 1 ∧
      newRate ≠ 0 ∧ newRate ≤ 39614081257132168796771975167 := by
  unfold SuperfluidCFA.createFlowNonApp at h
  simp only [Bind.bind] at h
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₁, hreceiver, h⟩
  have hs₁ : s₁ = s := by
    rw [success_state_eq _ _ _ _ hreceiver]
    exact preserving_require _ _ s
  subst s₁
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₂, hdistinctReq, h⟩
  have hs₂ : s₂ = s := by
    rw [success_state_eq _ _ _ _ hdistinctReq]
    exact preserving_require _ _ s
  have hdistinctCond : (sender != receiver) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (sender != receiver) "CFA_NO_SELF_FLOW" s (by rw [hdistinctReq]; rfl)
  have hdistinct : sender ≠ receiver := by
    intro heq
    subst receiver
    simp at hdistinctCond
  subst s₂
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₃, hrateReq, h⟩
  have hs₃ : s₃ = s := by
    rw [success_state_eq _ _ _ _ hrateReq]
    exact preserving_require _ _ s
  have hrateCond : (newRate != 0 && newRate <= 39614081257132168796771975167) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (newRate != 0 && newRate <= 39614081257132168796771975167) "CFA_INVALID_FLOW_RATE" s
      (by rw [hrateReq]; rfl)
  have hrate : newRate ≠ 0 ∧ newRate ≤ 39614081257132168796771975167 := by
    simpa using hrateCond
  subst s₃
  rcases preserving_bind_tail _ _ _ _ _
    (sourceEnvironment_preserving sender receiver liquidationPeriod minimumDeposit) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (directOuterHostContext_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, emptyState, hempty, h⟩
  have hemptyState : emptyState = s := by
    rw [success_state_eq _ _ _ _ hempty]
    exact emptyFlow_preserving sender receiver s
  have hemptyOwed : s.storageMap2 8 sender receiver = 0 :=
    emptyFlow_zero_owed_of_success s emptyState sender receiver hempty
  subst emptyState
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _
    (sourceDeposit_preserving newRate liquidationPeriod minimumDeposit) h with ⟨newDeposit, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, changed, hchange, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, existsState, hexists, h⟩
  have havailable := h
  have ht : t = existsState := by
    rw [success_state_eq _ _ _ _ havailable]
    exact availableNonnegative_preserving sender timestamp existsState
  refine ⟨newDeposit, ?_, hrate.1, hrate.2⟩
  refine ⟨changed, changeFlow_observations s changed sender receiver newRate newDeposit
    timestamp hdistinct hchange, ?_, hemptyOwed⟩
  have hexistsState : existsState =
      (setMapping2 SuperfluidCFA.flowExists sender receiver 1).runState changed :=
    success_state_eq _ _ _ _ hexists
  rw [ht, hexistsState]

private theorem updateFlowNonApp_observations
    (s t : ContractState) (sender receiver : Address)
    (newRate liquidationPeriod minimumDeposit timestamp : Uint256)
    (h : (SuperfluidCFA.updateFlowNonApp sender receiver newRate liquidationPeriod
      minimumDeposit timestamp).run s = ContractResult.success () t) :
    ∃ newDeposit,
      ChangeFlowObs s t sender receiver newRate newDeposit timestamp ∧
      s.storageMap2 9 sender receiver = 1 ∧
      newRate ≠ 0 ∧ newRate ≤ 39614081257132168796771975167 ∧
      s.storageMap2 8 sender receiver = 0 := by
  unfold SuperfluidCFA.updateFlowNonApp at h
  simp only [Bind.bind] at h
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₁, hreceiver, h⟩
  have hs₁ : s₁ = s := by
    rw [success_state_eq _ _ _ _ hreceiver]
    exact preserving_require _ _ s
  subst s₁
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₂, hdistinctReq, h⟩
  have hs₂ : s₂ = s := by
    rw [success_state_eq _ _ _ _ hdistinctReq]
    exact preserving_require _ _ s
  have hdistinctCond : (sender != receiver) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (sender != receiver) "CFA_NO_SELF_FLOW" s (by rw [hdistinctReq]; rfl)
  have hdistinct : sender ≠ receiver := by
    intro heq
    subst receiver
    simp at hdistinctCond
  subst s₂
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₃, hrateReq, h⟩
  have hs₃ : s₃ = s := by
    rw [success_state_eq _ _ _ _ hrateReq]
    exact preserving_require _ _ s
  have hrateCond : (newRate != 0 && newRate <= 39614081257132168796771975167) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (newRate != 0 && newRate <= 39614081257132168796771975167) "CFA_INVALID_FLOW_RATE" s
      (by rw [hrateReq]; rfl)
  have hrate : newRate ≠ 0 ∧ newRate ≤ 39614081257132168796771975167 := by
    simpa using hrateCond
  subst s₃
  rcases preserving_bind_tail _ _ _ _ _
    (sourceEnvironment_preserving sender receiver liquidationPeriod minimumDeposit) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (directOuterHostContext_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, existingState, hexisting, h⟩
  have hexistingObs := existingZeroOwedFlow_success_exists s existingState sender receiver hexisting
  have hexistingState : existingState = s := hexistingObs.2.2.2.2
  subst existingState
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _
    (sourceDeposit_preserving newRate liquidationPeriod minimumDeposit) h with ⟨newDeposit, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, changed, hchange, h⟩
  have hchangeObs := changeFlow_observations s changed sender receiver newRate newDeposit timestamp
    hdistinct hchange
  have ht : t = changed := by
    rw [success_state_eq _ _ _ _ h]
    exact availableNonnegative_preserving sender timestamp changed
  refine ⟨newDeposit, ?_, hexistingObs.1, hrate.1, hrate.2, hexistingObs.2.2.2.1⟩
  subst t
  exact hchangeObs

private theorem sourcePost_of_packed_exists
    (source : PinnedSourceState) (base post : ContractState) (sender receiver : Address)
    (hmodel : sourceModelRelation source base sender receiver)
    (hmaps : ∀ slotIndex account, 4 < slotIndex →
      post.storageMap slotIndex account = base.storageMap slotIndex account)
    (hkey : post.storageMap2 27 sender receiver = base.storageMap2 27 sender receiver)
    (hstorage : post.storage = base.storage)
    (hpacked : packFlowData (post.storageMap2 5 sender receiver)
      (post.storageMap2 6 sender receiver) (post.storageMap2 7 sender receiver)
      (post.storageMap2 8 sender receiver) > 0)
    (hexists : post.storageMap2 9 sender receiver = 1) :
    sourcePostRelation source post sender receiver := by
  apply sourcePost_of_model_frame source base post sender receiver hmodel
  · simp [hpacked, hexists]
  · exact hkey
  · exact hstorage
  · exact hmaps

private theorem setFlowExists_runState_storageMap
    (s : ContractState) (sender receiver : Address) (existsWord : Uint256) :
    ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState s).storageMap =
      s.storageMap := by
  rfl

private theorem setFlowExists_runState_rate
    (s : ContractState) (sender receiver : Address) (existsWord : Uint256) :
    ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState s).storageMap2 6
      sender receiver = s.storageMap2 6 sender receiver := by
  rfl

private theorem setFlowExists_runState_exists
    (s : ContractState) (sender receiver : Address) (existsWord : Uint256) :
    ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState s).storageMap2 9
      sender receiver = existsWord := by
  change (if 9 == SuperfluidCFA.flowExists.slot && sender == sender && receiver == receiver
    then existsWord else s.storageMap2 9 sender receiver) = existsWord
  simp [SuperfluidCFA.flowExists]

private theorem setFlowExists_runState_nonexists
    (s : ContractState) (sender receiver : Address) (existsWord : Uint256)
    (slotIndex : Nat) (hslot : slotIndex ≠ 9) :
    ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState s).storageMap2
      slotIndex sender receiver = s.storageMap2 slotIndex sender receiver := by
  change (if slotIndex == SuperfluidCFA.flowExists.slot && sender == sender && receiver == receiver
    then existsWord else s.storageMap2 slotIndex sender receiver) = s.storageMap2 slotIndex sender receiver
  simp [hslot, SuperfluidCFA.flowExists]

private theorem wrapperFlowObs_sourcePost
    (source : PinnedSourceState) (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp existsWord : Uint256)
    (hsource : pinnedSourcePathRelation source base sender receiver timestamp)
    (hobs : WrapperFlowObs base post sender receiver newRate newDeposit timestamp existsWord)
    (hrate : newRate ≠ 0) (hrateBound : newRate ≤ 39614081257132168796771975167)
    (hexists : existsWord = 1) (hstorage : post.storage = base.storage)
    (hmaps : ∀ slotIndex account, 4 < slotIndex →
      post.storageMap slotIndex account = base.storageMap slotIndex account) :
    sourcePostRelation source post sender receiver := by
  rcases hobs with ⟨changed, hchange, hpost, hbaseOwed⟩
  subst post
  refine sourcePost_of_packed_exists source base _ sender receiver hsource.1
    (by simpa using hmaps) ?_ (by simpa using hstorage) ?_ ?_
  · calc
      ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState changed).storageMap2
          27 sender receiver = changed.storageMap2 27 sender receiver :=
            setFlowExists_runState_nonexists _ _ _ _ 27 (by decide)
      _ = base.storageMap2 27 sender receiver := hchange.2.2.2.2.2.2.2.2.1
  · have htime :
        ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState changed).storageMap2
          5 sender receiver = timestamp := by
      rw [setFlowExists_runState_nonexists _ _ _ _ 5 (by decide)]
      rw [hchange.2.2.2.1]
      simp [hrate, hrateBound]
    have hrate' :
        ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState changed).storageMap2
          6 sender receiver = newRate := by
      rw [setFlowExists_runState_rate]
      exact hchange.2.2.2.2.1
    have hdeposit :
        ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState changed).storageMap2
          7 sender receiver =
          mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296 := by
      rw [setFlowExists_runState_nonexists _ _ _ _ 7 (by decide)]
      exact hchange.2.2.2.2.2.1
    have howed :
        ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState changed).storageMap2
          8 sender receiver = 0 := by
      rw [setFlowExists_runState_nonexists _ _ _ _ 8 (by decide)]
      rw [hchange.2.2.2.2.2.2.1, hbaseOwed]
    rw [htime, hrate', hdeposit, howed]
    exact packed_flow_positive timestamp newRate
      (mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296)
      hchange.2.2.2.2.2.2.2.2.2 hrate hrateBound (stored_flow_deposit_lt newDeposit)
  · rw [setFlowExists_runState_exists]
    exact hexists

private theorem wrapperFlowObs_projection
    (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp existsWord : Uint256)
    (hobs : WrapperFlowObs base post sender receiver newRate newDeposit timestamp existsWord) :
    pairCfaProjectionAt post sender receiver timestamp =
      pairCfaProjectionAt base sender receiver timestamp := by
  rcases hobs with ⟨changed, hchange, hpost, _⟩
  subst post
  simpa [pairCfaProjectionAt, cfaProjectionAt, setFlowExists_runState_storageMap] using hchange.1

private theorem wrapperFlowObs_pairRate
    (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp existsWord : Uint256)
    (hobs : WrapperFlowObs base post sender receiver newRate newDeposit timestamp existsWord) :
    pairNetFlowRate post sender receiver = pairNetFlowRate base sender receiver := by
  rcases hobs with ⟨changed, hchange, hpost, _⟩
  subst post
  simpa [pairNetFlowRate, setFlowExists_runState_storageMap] using hchange.2.1

private theorem wrapperFlowObs_frame
    (base post : ContractState) (sender receiver unrelated : Address)
    (newRate newDeposit timestamp existsWord : Uint256)
    (hunrelatedSender : unrelated ≠ sender) (hunrelatedReceiver : unrelated ≠ receiver)
    (hobs : WrapperFlowObs base post sender receiver newRate newDeposit timestamp existsWord) :
    ∀ slotIndex, post.storageMap slotIndex unrelated = base.storageMap slotIndex unrelated := by
  rcases hobs with ⟨changed, hchange, hpost, _⟩
  intro slotIndex
  rw [hpost, setFlowExists_runState_storageMap]
  exact hchange.2.2.1 slotIndex unrelated hunrelatedSender hunrelatedReceiver

theorem createNonApp_preserves_cfa_projection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    createNonAppPreservesCfaProjection source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold createNonAppPreservesCfaProjection
  intro hsource
  dsimp [runCreateNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  rcases createFlowNonApp_observations s
    ((SuperfluidCFA.createFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s).snd
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp heq with
    ⟨newDeposit, hobs, hrate, hrateBound⟩
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (createFlowNonApp_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (createFlowNonApp_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  exact ⟨wrapperFlowObs_sourcePost source s _ sender receiver flowRate newDeposit timestamp 1 hsource hobs
    hrate hrateBound rfl hframe.1 hframe.2,
    wrapperFlowObs_projection s _ sender receiver flowRate newDeposit timestamp 1 hobs⟩

theorem createNonApp_preserves_pair_net_flow_rate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    createNonAppPreservesPairNetFlowRate source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold createNonAppPreservesPairNetFlowRate
  intro hsource
  dsimp [runCreateNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  rcases createFlowNonApp_observations s
    ((SuperfluidCFA.createFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s).snd
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp heq with
    ⟨newDeposit, hobs, hrate, hrateBound⟩
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (createFlowNonApp_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (createFlowNonApp_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  exact ⟨wrapperFlowObs_sourcePost source s _ sender receiver flowRate newDeposit timestamp 1 hsource hobs
    hrate hrateBound rfl hframe.1 hframe.2,
    wrapperFlowObs_pairRate s _ sender receiver flowRate newDeposit timestamp 1 hobs⟩

theorem createNonApp_frames_unrelated_account
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    createNonAppFramesUnrelatedAccount source s sender receiver unrelated flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold createNonAppFramesUnrelatedAccount
  intro hsource hunrelatedSender hunrelatedReceiver
  dsimp [runCreateNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  rcases createFlowNonApp_observations s
    ((SuperfluidCFA.createFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s).snd
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp heq with
    ⟨newDeposit, hobs, hrate, hrateBound⟩
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (createFlowNonApp_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (createFlowNonApp_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  refine ⟨wrapperFlowObs_sourcePost source s _ sender receiver flowRate newDeposit timestamp 1 hsource hobs
    hrate hrateBound rfl hframe.1 hframe.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact wrapperFlowObs_frame s _ sender receiver unrelated flowRate newDeposit timestamp 1
      hunrelatedSender hunrelatedReceiver hobs 0
  · exact wrapperFlowObs_frame s _ sender receiver unrelated flowRate newDeposit timestamp 1
      hunrelatedSender hunrelatedReceiver hobs 1
  · exact wrapperFlowObs_frame s _ sender receiver unrelated flowRate newDeposit timestamp 1
      hunrelatedSender hunrelatedReceiver hobs 2
  · exact wrapperFlowObs_frame s _ sender receiver unrelated flowRate newDeposit timestamp 1
      hunrelatedSender hunrelatedReceiver hobs 3
  · exact wrapperFlowObs_frame s _ sender receiver unrelated flowRate newDeposit timestamp 1
      hunrelatedSender hunrelatedReceiver hobs 4

private theorem updateFlowObs_sourcePost
    (source : PinnedSourceState) (base post : ContractState) (sender receiver : Address)
    (newRate newDeposit timestamp : Uint256)
    (hsource : pinnedSourcePathRelation source base sender receiver timestamp)
    (hchange : ChangeFlowObs base post sender receiver newRate newDeposit timestamp)
    (hbaseExists : base.storageMap2 9 sender receiver = 1)
    (hbaseOwed : base.storageMap2 8 sender receiver = 0)
    (hrate : newRate ≠ 0) (hrateBound : newRate ≤ 39614081257132168796771975167)
    (hstorage : post.storage = base.storage)
    (hmaps : ∀ slotIndex account, 4 < slotIndex →
      post.storageMap slotIndex account = base.storageMap slotIndex account) :
    sourcePostRelation source post sender receiver := by
  refine sourcePost_of_packed_exists source base post sender receiver hsource.1 hmaps
    hchange.2.2.2.2.2.2.2.2.1 hstorage ?_ ?_
  · have htime : post.storageMap2 5 sender receiver = timestamp := by
      rw [hchange.2.2.2.1]
      simp [hrate, hrateBound]
    have hdeposit : post.storageMap2 7 sender receiver =
        mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296 :=
      hchange.2.2.2.2.2.1
    have howed : post.storageMap2 8 sender receiver = 0 := by
      rw [hchange.2.2.2.2.2.2.1, hbaseOwed]
    rw [htime, hchange.2.2.2.2.1, hdeposit, howed]
    exact packed_flow_positive timestamp newRate
      (mul (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296)
      hchange.2.2.2.2.2.2.2.2.2 hrate hrateBound (stored_flow_deposit_lt newDeposit)
  · exact hchange.2.2.2.2.2.2.2.1.trans hbaseExists

theorem updateNonApp_preserves_cfa_projection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    updateNonAppPreservesCfaProjection source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold updateNonAppPreservesCfaProjection
  intro hsource
  dsimp [runUpdateNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  rcases updateFlowNonApp_observations s
    ((SuperfluidCFA.updateFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s).snd
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp heq with
    ⟨newDeposit, hchange, hbaseExists, hrate, hrateBound, hbaseOwed⟩
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.updateFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (updateFlowNonApp_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (updateFlowNonApp_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  exact ⟨updateFlowObs_sourcePost source s _ sender receiver flowRate newDeposit timestamp hsource hchange
    hbaseExists hbaseOwed hrate hrateBound hframe.1 hframe.2, hchange.1⟩

theorem updateNonApp_preserves_pair_net_flow_rate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    updateNonAppPreservesPairNetFlowRate source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold updateNonAppPreservesPairNetFlowRate
  intro hsource
  dsimp [runUpdateNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  rcases updateFlowNonApp_observations s
    ((SuperfluidCFA.updateFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s).snd
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp heq with
    ⟨newDeposit, hchange, hbaseExists, hrate, hrateBound, hbaseOwed⟩
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.updateFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (updateFlowNonApp_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (updateFlowNonApp_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  exact ⟨updateFlowObs_sourcePost source s _ sender receiver flowRate newDeposit timestamp hsource hchange
    hbaseExists hbaseOwed hrate hrateBound hframe.1 hframe.2, hchange.2.1⟩

theorem updateNonApp_frames_unrelated_account
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    updateNonAppFramesUnrelatedAccount source s sender receiver unrelated flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold updateNonAppFramesUnrelatedAccount
  intro hsource hunrelatedSender hunrelatedReceiver
  dsimp [runUpdateNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  rcases updateFlowNonApp_observations s
    ((SuperfluidCFA.updateFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s).snd
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp heq with
    ⟨newDeposit, hchange, hbaseExists, hrate, hrateBound, hbaseOwed⟩
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.updateFlowNonApp sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (updateFlowNonApp_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (updateFlowNonApp_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  refine ⟨updateFlowObs_sourcePost source s _ sender receiver flowRate newDeposit timestamp hsource hchange
    hbaseExists hbaseOwed hrate hrateBound hframe.1 hframe.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hchange.2.2.1 0 unrelated hunrelatedSender hunrelatedReceiver
  · exact hchange.2.2.1 1 unrelated hunrelatedSender hunrelatedReceiver
  · exact hchange.2.2.1 2 unrelated hunrelatedSender hunrelatedReceiver
  · exact hchange.2.2.1 3 unrelated hunrelatedSender hunrelatedReceiver
  · exact hchange.2.2.1 4 unrelated hunrelatedSender hunrelatedReceiver

private def DeleteFlowObs
    (base post : ContractState) (sender receiver : Address) (timestamp : Uint256) : Prop :=
  ∃ changed,
    ChangeFlowObs base changed sender receiver 0 0 timestamp ∧
    base.storageMap2 9 sender receiver = 1 ∧
    base.storageMap2 6 sender receiver ≠ 0 ∧
    post = (setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed ∧
    base.storageMap2 8 sender receiver = 0

private theorem deleteFlowNonAppBySender_observations
    (s t : ContractState) (sender receiver : Address) (timestamp : Uint256)
    (h : (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp).run s =
      ContractResult.success () t) :
    DeleteFlowObs s t sender receiver timestamp := by
  unfold SuperfluidCFA.deleteFlowNonAppBySender at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getStorage _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getStorage _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _
    (sourceEnvironment_preserving sender receiver _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (directOuterHostContext_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, existingState, hexisting, h⟩
  have hexistingObs := existingZeroOwedFlow_success_exists s existingState sender receiver hexisting
  have hexistingState : existingState = s := hexistingObs.2.2.2.2
  subst existingState
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (availableNonnegative_preserving sender timestamp) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, changed, hchange, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, existsState, hexists, h⟩
  have ht : t = existsState := by
    rw [success_state_eq _ _ _ _ h]
    exact availableNonnegative_preserving sender timestamp existsState
  have hchangeObs : ChangeFlowObs s changed sender receiver 0 0 timestamp := by
    by_cases hdistinct : sender = receiver
    · subst receiver
      exact changeFlow_self_observations s changed sender 0 0 timestamp hchange
    · exact changeFlow_observations s changed sender receiver 0 0 timestamp hdistinct hchange
  refine ⟨changed, hchangeObs,
    hexistingObs.1, hexistingObs.2.1, ?_, hexistingObs.2.2.2.1⟩
  have hexistsState : existsState =
      (setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed :=
    success_state_eq _ _ _ _ hexists
  rw [ht, hexistsState]

private theorem deleteFlowObs_sourcePost
    (source : PinnedSourceState) (base post : ContractState) (sender receiver : Address)
    (timestamp : Uint256) (hsource : pinnedSourcePathRelation source base sender receiver timestamp)
    (hobs : DeleteFlowObs base post sender receiver timestamp)
    (hstorage : post.storage = base.storage)
    (hmaps : ∀ slotIndex account, 4 < slotIndex →
      post.storageMap slotIndex account = base.storageMap slotIndex account) :
    sourcePostRelation source post sender receiver := by
  rcases hobs with ⟨changed, hchange, _, _, hpost, hbaseOwed⟩
  subst post
  have htime :
      ((setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed).storageMap2
        5 sender receiver = 0 := by
    rw [setFlowExists_runState_nonexists _ _ _ _ 5 (by decide), hchange.2.2.2.1]
    simp
  have hrate :
      ((setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed).storageMap2
        6 sender receiver = 0 := by
    rw [setFlowExists_runState_rate, hchange.2.2.2.2.1]
  have hdeposit :
      ((setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed).storageMap2
        7 sender receiver = 0 := by
    rw [setFlowExists_runState_nonexists _ _ _ _ 7 (by decide), hchange.2.2.2.2.2.1]
    decide
  have howed :
      ((setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed).storageMap2
        8 sender receiver = 0 := by
    rw [setFlowExists_runState_nonexists _ _ _ _ 8 (by decide), hchange.2.2.2.2.2.2.1, hbaseOwed]
  refine sourcePost_of_model_frame source base _ sender receiver hsource.1 ?_ ?_
    (by simpa using hstorage) (by simpa using hmaps)
  · rw [htime, hrate, hdeposit, howed, setFlowExists_runState_exists]
    decide
  · calc
      ((setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState changed).storageMap2
          27 sender receiver = changed.storageMap2 27 sender receiver :=
            setFlowExists_runState_nonexists _ _ _ _ 27 (by decide)
      _ = base.storageMap2 27 sender receiver := hchange.2.2.2.2.2.2.2.2.1

private theorem deleteFlowObs_projection
    (base post : ContractState) (sender receiver : Address) (timestamp : Uint256)
    (hobs : DeleteFlowObs base post sender receiver timestamp) :
    pairCfaProjectionAt post sender receiver timestamp =
      pairCfaProjectionAt base sender receiver timestamp := by
  rcases hobs with ⟨changed, hchange, _, _, hpost, _⟩
  subst post
  simpa [pairCfaProjectionAt, cfaProjectionAt, setFlowExists_runState_storageMap] using hchange.1

private theorem deleteFlowObs_pairRate
    (base post : ContractState) (sender receiver : Address) (timestamp : Uint256)
    (hobs : DeleteFlowObs base post sender receiver timestamp) :
    pairNetFlowRate post sender receiver = pairNetFlowRate base sender receiver := by
  rcases hobs with ⟨changed, hchange, _, _, hpost, _⟩
  subst post
  simpa [pairNetFlowRate, setFlowExists_runState_storageMap] using hchange.2.1

private theorem deleteFlowObs_frame
    (base post : ContractState) (sender receiver unrelated : Address) (timestamp : Uint256)
    (hunrelatedSender : unrelated ≠ sender) (hunrelatedReceiver : unrelated ≠ receiver)
    (hobs : DeleteFlowObs base post sender receiver timestamp) :
    ∀ slotIndex, post.storageMap slotIndex unrelated = base.storageMap slotIndex unrelated := by
  rcases hobs with ⟨changed, hchange, _, _, hpost, _⟩
  intro slotIndex
  rw [hpost, setFlowExists_runState_storageMap]
  exact hchange.2.2.1 slotIndex unrelated hunrelatedSender hunrelatedReceiver

theorem deleteNonApp_preserves_cfa_projection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (timestamp : Uint256) :
    deleteNonAppPreservesCfaProjection source s sender receiver timestamp := by
  unfold deleteNonAppPreservesCfaProjection
  intro hsource
  dsimp [runDeleteNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  have hobs := deleteFlowNonAppBySender_observations s
    ((SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp).run s).snd
    sender receiver timestamp heq
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp)
    (deleteFlowNonAppBySender_storage_preserving sender receiver timestamp)
    (deleteFlowNonAppBySender_account_environment_preserving sender receiver timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  exact ⟨deleteFlowObs_sourcePost source s _ sender receiver timestamp hsource hobs hframe.1 hframe.2,
    deleteFlowObs_projection s _ sender receiver timestamp hobs⟩

theorem deleteNonApp_preserves_pair_net_flow_rate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (timestamp : Uint256) :
    deleteNonAppPreservesPairNetFlowRate source s sender receiver timestamp := by
  unfold deleteNonAppPreservesPairNetFlowRate
  intro hsource
  dsimp [runDeleteNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  have hobs := deleteFlowNonAppBySender_observations s
    ((SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp).run s).snd
    sender receiver timestamp heq
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp)
    (deleteFlowNonAppBySender_storage_preserving sender receiver timestamp)
    (deleteFlowNonAppBySender_account_environment_preserving sender receiver timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  exact ⟨deleteFlowObs_sourcePost source s _ sender receiver timestamp hsource hobs hframe.1 hframe.2,
    deleteFlowObs_pairRate s _ sender receiver timestamp hobs⟩

theorem deleteNonApp_frames_unrelated_account
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (timestamp : Uint256) :
    deleteNonAppFramesUnrelatedAccount source s sender receiver unrelated timestamp := by
  unfold deleteNonAppFramesUnrelatedAccount
  intro hsource hunrelatedSender hunrelatedReceiver
  dsimp [runDeleteNonApp]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  have heq := unit_success_eq hsuccess
  have hobs := deleteFlowNonAppBySender_observations s
    ((SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp).run s).snd
    sender receiver timestamp heq
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp)
    (deleteFlowNonAppBySender_storage_preserving sender receiver timestamp)
    (deleteFlowNonAppBySender_account_environment_preserving sender receiver timestamp) s
  rw [Contract.runState_eq_snd_run] at hframe
  refine ⟨deleteFlowObs_sourcePost source s _ sender receiver timestamp hsource hobs hframe.1 hframe.2,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact deleteFlowObs_frame s _ sender receiver unrelated timestamp
      hunrelatedSender hunrelatedReceiver hobs 0
  · exact deleteFlowObs_frame s _ sender receiver unrelated timestamp
      hunrelatedSender hunrelatedReceiver hobs 1
  · exact deleteFlowObs_frame s _ sender receiver unrelated timestamp
      hunrelatedSender hunrelatedReceiver hobs 2
  · exact deleteFlowObs_frame s _ sender receiver unrelated timestamp
      hunrelatedSender hunrelatedReceiver hobs 3
  · exact deleteFlowObs_frame s _ sender receiver unrelated timestamp
      hunrelatedSender hunrelatedReceiver hobs 4

private theorem setFlowExists_runState_other
    (s : ContractState) (sender receiver : Address) (existsWord : Uint256)
    (slotIndex : Nat) (hslot : slotIndex ≠ 9) :
    ((setMapping2 SuperfluidCFA.flowExists sender receiver existsWord).runState s).storageMap2
      slotIndex sender receiver = s.storageMap2 slotIndex sender receiver := by
  change (if slotIndex == SuperfluidCFA.flowExists.slot && sender == sender && receiver == receiver
    then existsWord else s.storageMap2 slotIndex sender receiver) = s.storageMap2 slotIndex sender receiver
  simp [hslot, SuperfluidCFA.flowExists]

private def CallbackObs
    (base post : ContractState) (sender receiver : Address) (timestamp result : Uint256) : Prop :=
  pairCfaProjectionAt post sender receiver timestamp =
    pairCfaProjectionAt base sender receiver timestamp ∧
  pairNetFlowRate post sender receiver = pairNetFlowRate base sender receiver ∧
  (∀ slotIndex query, query ≠ sender → query ≠ receiver →
    post.storageMap slotIndex query = base.storageMap slotIndex query) ∧
  post.storageMap2 6 sender receiver = 0 ∧
  post.storageMap2 7 sender receiver = 0 ∧
  post.storageMap2 8 sender receiver = 0 ∧
  post.storageMap2 9 sender receiver = 0 ∧
  result = 0 ∧
  post.storageMap2 5 sender receiver = 0 ∧
  post.storageMap2 27 sender receiver = base.storageMap2 27 sender receiver

private def receiverDeleteCallbackTail
    (sender receiver : Address) (newRate newDeposit timestamp : Uint256) : Contract Uint256 := do
  SuperfluidCFA._changeFlow sender receiver newRate newDeposit timestamp
  setMapping2 SuperfluidCFA.flowExists sender receiver 1
  SuperfluidCFA._requireCfaOnlyAvailableNonnegative sender timestamp
  SuperfluidCFA._requireExistingZeroOwedFlow sender receiver
  SuperfluidCFA._changeFlow sender receiver 0 0 timestamp
  setMapping2 SuperfluidCFA.flowExists sender receiver 0
  let reloadedFlowRate ← getMapping2 SuperfluidCFA.flowRates sender receiver
  let reloadedFlowOwed ← getMapping2 SuperfluidCFA.flowOwedDeposits sender receiver
  require (reloadedFlowOwed == 0) "CFA_RELOADED_OWED_DEPOSIT"
  SuperfluidCFA._updateAccountFlowState sender 0 0 0 timestamp
  SuperfluidCFA._updateAccountFlowState receiver 0 0 0 timestamp
  SuperfluidCFA._requireCfaOnlyAvailableNonnegative sender timestamp
  SuperfluidCFA._requireCfaOnlyAvailableNonnegative receiver timestamp
  return reloadedFlowRate

private theorem receiverDeleteCallbackTail_storage_preserving
    (sender receiver : Address) (newRate newDeposit timestamp : Uint256) :
    StoragePreserving (receiverDeleteCallbackTail sender receiver newRate newDeposit timestamp) := by
  unfold receiverDeleteCallbackTail
  apply storage_preserving_bind
  · exact changeFlow_storage_preserving _ _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping2 _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (availableNonnegative_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (existingZeroOwedFlow_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact changeFlow_storage_preserving _ _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_setMapping2 _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping2 _ _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping2 _ _ _
  intro reloadedOwed
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact updateAccountFlowState_storage_preserving _ _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact updateAccountFlowState_storage_preserving _ _ _ _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (availableNonnegative_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (availableNonnegative_preserving _ _)
  intro _
  exact storage_preserving_pure _

private theorem receiverDeleteCallbackTail_account_environment_preserving
    (sender receiver : Address) (newRate newDeposit timestamp : Uint256) :
    AccountEnvironmentPreserving
      (receiverDeleteCallbackTail sender receiver newRate newDeposit timestamp) := by
  unfold receiverDeleteCallbackTail
  apply account_environment_preserving_bind
  · exact changeFlow_account_environment_preserving _ _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping2 _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (availableNonnegative_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (existingZeroOwedFlow_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact changeFlow_account_environment_preserving _ _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_setMapping2 _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping2 _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping2 _ _ _
  intro reloadedOwed
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact updateAccountFlowState_account_environment_preserving _ _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact updateAccountFlowState_account_environment_preserving _ _ _ _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (availableNonnegative_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (availableNonnegative_preserving _ _)
  intro _
  exact account_environment_preserving_pure _

private theorem receiverDeleteCallback_observations
    (s t : ContractState) (sender receiver : Address)
    (newRate liquidationPeriod minimumDeposit timestamp result : Uint256)
    (h : (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver newRate
      liquidationPeriod minimumDeposit timestamp).run s = ContractResult.success result t) :
    CallbackObs s t sender receiver timestamp result := by
  unfold SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback runOneLevelOuterNested
    behavioralOneLevelCallback SuperfluidCFA._receiverDeleteCallbackOuterPrefix
    SuperfluidCFA._receiverDeleteCallbackNestedDelete
    SuperfluidCFA._receiverDeleteCallbackOuterResume at h
  simp only [Bind.bind, Contract.bind_assoc] at h
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, distinctState, hdistinctReq, h⟩
  have hdistinctState : distinctState = s := by
    rw [success_state_eq _ _ _ _ hdistinctReq]
    exact preserving_require _ _ s
  have hdistinctCond : (sender != receiver) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (sender != receiver) "CFA_NO_SELF_FLOW" s (by rw [hdistinctReq]; rfl)
  have hdistinct : sender ≠ receiver := by
    intro heq
    subst receiver
    simp at hdistinctCond
  subst distinctState
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _
    (sourceEnvironment_preserving sender receiver liquidationPeriod minimumDeposit) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (directOuterHostContext_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (emptyFlow_preserving sender receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _
    (sourceAppCreditBase_preserving newRate liquidationPeriod) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨newDeposit, depositState, hdeposit, h⟩
  have hdepositState : depositState = s := by
    rw [success_state_eq _ _ _ _ hdeposit]
    exact sourceDeposit_preserving newRate liquidationPeriod minimumDeposit s
  subst depositState
  have callbackTail
      (h : (receiverDeleteCallbackTail sender receiver newRate newDeposit timestamp).run s =
        ContractResult.success result t) :
      CallbackObs s t sender receiver timestamp result := by
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, created, houter, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, afterCreate, hcreateExists, h⟩
    have hafterCreate : afterCreate =
        (setMapping2 SuperfluidCFA.flowExists sender receiver 1).runState created :=
      success_state_eq _ _ _ _ hcreateExists
    rcases preserving_bind_tail _ _ _ _ _ (availableNonnegative_preserving sender timestamp) h with ⟨_, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, innerBase, hexisting, h⟩
    have hexistingObs := existingZeroOwedFlow_success_exists afterCreate innerBase sender receiver hexisting
    have hinnerBase : innerBase = afterCreate := hexistingObs.2.2.2.2
    subst innerBase
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, deleted, hdelete, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, afterDelete, hdeleteExists, h⟩
    have hafterDelete : afterDelete =
        (setMapping2 SuperfluidCFA.flowExists sender receiver 0).runState deleted :=
      success_state_eq _ _ _ _ hdeleteExists
    rcases bind_success_elim _ _ _ _ _ h with ⟨reloadedRate, rateState, hreload, h⟩
    have hrateState : rateState = afterDelete := success_state_eq _ _ _ _ hreload
    have hreloadValue : reloadedRate = afterDelete.storageMap2 6 sender receiver :=
      getMapping2_value_of_success SuperfluidCFA.flowRates sender receiver _ _ _ hreload
    subst rateState
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, owedState, hgetOwed, h⟩
    have howedState : owedState = afterDelete := success_state_eq _ _ _ _ hgetOwed
    subst owedState
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, senderReconciled, hsender, h⟩
    rcases bind_success_elim _ _ _ _ _ h with ⟨_, receiverReconciled, hreceiver, h⟩
    rcases preserving_bind_tail _ _ _ _ _ (availableNonnegative_preserving sender timestamp) h with ⟨_, h⟩
    rcases preserving_bind_tail _ _ _ _ _ (availableNonnegative_preserving receiver timestamp) h with ⟨_, h⟩
    have hraw := Contract.eq_of_run_success h
    change ContractResult.success reloadedRate receiverReconciled = ContractResult.success result t at hraw
    injection hraw with hresult hstate
    have ht : t = receiverReconciled := hstate.symm
    have houterObs := changeFlow_observations s created sender receiver newRate newDeposit timestamp
      hdistinct houter
    have hinnerObs := changeFlow_observations afterCreate deleted sender receiver 0 0 timestamp
      hdistinct hdelete
    have hsenderObs := updateAccountFlowState_observations afterDelete senderReconciled sender 0 0 0
      timestamp hsender
    have hreceiverObs := updateAccountFlowState_observations senderReconciled receiverReconciled receiver
      0 0 0 timestamp hreceiver
    have hsenderMap2 : senderReconciled.storageMap2 = afterDelete.storageMap2 := by
      rw [success_state_eq _ _ _ _ hsender]
      exact updateAccountFlowState_map2_preserving _ _ _ _ _ _
    have hreceiverMap2 : receiverReconciled.storageMap2 = senderReconciled.storageMap2 := by
      rw [success_state_eq _ _ _ _ hreceiver]
      exact updateAccountFlowState_map2_preserving _ _ _ _ _ _
    have hafterCreateStorage : afterCreate.storageMap = created.storageMap := by
      rw [hafterCreate]
      exact setFlowExists_runState_storageMap created sender receiver 1
    have hafterDeleteStorage : afterDelete.storageMap = deleted.storageMap := by
      rw [hafterDelete]
      exact setFlowExists_runState_storageMap deleted sender receiver 0
    have hprojection : pairCfaProjectionAt t sender receiver timestamp =
        pairCfaProjectionAt s sender receiver timestamp := by
      unfold pairCfaProjectionAt
      calc
        add (cfaProjectionAt t sender timestamp) (cfaProjectionAt t receiver timestamp) =
            add (cfaProjectionAt senderReconciled sender timestamp)
              (cfaProjectionAt senderReconciled receiver timestamp) := by
                rw [ht, hreceiverObs.1]
                simp [cfaProjectionAt,
                  hreceiverObs.2.2 0 sender hdistinct,
                  hreceiverObs.2.2 1 sender hdistinct,
                  hreceiverObs.2.2 2 sender hdistinct]
        _ = add (cfaProjectionAt afterDelete sender timestamp)
              (cfaProjectionAt afterDelete receiver timestamp) := by
                rw [hsenderObs.1]
                simp [cfaProjectionAt,
                  hsenderObs.2.2 0 receiver (Ne.symm hdistinct),
                  hsenderObs.2.2 1 receiver (Ne.symm hdistinct),
                  hsenderObs.2.2 2 receiver (Ne.symm hdistinct)]
        _ = add (cfaProjectionAt deleted sender timestamp)
              (cfaProjectionAt deleted receiver timestamp) := by
                simpa [cfaProjectionAt, hafterDeleteStorage]
        _ = add (cfaProjectionAt afterCreate sender timestamp)
              (cfaProjectionAt afterCreate receiver timestamp) := hinnerObs.1
        _ = add (cfaProjectionAt created sender timestamp)
              (cfaProjectionAt created receiver timestamp) := by
                simpa [cfaProjectionAt, hafterCreateStorage]
        _ = add (cfaProjectionAt s sender timestamp) (cfaProjectionAt s receiver timestamp) := houterObs.1
    have hpairRate : pairNetFlowRate t sender receiver = pairNetFlowRate s sender receiver := by
      unfold pairNetFlowRate
      have hsenderRate : senderReconciled.storageMap 1 sender = afterDelete.storageMap 1 sender := by
        calc
          senderReconciled.storageMap 1 sender = add (afterDelete.storageMap 1 sender) 0 :=
            hsenderObs.2.1
          _ = afterDelete.storageMap 1 sender := Verity.Core.Uint256.add_zero _
      have hreceiverRate : receiverReconciled.storageMap 1 receiver =
          senderReconciled.storageMap 1 receiver := by
        calc
          receiverReconciled.storageMap 1 receiver = add (senderReconciled.storageMap 1 receiver) 0 :=
            hreceiverObs.2.1
          _ = senderReconciled.storageMap 1 receiver := Verity.Core.Uint256.add_zero _
      calc
        add (t.storageMap 1 sender) (t.storageMap 1 receiver) =
            add (senderReconciled.storageMap 1 sender) (senderReconciled.storageMap 1 receiver) := by
              rw [ht, hreceiverObs.2.2 1 sender hdistinct, hreceiverRate]
        _ = add (afterDelete.storageMap 1 sender) (afterDelete.storageMap 1 receiver) := by
              rw [hsenderObs.2.2 1 receiver (Ne.symm hdistinct), hsenderRate]
        _ = add (deleted.storageMap 1 sender) (deleted.storageMap 1 receiver) := by
              simpa [hafterDeleteStorage]
        _ = add (afterCreate.storageMap 1 sender) (afterCreate.storageMap 1 receiver) := hinnerObs.2.1
        _ = add (created.storageMap 1 sender) (created.storageMap 1 receiver) := by
              simpa [hafterCreateStorage]
        _ = add (s.storageMap 1 sender) (s.storageMap 1 receiver) := houterObs.2.1
    have hframe : ∀ slotIndex query, query ≠ sender → query ≠ receiver →
        t.storageMap slotIndex query = s.storageMap slotIndex query := by
      intro slotIndex query hquerySender hqueryReceiver
      calc
        t.storageMap slotIndex query = receiverReconciled.storageMap slotIndex query := by rw [ht]
        _ = senderReconciled.storageMap slotIndex query :=
          hreceiverObs.2.2 slotIndex query hqueryReceiver
        _ = afterDelete.storageMap slotIndex query :=
          hsenderObs.2.2 slotIndex query hquerySender
        _ = deleted.storageMap slotIndex query := by rw [hafterDeleteStorage]
        _ = afterCreate.storageMap slotIndex query :=
          hinnerObs.2.2.1 slotIndex query hquerySender hqueryReceiver
        _ = created.storageMap slotIndex query := by rw [hafterCreateStorage]
        _ = s.storageMap slotIndex query :=
          houterObs.2.2.1 slotIndex query hquerySender hqueryReceiver
    have hfinalRate : t.storageMap2 6 sender receiver = 0 := by
      calc
        t.storageMap2 6 sender receiver = receiverReconciled.storageMap2 6 sender receiver := by rw [ht]
        _ = afterDelete.storageMap2 6 sender receiver := by rw [hreceiverMap2, hsenderMap2]
        _ = deleted.storageMap2 6 sender receiver := by rw [hafterDelete, setFlowExists_runState_rate]
        _ = 0 := hinnerObs.2.2.2.2.1
    have hfinalTimestamp : t.storageMap2 5 sender receiver = 0 := by
      calc
        t.storageMap2 5 sender receiver = receiverReconciled.storageMap2 5 sender receiver := by rw [ht]
        _ = afterDelete.storageMap2 5 sender receiver := by rw [hreceiverMap2, hsenderMap2]
        _ = deleted.storageMap2 5 sender receiver := by
          rw [hafterDelete, setFlowExists_runState_other _ _ _ _ 5 (by decide)]
        _ = (if (0 != 0 && 0 <= 39614081257132168796771975167) = true then timestamp else 0) :=
          hinnerObs.2.2.2.1
        _ = 0 := by simp
    have hfinalDeposit : t.storageMap2 7 sender receiver = 0 := by
      calc
        t.storageMap2 7 sender receiver = receiverReconciled.storageMap2 7 sender receiver := by rw [ht]
        _ = afterDelete.storageMap2 7 sender receiver := by rw [hreceiverMap2, hsenderMap2]
        _ = deleted.storageMap2 7 sender receiver := by
          rw [hafterDelete, setFlowExists_runState_other _ _ _ _ 7 (by decide)]
        _ = 0 := by
          rw [hinnerObs.2.2.2.2.2.1]
          decide
    have hfinalOwed : t.storageMap2 8 sender receiver = 0 := by
      calc
        t.storageMap2 8 sender receiver = receiverReconciled.storageMap2 8 sender receiver := by rw [ht]
        _ = afterDelete.storageMap2 8 sender receiver := by rw [hreceiverMap2, hsenderMap2]
        _ = deleted.storageMap2 8 sender receiver := by
          rw [hafterDelete, setFlowExists_runState_other _ _ _ _ 8 (by decide)]
        _ = afterCreate.storageMap2 8 sender receiver := hinnerObs.2.2.2.2.2.2.1
        _ = 0 := hexistingObs.2.2.2.1
    have hfinalExists : t.storageMap2 9 sender receiver = 0 := by
      calc
        t.storageMap2 9 sender receiver = receiverReconciled.storageMap2 9 sender receiver := by rw [ht]
        _ = afterDelete.storageMap2 9 sender receiver := by rw [hreceiverMap2, hsenderMap2]
        _ = 0 := by rw [hafterDelete, setFlowExists_runState_exists]
    have hfinalKey : t.storageMap2 27 sender receiver = s.storageMap2 27 sender receiver := by
      calc
        t.storageMap2 27 sender receiver = receiverReconciled.storageMap2 27 sender receiver := by rw [ht]
        _ = afterDelete.storageMap2 27 sender receiver := by rw [hreceiverMap2, hsenderMap2]
        _ = deleted.storageMap2 27 sender receiver := by
          rw [hafterDelete, setFlowExists_runState_other _ _ _ _ 27 (by decide)]
        _ = afterCreate.storageMap2 27 sender receiver := hinnerObs.2.2.2.2.2.2.2.2.1
        _ = created.storageMap2 27 sender receiver := by
          rw [hafterCreate, setFlowExists_runState_other _ _ _ _ 27 (by decide)]
        _ = s.storageMap2 27 sender receiver := houterObs.2.2.2.2.2.2.2.2.1
    have hresultZero : result = 0 := by
      calc
        result = reloadedRate := hresult.symm
        _ = afterDelete.storageMap2 6 sender receiver := hreloadValue
        _ = deleted.storageMap2 6 sender receiver := by rw [hafterDelete, setFlowExists_runState_rate]
        _ = 0 := hinnerObs.2.2.2.2.1
    exact ⟨hprojection, hpairRate, hframe, hfinalRate, hfinalDeposit, hfinalOwed,
      hfinalExists, hresultZero, hfinalTimestamp, hfinalKey⟩
  split at h
  · simp only [Contract.bind_assoc, if_true] at h
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    change (receiverDeleteCallbackTail sender receiver newRate newDeposit timestamp).run s =
      ContractResult.success result t at h
    exact callbackTail h
  · simp only [Contract.bind_assoc, if_true] at h
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
    change (receiverDeleteCallbackTail sender receiver newRate newDeposit timestamp).run s =
      ContractResult.success result t at h
    exact callbackTail h

private theorem callbackObs_sourcePost
    (source : PinnedSourceState) (base post : ContractState) (sender receiver : Address)
    (timestamp result : Uint256)
    (hsource : pinnedSourcePathRelation source base sender receiver timestamp)
    (hobs : CallbackObs base post sender receiver timestamp result)
    (hstorage : post.storage = base.storage)
    (hmaps : ∀ slotIndex account, 4 < slotIndex →
      post.storageMap slotIndex account = base.storageMap slotIndex account) :
    sourcePostRelation source post sender receiver := by
  refine sourcePost_of_model_frame source base post sender receiver hsource.1 ?_
    hobs.2.2.2.2.2.2.2.2.2 (by simpa using hstorage) hmaps
  · rw [hobs.2.2.2.2.2.2.2.2.1, hobs.2.2.2.1, hobs.2.2.2.2.1,
      hobs.2.2.2.2.2.1, hobs.2.2.2.2.2.2.1]
    decide

private theorem receiverDeleteCallback_storage_preserving
    (sender receiver : Address) (newRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    StoragePreserving (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver newRate
      liquidationPeriod minimumDeposit timestamp) := by
  unfold SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback runOneLevelOuterNested
    behavioralOneLevelCallback SuperfluidCFA._receiverDeleteCallbackOuterPrefix
    SuperfluidCFA._receiverDeleteCallbackNestedDelete
    SuperfluidCFA._receiverDeleteCallbackOuterResume
  simp only [Bind.bind, Contract.bind_assoc]
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (directOuterHostContext_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (emptyFlow_preserving _ _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (canonical_preserving _)
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_getMapping _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact storage_preserving_require _ _
  intro _
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceAppCreditBase_preserving _ _)
  intro appCreditBase
  apply storage_preserving_bind
  · exact state_preserving_storage (sourceDeposit_preserving _ _ _)
  intro newDeposit
  dsimp
  split
  · simp only [Contract.bind_assoc]
    apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    simpa [receiverDeleteCallbackTail] using
      receiverDeleteCallbackTail_storage_preserving sender receiver newRate newDeposit timestamp

  · simp only [Contract.bind_assoc]
    apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    apply storage_preserving_bind
    · exact storage_preserving_require _ _
    intro _
    simpa [receiverDeleteCallbackTail] using
      receiverDeleteCallbackTail_storage_preserving sender receiver newRate newDeposit timestamp

private theorem receiverDeleteCallback_account_environment_preserving
    (sender receiver : Address) (newRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    AccountEnvironmentPreserving
      (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver newRate
        liquidationPeriod minimumDeposit timestamp) := by
  unfold SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback runOneLevelOuterNested
    behavioralOneLevelCallback SuperfluidCFA._receiverDeleteCallbackOuterPrefix
    SuperfluidCFA._receiverDeleteCallbackNestedDelete
    SuperfluidCFA._receiverDeleteCallbackOuterResume
  simp only [Bind.bind, Contract.bind_assoc]
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceEnvironment_preserving _ _ _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (directOuterHostContext_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (emptyFlow_preserving _ _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (canonical_preserving _)
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_getMapping _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact account_environment_preserving_require _ _
  intro _
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceAppCreditBase_preserving _ _)
  intro appCreditBase
  apply account_environment_preserving_bind
  · exact state_preserving_account_environment (sourceDeposit_preserving _ _ _)
  intro newDeposit
  dsimp
  split
  · simp only [Contract.bind_assoc]
    apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    simpa [receiverDeleteCallbackTail] using
      receiverDeleteCallbackTail_account_environment_preserving sender receiver newRate newDeposit timestamp
  · simp only [Contract.bind_assoc]
    apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    apply account_environment_preserving_bind
    · exact account_environment_preserving_require _ _
    intro _
    simpa [receiverDeleteCallbackTail] using
      receiverDeleteCallbackTail_account_environment_preserving sender receiver newRate newDeposit timestamp

theorem receiverDeleteCallback_reloads_final_zero
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    receiverDeleteCallbackReloadsFinalZero source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold receiverDeleteCallbackReloadsFinalZero
  intro hsource
  dsimp [runReceiverDeleteCallback]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  rcases success_exists
    ((SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate
      liquidationPeriod minimumDeposit timestamp).run s) hsuccess with ⟨result, post, hrun⟩
  have hobs := receiverDeleteCallback_observations s post sender receiver flowRate liquidationPeriod
    minimumDeposit timestamp result hrun
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp)
    (receiverDeleteCallback_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (receiverDeleteCallback_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run, hrun] at hframe
  rw [hrun]
  refine ⟨callbackObs_sourcePost source s post sender receiver timestamp result hsource hobs hframe.1 hframe.2, ?_,
    hobs.2.2.2.1, hobs.2.2.2.2.2.2.1⟩
  simpa [ContractResult.getValue?] using hobs.2.2.2.2.2.2.2.1

theorem receiverDeleteCallback_preserves_cfa_projection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    receiverDeleteCallbackPreservesCfaProjection source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold receiverDeleteCallbackPreservesCfaProjection
  intro hsource
  dsimp [runReceiverDeleteCallback]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  rcases success_exists
    ((SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate
      liquidationPeriod minimumDeposit timestamp).run s) hsuccess with ⟨result, post, hrun⟩
  have hobs := receiverDeleteCallback_observations s post sender receiver flowRate liquidationPeriod
    minimumDeposit timestamp result hrun
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp)
    (receiverDeleteCallback_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (receiverDeleteCallback_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run, hrun] at hframe
  rw [hrun]
  exact ⟨callbackObs_sourcePost source s post sender receiver timestamp result hsource hobs hframe.1 hframe.2, hobs.1⟩

theorem receiverDeleteCallback_preserves_pair_net_flow_rate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    receiverDeleteCallbackPreservesPairNetFlowRate source s sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold receiverDeleteCallbackPreservesPairNetFlowRate
  intro hsource
  dsimp [runReceiverDeleteCallback]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  rcases success_exists
    ((SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate
      liquidationPeriod minimumDeposit timestamp).run s) hsuccess with ⟨result, post, hrun⟩
  have hobs := receiverDeleteCallback_observations s post sender receiver flowRate liquidationPeriod
    minimumDeposit timestamp result hrun
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp)
    (receiverDeleteCallback_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (receiverDeleteCallback_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run, hrun] at hframe
  rw [hrun]
  exact ⟨callbackObs_sourcePost source s post sender receiver timestamp result hsource hobs hframe.1 hframe.2, hobs.2.1⟩

theorem receiverDeleteCallback_frames_unrelated_account
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    receiverDeleteCallbackFramesUnrelatedAccount source s sender receiver unrelated flowRate liquidationPeriod
      minimumDeposit timestamp := by
  unfold receiverDeleteCallbackFramesUnrelatedAccount
  intro hsource hunrelatedSender hunrelatedReceiver
  dsimp [runReceiverDeleteCallback]
  intro hsuccess
  unfold modelSucceeded at hsuccess
  rcases success_exists
    ((SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate
      liquidationPeriod minimumDeposit timestamp).run s) hsuccess with ⟨result, post, hrun⟩
  have hobs := receiverDeleteCallback_observations s post sender receiver flowRate liquidationPeriod
    minimumDeposit timestamp result hrun
  have hframe := endpoint_environment_frame_of_preserving
    (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate liquidationPeriod
      minimumDeposit timestamp)
    (receiverDeleteCallback_storage_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp)
    (receiverDeleteCallback_account_environment_preserving sender receiver flowRate liquidationPeriod minimumDeposit timestamp) s
  rw [Contract.runState_eq_snd_run, hrun] at hframe
  rw [hrun]
  refine ⟨callbackObs_sourcePost source s post sender receiver timestamp result hsource hobs hframe.1 hframe.2,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hobs.2.2.1 0 unrelated hunrelatedSender hunrelatedReceiver
  · exact hobs.2.2.1 1 unrelated hunrelatedSender hunrelatedReceiver
  · exact hobs.2.2.1 2 unrelated hunrelatedSender hunrelatedReceiver
  · exact hobs.2.2.1 3 unrelated hunrelatedSender hunrelatedReceiver
  · exact hobs.2.2.1 4 unrelated hunrelatedSender hunrelatedReceiver

/-! Phase 3 finite-universe, future-time, and callback-composition proofs. -/

private theorem uint256_sub_triangle
    (earlier middle later : Uint256) :
    later - earlier = (middle - earlier) + (later - middle) := by
  apply Verity.Core.Uint256.add_right_cancel (c := earlier)
  rw [Verity.Core.Uint256.sub_add_cancel_left]
  symm
  calc
    ((middle - earlier) + (later - middle)) + earlier =
        ((middle - earlier) + earlier) + (later - middle) := by
          simp only [Verity.Core.Uint256.add_assoc, Verity.Core.Uint256.add_comm]
    _ = middle + (later - middle) := by
          rw [Verity.Core.Uint256.sub_add_cancel_left]
    _ = (later - middle) + middle := by
          rw [Verity.Core.Uint256.add_comm]
    _ = later := Verity.Core.Uint256.sub_add_cancel_left later middle

private theorem cfaProjectionAt_shift
    (state : ContractState) (account : Address) (fromTimestamp toTimestamp : Uint256) :
    cfaProjectionAt state account toTimestamp =
      cfaProjectionAt state account fromTimestamp +
        (toTimestamp - fromTimestamp) * state.storageMap 1 account := by
  unfold cfaProjectionAt
  change state.storageMap 0 account +
      ((toTimestamp - state.storageMap 2 account) * state.storageMap 1 account) =
    (state.storageMap 0 account +
      ((fromTimestamp - state.storageMap 2 account) * state.storageMap 1 account)) +
      (toTimestamp - fromTimestamp) * state.storageMap 1 account
  rw [uint256_sub_triangle (state.storageMap 2 account) fromTimestamp toTimestamp]
  rw [Verity.Core.Uint256.add_mul]
  simp only [Verity.Core.Uint256.add_assoc]

private theorem pairCfaProjectionAt_shift
    (state : ContractState) (sender receiver : Address)
    (fromTimestamp toTimestamp : Uint256) :
    pairCfaProjectionAt state sender receiver toTimestamp =
      pairCfaProjectionAt state sender receiver fromTimestamp +
        (toTimestamp - fromTimestamp) * pairNetFlowRate state sender receiver := by
  unfold pairCfaProjectionAt pairNetFlowRate
  rw [cfaProjectionAt_shift state sender fromTimestamp toTimestamp,
    cfaProjectionAt_shift state receiver fromTimestamp toTimestamp]
  have hfactor :
      (toTimestamp - fromTimestamp) * state.storageMap 1 sender +
          (toTimestamp - fromTimestamp) * state.storageMap 1 receiver =
        (toTimestamp - fromTimestamp) *
          (state.storageMap 1 sender + state.storageMap 1 receiver) := by
    calc
      (toTimestamp - fromTimestamp) * state.storageMap 1 sender +
          (toTimestamp - fromTimestamp) * state.storageMap 1 receiver =
        state.storageMap 1 sender * (toTimestamp - fromTimestamp) +
          state.storageMap 1 receiver * (toTimestamp - fromTimestamp) := by
            simp only [Verity.Core.Uint256.mul_comm]
      _ = (state.storageMap 1 sender + state.storageMap 1 receiver) *
          (toTimestamp - fromTimestamp) := by
            rw [Verity.Core.Uint256.add_mul]
      _ = (toTimestamp - fromTimestamp) *
          (state.storageMap 1 sender + state.storageMap 1 receiver) := by
            rw [Verity.Core.Uint256.mul_comm]
  calc
    (cfaProjectionAt state sender fromTimestamp +
          (toTimestamp - fromTimestamp) * state.storageMap 1 sender) +
        (cfaProjectionAt state receiver fromTimestamp +
          (toTimestamp - fromTimestamp) * state.storageMap 1 receiver) =
      (cfaProjectionAt state sender fromTimestamp +
          cfaProjectionAt state receiver fromTimestamp) +
        ((toTimestamp - fromTimestamp) * state.storageMap 1 sender +
          (toTimestamp - fromTimestamp) * state.storageMap 1 receiver) := by
            calc
              (cfaProjectionAt state sender fromTimestamp +
                    (toTimestamp - fromTimestamp) * state.storageMap 1 sender) +
                  (cfaProjectionAt state receiver fromTimestamp +
                    (toTimestamp - fromTimestamp) * state.storageMap 1 receiver) =
                cfaProjectionAt state sender fromTimestamp +
                  ((toTimestamp - fromTimestamp) * state.storageMap 1 sender +
                    (cfaProjectionAt state receiver fromTimestamp +
                      (toTimestamp - fromTimestamp) * state.storageMap 1 receiver)) := by
                        rw [Verity.Core.Uint256.add_assoc]
              _ = cfaProjectionAt state sender fromTimestamp +
                  (((toTimestamp - fromTimestamp) * state.storageMap 1 sender +
                    cfaProjectionAt state receiver fromTimestamp) +
                      (toTimestamp - fromTimestamp) * state.storageMap 1 receiver) := by
                        rw [Verity.Core.Uint256.add_assoc]
              _ = cfaProjectionAt state sender fromTimestamp +
                  ((cfaProjectionAt state receiver fromTimestamp +
                    (toTimestamp - fromTimestamp) * state.storageMap 1 sender) +
                      (toTimestamp - fromTimestamp) * state.storageMap 1 receiver) := by
                        rw [Verity.Core.Uint256.add_comm
                          ((toTimestamp - fromTimestamp) * state.storageMap 1 sender)
                          (cfaProjectionAt state receiver fromTimestamp)]
              _ = cfaProjectionAt state sender fromTimestamp +
                  (cfaProjectionAt state receiver fromTimestamp +
                    ((toTimestamp - fromTimestamp) * state.storageMap 1 sender +
                      (toTimestamp - fromTimestamp) * state.storageMap 1 receiver)) := by
                        rw [Verity.Core.Uint256.add_assoc]
              _ = (cfaProjectionAt state sender fromTimestamp +
                    cfaProjectionAt state receiver fromTimestamp) +
                  ((toTimestamp - fromTimestamp) * state.storageMap 1 sender +
                    (toTimestamp - fromTimestamp) * state.storageMap 1 receiver) := by
                        rw [Verity.Core.Uint256.add_assoc]
    _ = (cfaProjectionAt state sender fromTimestamp +
          cfaProjectionAt state receiver fromTimestamp) +
        (toTimestamp - fromTimestamp) *
          (state.storageMap 1 sender + state.storageMap 1 receiver) := by rw [hfactor]

private theorem pairCfaProjectionAt_future_of_operation_and_rate
    (pre post : ContractState) (sender receiver : Address)
    (operationTimestamp tau : Uint256)
    (hprojection : pairCfaProjectionAt post sender receiver operationTimestamp =
      pairCfaProjectionAt pre sender receiver operationTimestamp)
    (hrate : pairNetFlowRate post sender receiver = pairNetFlowRate pre sender receiver) :
    pairCfaProjectionAt post sender receiver tau =
      pairCfaProjectionAt pre sender receiver tau := by
  rw [pairCfaProjectionAt_shift post sender receiver operationTimestamp tau,
    pairCfaProjectionAt_shift pre sender receiver operationTimestamp tau,
    hprojection, hrate]

private theorem uint256_map_sum_eq_of_perm
    {α : Type} (f : α → Uint256) {left right : List α}
    (hperm : left.Perm right) :
    (left.map f).sum = (right.map f).sum := by
  induction hperm with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap first second rest =>
      simp only [List.map, List.sum_cons]
      calc
        f second + (f first + (rest.map f).sum) =
            (f second + f first) + (rest.map f).sum := by
              rw [Verity.Core.Uint256.add_assoc]
        _ = (f first + f second) + (rest.map f).sum := by
              rw [Verity.Core.Uint256.add_comm (f second) (f first)]
        _ = f first + (f second + (rest.map f).sum) := by
              rw [Verity.Core.Uint256.add_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem framed_map_sum
    (pre post : ContractState) (accounts : List Address)
    (sender receiver : Address) (timestamp : Uint256)
    (hframe : ∀ account, account ∈ accounts → account ≠ sender → account ≠ receiver →
      cfaProjectionAt post account timestamp = cfaProjectionAt pre account timestamp) :
    ∀ rest : List Address, sender ∉ rest → receiver ∉ rest →
      (∀ account, account ∈ rest → account ∈ accounts) →
      (rest.map (fun account => cfaProjectionAt post account timestamp)).sum =
        (rest.map (fun account => cfaProjectionAt pre account timestamp)).sum := by
  intro rest hsenderRest hreceiverRest hsubset
  induction rest with
  | nil => rfl
  | cons account tail ih =>
      have hmember : account ∈ accounts := hsubset account (by simp)
      have hsender : account ≠ sender := by
        intro heq
        apply hsenderRest
        simp [heq]
      have hreceiver : account ≠ receiver := by
        intro heq
        apply hreceiverRest
        simp [heq]
      have hsenderTail : sender ∉ tail := by
        intro hmember
        exact hsenderRest (by simp [hmember])
      have hreceiverTail : receiver ∉ tail := by
        intro hmember
        exact hreceiverRest (by simp [hmember])
      have htail : ∀ query, query ∈ tail → query ∈ accounts := by
        intro query hquery
        exact hsubset query (by simp [hquery])
      simp only [List.map, List.sum_cons]
      rw [hframe account hmember hsender hreceiver,
        ih hsenderTail hreceiverTail htail]

theorem pairAndFrame_implies_modular_cfa_global_projection
    (pre post : ContractState) (accounts : List Address) (sender receiver : Address)
    (timestamp : Uint256) :
    pairAndFrameImplyModularCfaGlobalProjection pre post accounts sender receiver timestamp := by
  unfold pairAndFrameImplyModularCfaGlobalProjection CfaPairCoveredBy
  rintro ⟨hnodup, hdistinct, hsenderMem, hreceiverMem⟩ hpair hframe
  let withoutSender := accounts.erase sender
  let rest := withoutSender.erase receiver
  have hreceiverWithout : receiver ∈ withoutSender := by
    simp [withoutSender, hreceiverMem, Ne.symm hdistinct]
  have haccountsPerm : accounts.Perm (sender :: receiver :: rest) := by
    exact (List.perm_cons_erase hsenderMem).trans
      (List.Perm.cons sender (List.perm_cons_erase hreceiverWithout))
  have hrestSubset : ∀ account, account ∈ rest → account ∈ accounts := by
    intro account haccount
    exact List.mem_of_mem_erase (List.mem_of_mem_erase haccount)
  have hrestSender : sender ∉ rest := by
    intro hmember
    have hwithout : sender ∈ withoutSender := List.mem_of_mem_erase hmember
    exact (List.Nodup.not_mem_erase hnodup) hwithout
  have hrestReceiver : receiver ∉ rest := by
    exact (hnodup.erase sender).not_mem_erase
  have hrestSum := framed_map_sum pre post accounts sender receiver timestamp hframe rest
    hrestSender hrestReceiver hrestSubset
  unfold modularCfaGlobalProjectionSumAt
  rw [uint256_map_sum_eq_of_perm (fun account => cfaProjectionAt post account timestamp)
      haccountsPerm,
    uint256_map_sum_eq_of_perm (fun account => cfaProjectionAt pre account timestamp)
      haccountsPerm]
  simp only [List.map, List.sum_cons]
  have hpair' :
      cfaProjectionAt post sender timestamp + cfaProjectionAt post receiver timestamp =
        cfaProjectionAt pre sender timestamp + cfaProjectionAt pre receiver timestamp := by
    simpa [pairCfaProjectionAt] using hpair
  calc
    cfaProjectionAt post sender timestamp +
        (cfaProjectionAt post receiver timestamp +
          (rest.map (fun account => cfaProjectionAt post account timestamp)).sum) =
      (cfaProjectionAt post sender timestamp + cfaProjectionAt post receiver timestamp) +
        (rest.map (fun account => cfaProjectionAt post account timestamp)).sum := by
          rw [Verity.Core.Uint256.add_assoc]
    _ = (cfaProjectionAt pre sender timestamp + cfaProjectionAt pre receiver timestamp) +
        (rest.map (fun account => cfaProjectionAt post account timestamp)).sum := by rw [hpair']
    _ = (cfaProjectionAt pre sender timestamp + cfaProjectionAt pre receiver timestamp) +
        (rest.map (fun account => cfaProjectionAt pre account timestamp)).sum := by rw [hrestSum]
    _ = cfaProjectionAt pre sender timestamp +
        (cfaProjectionAt pre receiver timestamp +
          (rest.map (fun account => cfaProjectionAt pre account timestamp)).sum) := by
            rw [Verity.Core.Uint256.add_assoc]

theorem createNonApp_preserves_future_modular_cfa_global_projection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) :
    createNonAppPreservesFutureModularCfaGlobalProjection source s accounts sender receiver
      flowRate liquidationPeriod minimumDeposit operationTimestamp tau := by
  unfold createNonAppPreservesFutureModularCfaGlobalProjection
  intro hcovered _htimestamp _htau hsource
  dsimp only
  intro hsuccess
  have hprojection := createNonApp_preserves_cfa_projection source s sender receiver flowRate
    liquidationPeriod minimumDeposit operationTimestamp
  unfold createNonAppPreservesCfaProjection at hprojection
  have hprojection := hprojection hsource hsuccess
  have hrate := createNonApp_preserves_pair_net_flow_rate source s sender receiver flowRate
    liquidationPeriod minimumDeposit operationTimestamp
  unfold createNonAppPreservesPairNetFlowRate at hrate
  have hrate := hrate hsource hsuccess
  refine ⟨hprojection.1, ?_⟩
  apply pairAndFrame_implies_modular_cfa_global_projection
  · exact hcovered
  · exact pairCfaProjectionAt_future_of_operation_and_rate s
      (runCreateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit
        operationTimestamp).snd sender receiver operationTimestamp tau hprojection.2 hrate.2
  · intro account hmember hsender hreceiver
    have hframe := createNonApp_frames_unrelated_account source s sender receiver account flowRate
      liquidationPeriod minimumDeposit operationTimestamp
    unfold createNonAppFramesUnrelatedAccount at hframe
    rcases hframe hsource hsender hreceiver hsuccess with
      ⟨_, hsettled, hnetRate, haccountTimestamp, _, _⟩
    simp [cfaProjectionAt, hsettled, hnetRate, haccountTimestamp]

theorem updateNonApp_preserves_future_modular_cfa_global_projection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) :
    updateNonAppPreservesFutureModularCfaGlobalProjection source s accounts sender receiver
      flowRate liquidationPeriod minimumDeposit operationTimestamp tau := by
  unfold updateNonAppPreservesFutureModularCfaGlobalProjection
  intro hcovered _htimestamp _htau hsource
  dsimp only
  intro hsuccess
  have hprojection := updateNonApp_preserves_cfa_projection source s sender receiver flowRate
    liquidationPeriod minimumDeposit operationTimestamp
  unfold updateNonAppPreservesCfaProjection at hprojection
  have hprojection := hprojection hsource hsuccess
  have hrate := updateNonApp_preserves_pair_net_flow_rate source s sender receiver flowRate
    liquidationPeriod minimumDeposit operationTimestamp
  unfold updateNonAppPreservesPairNetFlowRate at hrate
  have hrate := hrate hsource hsuccess
  refine ⟨hprojection.1, ?_⟩
  apply pairAndFrame_implies_modular_cfa_global_projection
  · exact hcovered
  · exact pairCfaProjectionAt_future_of_operation_and_rate s
      (runUpdateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit
        operationTimestamp).snd sender receiver operationTimestamp tau hprojection.2 hrate.2
  · intro account hmember hsender hreceiver
    have hframe := updateNonApp_frames_unrelated_account source s sender receiver account flowRate
      liquidationPeriod minimumDeposit operationTimestamp
    unfold updateNonAppFramesUnrelatedAccount at hframe
    rcases hframe hsource hsender hreceiver hsuccess with
      ⟨_, hsettled, hnetRate, haccountTimestamp, _, _⟩
    simp [cfaProjectionAt, hsettled, hnetRate, haccountTimestamp]

theorem deleteNonApp_preserves_future_modular_cfa_global_projection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address) (operationTimestamp tau : Uint256) :
    deleteNonAppPreservesFutureModularCfaGlobalProjection source s accounts sender receiver
      operationTimestamp tau := by
  unfold deleteNonAppPreservesFutureModularCfaGlobalProjection
  intro hcovered _htimestamp _htau hsource
  dsimp only
  intro hsuccess
  have hprojection := deleteNonApp_preserves_cfa_projection source s sender receiver
    operationTimestamp
  unfold deleteNonAppPreservesCfaProjection at hprojection
  have hprojection := hprojection hsource hsuccess
  have hrate := deleteNonApp_preserves_pair_net_flow_rate source s sender receiver
    operationTimestamp
  unfold deleteNonAppPreservesPairNetFlowRate at hrate
  have hrate := hrate hsource hsuccess
  refine ⟨hprojection.1, ?_⟩
  apply pairAndFrame_implies_modular_cfa_global_projection
  · exact hcovered
  · exact pairCfaProjectionAt_future_of_operation_and_rate s
      (runDeleteNonApp s sender receiver operationTimestamp).snd sender receiver
      operationTimestamp tau hprojection.2 hrate.2
  · intro account hmember hsender hreceiver
    have hframe := deleteNonApp_frames_unrelated_account source s sender receiver account
      operationTimestamp
    unfold deleteNonAppFramesUnrelatedAccount at hframe
    rcases hframe hsource hsender hreceiver hsuccess with
      ⟨_, hsettled, hnetRate, haccountTimestamp, _, _⟩
    simp [cfaProjectionAt, hsettled, hnetRate, haccountTimestamp]

theorem receiverDeleteCallback_preserves_future_modular_cfa_global_projection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) :
    receiverDeleteCallbackPreservesFutureModularCfaGlobalProjection source s accounts
      sender receiver flowRate liquidationPeriod minimumDeposit operationTimestamp tau := by
  unfold receiverDeleteCallbackPreservesFutureModularCfaGlobalProjection
  intro hcovered _htimestamp _htau hsource _hguards
  dsimp only
  intro hsuccess
  have hprojection := receiverDeleteCallback_preserves_cfa_projection source s sender receiver
    flowRate liquidationPeriod minimumDeposit operationTimestamp
  unfold receiverDeleteCallbackPreservesCfaProjection at hprojection
  have hprojection := hprojection hsource hsuccess
  have hrate := receiverDeleteCallback_preserves_pair_net_flow_rate source s sender receiver
    flowRate liquidationPeriod minimumDeposit operationTimestamp
  unfold receiverDeleteCallbackPreservesPairNetFlowRate at hrate
  have hrate := hrate hsource hsuccess
  refine ⟨hprojection.1, ?_⟩
  apply pairAndFrame_implies_modular_cfa_global_projection
  · exact hcovered
  · exact pairCfaProjectionAt_future_of_operation_and_rate s
      (runReceiverDeleteCallback s sender receiver flowRate liquidationPeriod minimumDeposit
        operationTimestamp).snd sender receiver operationTimestamp tau hprojection.2 hrate.2
  · intro account hmember hsender hreceiver
    have hframe := receiverDeleteCallback_frames_unrelated_account source s sender receiver account
      flowRate liquidationPeriod minimumDeposit operationTimestamp
    unfold receiverDeleteCallbackFramesUnrelatedAccount at hframe
    rcases hframe hsource hsender hreceiver hsuccess with
      ⟨_, hsettled, hnetRate, haccountTimestamp, _, _⟩
    simp [cfaProjectionAt, hsettled, hnetRate, haccountTimestamp]

theorem successfulOneLevel_components_compose {α β γ : Type}
    (outerPrefix : Contract α) (nested : α → Contract β)
    (outerResume : α → β → Contract γ) (accounts : List Address) (timestamp : Uint256) :
    successfulOneLevelComponentsCompose outerPrefix nested outerResume accounts timestamp := by
  unfold successfulOneLevelComponentsCompose PreservesModularCfaGlobalProjection
  intro hprefix hnested hresume pre value post hrun
  unfold runOneLevelOuterNested behavioralOneLevelCallback at hrun
  simp only [Bind.bind, if_true] at hrun
  rcases bind_success_elim _ _ _ _ _ hrun with
    ⟨prefixValue, prefixPost, hprefixRun, htail⟩
  rcases bind_success_elim _ _ _ _ _ htail with
    ⟨nestedValue, nestedPost, hnestedRun, hresumeRun⟩
  exact (hresume prefixValue nestedValue nestedPost value post hresumeRun).trans
    ((hnested prefixValue prefixPost nestedValue nestedPost hnestedRun).trans
      (hprefix pre prefixValue prefixPost hprefixRun))

theorem callbackLevelTwo_is_rejected : callbackLevelTwoRejected := by
  unfold callbackLevelTwoRejected
  intro α nested pre
  simp [behavioralOneLevelCallback, Verity.bind, Verity.require, Contract.run]

theorem failedNested_rolls_back_and_prevents_resume {α β γ : Type}
    (outerPrefix : Contract α) (nested : α → Contract β)
    (outerResume : α → β → Contract γ) :
    failedNestedRollsBackAndPreventsResume outerPrefix nested outerResume := by
  unfold failedNestedRollsBackAndPreventsResume
  intro pre mid prefixValue msg hprefix hnested
  have hprefixRaw := Contract.eq_of_run_success hprefix
  unfold runOneLevelOuterNested behavioralOneLevelCallback
  simp only [Bind.bind, if_true]
  unfold Contract.run Verity.bind
  rw [hprefixRaw]
  cases hnestedRaw : nested prefixValue mid with
  | success nestedValue nestedPost =>
      simp [Contract.run, hnestedRaw] at hnested
  | «revert» nestedMsg nestedState =>
      simp [Contract.run, hnestedRaw] at hnested
      subst nestedMsg
      simp [hnestedRaw]

private theorem require_success_observations
    (cond : Bool) (msg : String) (s t : ContractState)
    (h : (Verity.require cond msg).run s = ContractResult.success () t) :
    cond = true ∧ t = s := by
  constructor
  · exact Verity.Proofs.Stdlib.Automation.require_success_implies_cond cond msg s
      (by rw [h]; rfl)
  · rw [success_state_eq _ _ _ _ h]
    exact preserving_require cond msg s

private theorem getStorage_value_of_success
    (sl : StorageSlot Uint256) (s t : ContractState) (value : Uint256)
    (h : (getStorage sl).run s = ContractResult.success value t) :
    value = s.storage sl.slot := by
  have hraw := Contract.eq_of_run_success h
  change ContractResult.success (s.storage sl.slot) s =
    ContractResult.success value t at hraw
  injection hraw with hvalue _
  exact hvalue.symm

private theorem directOuterHostContext_observations
    (s t : ContractState) (sender : Address)
    (h : (SuperfluidCFA._requireDirectOuterHostContext sender).run s =
      ContractResult.success () t) :
    s.storage 29 = 1 ∧ s.storage 30 = 0 ∧ s.storage 31 = sender ∧ t = s := by
  unfold SuperfluidCFA._requireDirectOuterHostContext at h
  simp only [Bind.bind] at h
  rcases bind_success_elim _ _ _ _ _ h with ⟨direct, s₁, hdirectGet, h⟩
  have hs₁ : s₁ = s := success_state_eq _ _ _ _ hdirectGet
  have hdirect : direct = s.storage 29 := by
    simpa [SuperfluidCFA.hostOuterIsDirectCallContext] using
      getStorage_value_of_success SuperfluidCFA.hostOuterIsDirectCallContext s s₁ direct hdirectGet
  subst s₁
  subst direct
  rcases bind_success_elim _ _ _ _ _ h with ⟨token, s₂, htokenGet, h⟩
  have hs₂ : s₂ = s := success_state_eq _ _ _ _ htokenGet
  have htoken : token = s.storage 30 := by
    simpa [SuperfluidCFA.hostOuterAppCreditToken] using
      getStorage_value_of_success SuperfluidCFA.hostOuterAppCreditToken s s₂ token htokenGet
  subst s₂
  subst token
  rcases bind_success_elim _ _ _ _ _ h with ⟨actor, s₃, hactorGet, h⟩
  have hs₃ : s₃ = s := success_state_eq _ _ _ _ hactorGet
  have hactor : actor = s.storage 31 := by
    simpa [SuperfluidCFA.hostOuterActor] using
      getStorage_value_of_success SuperfluidCFA.hostOuterActor s s₃ actor hactorGet
  subst s₃
  subst actor
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₄, hdirectReq, h⟩
  have hdirectObs := require_success_observations _ _ s s₄ hdirectReq
  have hs₄ := hdirectObs.2
  subst s₄
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, s₅, htokenReq, h⟩
  have htokenObs := require_success_observations _ _ s s₅ htokenReq
  have hs₅ := htokenObs.2
  subst s₅
  have hactorObs := require_success_observations _ _ s t h
  simpa using And.intro hdirectObs.1
    (And.intro htokenObs.1 (And.intro hactorObs.1 hactorObs.2))

set_option maxRecDepth 4096 in
private theorem sourceAppCreditBase_value_of_success
    (flowRate liquidationPeriod value : Uint256) (s t : ContractState)
    (h : (SuperfluidCFA._calculateSourceAppCreditBase flowRate liquidationPeriod).run s =
      ContractResult.success value t) :
    value = clipDepositRoundingUp (mul flowRate liquidationPeriod) := by
  unfold SuperfluidCFA._calculateSourceAppCreditBase at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  by_cases hzero : flowRate = 0
  · subst flowRate
    simp [Verity.pure, Pure.pure, Contract.run] at h
    have hmul : mul (0 : Uint256) liquidationPeriod = 0 :=
      Verity.Core.Uint256.zero_mul liquidationPeriod
    have hclip : clipDepositRoundingUp (mul (0 : Uint256) liquidationPeriod) = 0 := by
      rw [hmul]
      decide
    exact h.1.symm.trans hclip.symm
  · have hzeroBool : (flowRate == 0) = false := by simp [hzero]
    simp only [hzeroBool] at h
    by_cases hlow : mod (mul flowRate liquidationPeriod) 4294967296 > 0
    · simp [hlow, Verity.pure, Pure.pure, Contract.run] at h
      unfold clipDepositRoundingUp
      rw [if_pos hlow]
      dsimp only
      exact h.1.symm
    · simp [hlow, Verity.pure, Pure.pure, Contract.run] at h
      unfold clipDepositRoundingUp
      rw [if_neg hlow]
      dsimp only
      rw [show add (div (mul flowRate liquidationPeriod) 4294967296) 0 =
        div (mul flowRate liquidationPeriod) 4294967296 by
          exact Verity.Core.Uint256.add_zero _]
      exact h.1.symm

private theorem receiverDeleteCallback_prefix_guards_of_success
    (source : PinnedSourceState) (s t : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp newDeposit : Uint256)
    (hsource : pinnedSourcePathRelation source s sender receiver operationTimestamp)
    (h : (SuperfluidCFA._receiverDeleteCallbackOuterPrefix sender receiver flowRate
      liquidationPeriod minimumDeposit operationTimestamp).run s =
        ContractResult.success newDeposit t) :
    ConcreteSelfDeletingCallbackGuards source sender receiver flowRate liquidationPeriod
      minimumDeposit := by
  unfold pinnedSourcePathRelation at hsource
  rcases hsource with ⟨hmodel, _, _⟩
  unfold sourceModelRelation at hmodel
  rcases hmodel with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hsrcSenderApp, hsrcReceiverApp, hsrcJailed,
      hsrcBefore, hsrcAfter, hsrcCreditUsed, hsrcLevel, hsrcActor, hsrcAppAddress,
      hsrcContext, hsrcDelete, hsrcNested, hsrcTokenMatch, hsrcGranted, hsrcAdditional,
      hsrcSelfDelete, hsrcOuterDirect, hsrcOuterToken, hsrcOuterActor⟩
  unfold SuperfluidCFA._receiverDeleteCallbackOuterPrefix at h
  simp only [Bind.bind] at h
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _
    (sourceEnvironment_preserving sender receiver liquidationPeriod minimumDeposit) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, directState, hdirect, h⟩
  have hdirectObs := directOuterHostContext_observations s directState sender hdirect
  have hdirectState := hdirectObs.2.2.2
  subst directState
  rcases bind_success_elim _ _ _ _ _ h with ⟨receiverIsApp, state₁, hget₁, h⟩
  have hstate₁ : state₁ = s := success_state_eq _ _ _ _ hget₁
  have hvalue₁ : receiverIsApp = s.storageMap 10 receiver := by
    simpa [SuperfluidCFA.hostIsApp] using
      getMapping_value_of_success SuperfluidCFA.hostIsApp receiver s state₁ receiverIsApp hget₁
  subst state₁
  subst receiverIsApp
  rcases bind_success_elim _ _ _ _ _ h with ⟨senderIsApp, state₂, hget₂, h⟩
  have hstate₂ : state₂ = s := success_state_eq _ _ _ _ hget₂
  have hvalue₂ : senderIsApp = s.storageMap 10 sender := by
    simpa [SuperfluidCFA.hostIsApp] using
      getMapping_value_of_success SuperfluidCFA.hostIsApp sender s state₂ senderIsApp hget₂
  subst state₂
  subst senderIsApp
  rcases bind_success_elim _ _ _ _ _ h with ⟨receiverIsJailed, state₃, hget₃, h⟩
  have hstate₃ : state₃ = s := success_state_eq _ _ _ _ hget₃
  have hvalue₃ : receiverIsJailed = s.storageMap 11 receiver := by
    simpa [SuperfluidCFA.hostIsJailed] using
      getMapping_value_of_success SuperfluidCFA.hostIsJailed receiver s state₃ receiverIsJailed hget₃
  subst state₃
  subst receiverIsJailed
  rcases bind_success_elim _ _ _ _ _ h with ⟨beforeCreatedNoop, state₄, hget₄, h⟩
  have hstate₄ : state₄ = s := success_state_eq _ _ _ _ hget₄
  have hvalue₄ : beforeCreatedNoop = s.storageMap 12 receiver := by
    simpa [SuperfluidCFA.hostBeforeCreatedNoop] using
      getMapping_value_of_success SuperfluidCFA.hostBeforeCreatedNoop receiver s state₄
        beforeCreatedNoop hget₄
  subst state₄
  subst beforeCreatedNoop
  rcases bind_success_elim _ _ _ _ _ h with ⟨afterCreatedEnabled, state₅, hget₅, h⟩
  have hstate₅ : state₅ = s := success_state_eq _ _ _ _ hget₅
  have hvalue₅ : afterCreatedEnabled = s.storageMap 13 receiver := by
    simpa [SuperfluidCFA.hostAfterCreatedEnabled] using
      getMapping_value_of_success SuperfluidCFA.hostAfterCreatedEnabled receiver s state₅
        afterCreatedEnabled hget₅
  subst state₅
  subst afterCreatedEnabled
  rcases bind_success_elim _ _ _ _ _ h with ⟨callbackCreditUsed, state₆, hget₆, h⟩
  have hstate₆ : state₆ = s := success_state_eq _ _ _ _ hget₆
  have hvalue₆ : callbackCreditUsed = s.storageMap 14 receiver := by
    simpa [SuperfluidCFA.hostCallbackCreditUsed] using
      getMapping_value_of_success SuperfluidCFA.hostCallbackCreditUsed receiver s state₆
        callbackCreditUsed hget₆
  subst state₆
  subst callbackCreditUsed
  rcases bind_success_elim _ _ _ _ _ h with ⟨callbackLevel, state₇, hget₇, h⟩
  have hstate₇ : state₇ = s := success_state_eq _ _ _ _ hget₇
  have hvalue₇ : callbackLevel = s.storageMap 15 receiver := by
    simpa [SuperfluidCFA.hostCallbackLevel] using
      getMapping_value_of_success SuperfluidCFA.hostCallbackLevel receiver s state₇ callbackLevel hget₇
  subst state₇
  subst callbackLevel
  rcases bind_success_elim _ _ _ _ _ h with ⟨callbackActor, state₈, hget₈, h⟩
  have hstate₈ : state₈ = s := success_state_eq _ _ _ _ hget₈
  have hvalue₈ : callbackActor = s.storageMap 16 receiver := by
    simpa [SuperfluidCFA.hostCallbackActor] using
      getMapping_value_of_success SuperfluidCFA.hostCallbackActor receiver s state₈ callbackActor hget₈
  subst state₈
  subst callbackActor
  rcases bind_success_elim _ _ _ _ _ h with ⟨callbackAppAddress, state₉, hget₉, h⟩
  have hstate₉ : state₉ = s := success_state_eq _ _ _ _ hget₉
  have hvalue₉ : callbackAppAddress = s.storageMap 17 receiver := by
    simpa [SuperfluidCFA.hostCallbackAppAddress] using
      getMapping_value_of_success SuperfluidCFA.hostCallbackAppAddress receiver s state₉
        callbackAppAddress hget₉
  subst state₉
  subst callbackAppAddress
  rcases bind_success_elim _ _ _ _ _ h with ⟨isAppCallbackContext, state₁₀, hget₁₀, h⟩
  have hstate₁₀ : state₁₀ = s := success_state_eq _ _ _ _ hget₁₀
  have hvalue₁₀ : isAppCallbackContext = s.storageMap 18 receiver := by
    simpa [SuperfluidCFA.hostIsAppCallbackContext] using
      getMapping_value_of_success SuperfluidCFA.hostIsAppCallbackContext receiver s state₁₀
        isAppCallbackContext hget₁₀
  subst state₁₀
  subst isAppCallbackContext
  rcases bind_success_elim _ _ _ _ _ h with ⟨contextualDeleteEnabled, state₁₁, hget₁₁, h⟩
  have hstate₁₁ : state₁₁ = s := success_state_eq _ _ _ _ hget₁₁
  have hvalue₁₁ : contextualDeleteEnabled = s.storageMap 19 receiver := by
    simpa [SuperfluidCFA.hostContextualDeleteEnabled] using
      getMapping_value_of_success SuperfluidCFA.hostContextualDeleteEnabled receiver s state₁₁
        contextualDeleteEnabled hget₁₁
  subst state₁₁
  subst contextualDeleteEnabled
  rcases bind_success_elim _ _ _ _ _ h with ⟨nestedCallbackSuppressed, state₁₂, hget₁₂, h⟩
  have hstate₁₂ : state₁₂ = s := success_state_eq _ _ _ _ hget₁₂
  have hvalue₁₂ : nestedCallbackSuppressed = s.storageMap 20 receiver := by
    simpa [SuperfluidCFA.hostNestedCallbackSuppressed] using
      getMapping_value_of_success SuperfluidCFA.hostNestedCallbackSuppressed receiver s state₁₂
        nestedCallbackSuppressed hget₁₂
  subst state₁₂
  subst nestedCallbackSuppressed
  rcases bind_success_elim _ _ _ _ _ h with ⟨appCreditTokenMatches, state₁₃, hget₁₃, h⟩
  have hstate₁₃ : state₁₃ = s := success_state_eq _ _ _ _ hget₁₃
  have hvalue₁₃ : appCreditTokenMatches = s.storageMap 21 receiver := by
    simpa [SuperfluidCFA.hostAppCreditTokenMatches] using
      getMapping_value_of_success SuperfluidCFA.hostAppCreditTokenMatches receiver s state₁₃
        appCreditTokenMatches hget₁₃
  subst state₁₃
  subst appCreditTokenMatches
  rcases bind_success_elim _ _ _ _ _ h with ⟨appCreditGranted, state₁₄, hget₁₄, h⟩
  have hstate₁₄ : state₁₄ = s := success_state_eq _ _ _ _ hget₁₄
  have hvalue₁₄ : appCreditGranted = s.storageMap 22 receiver := by
    simpa [SuperfluidCFA.hostAppCreditGranted] using
      getMapping_value_of_success SuperfluidCFA.hostAppCreditGranted receiver s state₁₄
        appCreditGranted hget₁₄
  subst state₁₄
  subst appCreditGranted
  rcases bind_success_elim _ _ _ _ _ h with ⟨additionalAppCredit, state₁₅, hget₁₅, h⟩
  have hstate₁₅ : state₁₅ = s := success_state_eq _ _ _ _ hget₁₅
  have hvalue₁₅ : additionalAppCredit = s.storageMap 23 receiver := by
    simpa [SuperfluidCFA.hostAdditionalAppCredit] using
      getMapping_value_of_success SuperfluidCFA.hostAdditionalAppCredit receiver s state₁₅
        additionalAppCredit hget₁₅
  subst state₁₅
  subst additionalAppCredit
  rcases bind_success_elim _ _ _ _ _ h with ⟨receiverIsSelfDeleting, state₁₆, hget₁₆, h⟩
  have hstate₁₆ : state₁₆ = s := success_state_eq _ _ _ _ hget₁₆
  have hvalue₁₆ : receiverIsSelfDeleting = s.storageMap 28 receiver := by
    simpa [SuperfluidCFA.hostIsSelfDeletingFlowApp] using
      getMapping_value_of_success SuperfluidCFA.hostIsSelfDeletingFlowApp receiver s state₁₆
        receiverIsSelfDeleting hget₁₆
  subst state₁₆
  subst receiverIsSelfDeleting
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₁, hreq₁, h⟩
  have hreqObs₁ := require_success_observations _ _ s reqState₁ hreq₁
  have hreqState₁ := hreqObs₁.2
  have hreceiverApp : s.storageMap 10 receiver = 1 := by simpa using hreqObs₁.1
  subst reqState₁
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₂, hreq₂, h⟩
  have hreqObs₂ := require_success_observations _ _ s reqState₂ hreq₂
  have hreqState₂ := hreqObs₂.2
  have hsenderApp : s.storageMap 10 sender = 0 := by simpa using hreqObs₂.1
  subst reqState₂
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₃, hreq₃, h⟩
  have hreqObs₃ := require_success_observations _ _ s reqState₃ hreq₃
  have hreqState₃ := hreqObs₃.2
  have hjailed : s.storageMap 11 receiver = 0 := by simpa using hreqObs₃.1
  subst reqState₃
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₄, hreq₄, h⟩
  have hreqObs₄ := require_success_observations _ _ s reqState₄ hreq₄
  have hreqState₄ := hreqObs₄.2
  have hbefore : s.storageMap 12 receiver = 1 := by simpa using hreqObs₄.1
  subst reqState₄
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₅, hreq₅, h⟩
  have hreqObs₅ := require_success_observations _ _ s reqState₅ hreq₅
  have hreqState₅ := hreqObs₅.2
  have hafter : s.storageMap 13 receiver = 1 := by simpa using hreqObs₅.1
  subst reqState₅
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₆, hreq₆, h⟩
  have hreqObs₆ := require_success_observations _ _ s reqState₆ hreq₆
  have hreqState₆ := hreqObs₆.2
  have hcreditUsed : s.storageMap 14 receiver = 0 := by simpa using hreqObs₆.1
  subst reqState₆
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₇, hreq₇, h⟩
  have hreqObs₇ := require_success_observations _ _ s reqState₇ hreq₇
  have hreqState₇ := hreqObs₇.2
  have hlevel : s.storageMap 15 receiver = 1 := by simpa using hreqObs₇.1
  subst reqState₇
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₈, hreq₈, h⟩
  have hreqObs₈ := require_success_observations _ _ s reqState₈ hreq₈
  have hreqState₈ := hreqObs₈.2
  have hactor : s.storageMap 16 receiver = receiver := by simpa using hreqObs₈.1
  subst reqState₈
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₉, hreq₉, h⟩
  have hreqObs₉ := require_success_observations _ _ s reqState₉ hreq₉
  have hreqState₉ := hreqObs₉.2
  have happAddress : s.storageMap 17 receiver = receiver := by simpa using hreqObs₉.1
  subst reqState₉
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₁₀, hreq₁₀, h⟩
  have hreqObs₁₀ := require_success_observations _ _ s reqState₁₀ hreq₁₀
  have hreqState₁₀ := hreqObs₁₀.2
  have hcontext : s.storageMap 18 receiver = 1 := by simpa using hreqObs₁₀.1
  subst reqState₁₀
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₁₁, hreq₁₁, h⟩
  have hreqObs₁₁ := require_success_observations _ _ s reqState₁₁ hreq₁₁
  have hreqState₁₁ := hreqObs₁₁.2
  have hdelete : s.storageMap 19 receiver = 1 := by simpa using hreqObs₁₁.1
  subst reqState₁₁
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₁₂, hreq₁₂, h⟩
  have hreqObs₁₂ := require_success_observations _ _ s reqState₁₂ hreq₁₂
  have hreqState₁₂ := hreqObs₁₂.2
  have hnested : s.storageMap 20 receiver = 1 := by simpa using hreqObs₁₂.1
  subst reqState₁₂
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₁₃, hreq₁₃, h⟩
  have hreqObs₁₃ := require_success_observations _ _ s reqState₁₃ hreq₁₃
  have hreqState₁₃ := hreqObs₁₃.2
  have htokenMatch : s.storageMap 21 receiver = 1 := by simpa using hreqObs₁₃.1
  subst reqState₁₃
  rcases bind_success_elim _ _ _ _ _ h with ⟨_, reqState₁₄, hreq₁₄, h⟩
  have hreqObs₁₄ := require_success_observations _ _ s reqState₁₄ hreq₁₄
  have hreqState₁₄ := hreqObs₁₄.2
  have hselfDelete : s.storageMap 28 receiver = 1 := by simpa using hreqObs₁₄.1
  subst reqState₁₄
  rcases preserving_bind_tail _ _ _ _ _ (emptyFlow_preserving sender receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving sender) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (canonical_preserving receiver) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_getMapping _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases preserving_bind_tail _ _ _ _ _ (preserving_require _ _) h with ⟨_, h⟩
  rcases bind_success_elim _ _ _ _ _ h with ⟨appCreditBase, creditState, hcreditBase, h⟩
  have hcreditState : creditState = s := by
    rw [success_state_eq _ _ _ _ hcreditBase]
    exact sourceAppCreditBase_preserving flowRate liquidationPeriod s
  have hcreditBaseValue := sourceAppCreditBase_value_of_success flowRate liquidationPeriod
    appCreditBase s creditState hcreditBase
  subst creditState
  rcases preserving_bind_tail _ _ _ _ _
    (sourceDeposit_preserving flowRate liquidationPeriod minimumDeposit) h with ⟨_, h⟩
  have hfixed :
      source.hostIsApp receiver = 1 ∧ source.hostIsApp sender = 0 ∧
      source.hostIsJailed receiver = 0 ∧ source.hostBeforeCreatedNoop receiver = 1 ∧
      source.hostAfterCreatedEnabled receiver = 1 ∧
      source.hostCallbackCreditUsed receiver = 0 ∧ source.hostCallbackLevel receiver = 1 ∧
      source.hostCallbackActor receiver = receiver ∧
      source.hostCallbackAppAddress receiver = receiver ∧
      source.hostIsAppCallbackContext receiver = 1 ∧
      source.hostContextualDeleteEnabled receiver = 1 ∧
      source.hostNestedCallbackSuppressed receiver = 1 ∧
      source.hostAppCreditTokenMatches receiver = 1 ∧
      source.hostIsSelfDeletingFlowApp receiver = 1 ∧
      source.hostOuterIsDirectCallContext = 1 ∧ source.hostOuterAppCreditToken = 0 ∧
      source.hostOuterActor = sender := by
    exact ⟨hsrcReceiverApp.trans hreceiverApp, hsrcSenderApp.trans hsenderApp,
      hsrcJailed.trans hjailed, hsrcBefore.trans hbefore, hsrcAfter.trans hafter,
      hsrcCreditUsed.trans hcreditUsed, hsrcLevel.trans hlevel, hsrcActor.trans hactor,
      hsrcAppAddress.trans happAddress, hsrcContext.trans hcontext, hsrcDelete.trans hdelete,
      hsrcNested.trans hnested, hsrcTokenMatch.trans htokenMatch,
      hsrcSelfDelete.trans hselfDelete, hsrcOuterDirect.trans hdirectObs.1,
      hsrcOuterToken.trans hdirectObs.2.1, hsrcOuterActor.trans hdirectObs.2.2.1⟩
  have hcreditGuards :
      let creditBase := clipDepositRoundingUp (mul flowRate liquidationPeriod)
      if creditBase = 0 then
        source.hostAdditionalAppCredit receiver = 0 ∧
        source.hostAppCreditGranted receiver = 0
      else
        source.hostAdditionalAppCredit receiver ≥ 4294967296 ∧
        source.hostAdditionalAppCredit receiver ≥ minimumDeposit ∧
        (source.hostAdditionalAppCredit receiver = 4294967296 ∨
          source.hostAdditionalAppCredit receiver = minimumDeposit) ∧
        source.hostAppCreditGranted receiver =
          add creditBase (source.hostAdditionalAppCredit receiver) := by
    dsimp only
    split at h
    · rename_i hzeroBranch
      have hzero : appCreditBase = 0 := by simpa using hzeroBranch
      rcases bind_success_elim _ _ _ _ _ h with ⟨_, creditReqState₁, hcreditReq₁, h⟩
      have hcreditReqObs₁ := require_success_observations _ _ s creditReqState₁ hcreditReq₁
      have hcreditReqState₁ := hcreditReqObs₁.2
      have hadditionalZero : s.storageMap 23 receiver = 0 := by
        simpa using hcreditReqObs₁.1
      subst creditReqState₁
      rcases bind_success_elim _ _ _ _ _ h with ⟨_, creditReqState₂, hcreditReq₂, _⟩
      have hcreditReqObs₂ := require_success_observations _ _ s creditReqState₂ hcreditReq₂
      have hgrantedZero : s.storageMap 22 receiver = 0 := by
        simpa using hcreditReqObs₂.1
      have hspecZero : clipDepositRoundingUp (mul flowRate liquidationPeriod) = 0 :=
        hcreditBaseValue.symm.trans hzero
      rw [if_pos hspecZero]
      exact ⟨hsrcAdditional.trans hadditionalZero, hsrcGranted.trans hgrantedZero⟩
    · rename_i hnonzeroBranch
      have hnonzero : appCreditBase ≠ 0 := by simpa using hnonzeroBranch
      rcases bind_success_elim _ _ _ _ _ h with ⟨_, creditReqState₁, hcreditReq₁, h⟩
      have hcreditReqObs₁ := require_success_observations _ _ s creditReqState₁ hcreditReq₁
      have hcreditReqState₁ := hcreditReqObs₁.2
      have hadditionalDefault : s.storageMap 23 receiver ≥ 4294967296 := by
        simpa using hcreditReqObs₁.1
      subst creditReqState₁
      rcases bind_success_elim _ _ _ _ _ h with ⟨_, creditReqState₂, hcreditReq₂, h⟩
      have hcreditReqObs₂ := require_success_observations _ _ s creditReqState₂ hcreditReq₂
      have hcreditReqState₂ := hcreditReqObs₂.2
      have hadditionalMinimum : s.storageMap 23 receiver ≥ minimumDeposit := by
        simpa using hcreditReqObs₂.1
      subst creditReqState₂
      rcases bind_success_elim _ _ _ _ _ h with ⟨_, creditReqState₃, hcreditReq₃, h⟩
      have hcreditReqObs₃ := require_success_observations _ _ s creditReqState₃ hcreditReq₃
      have hcreditReqState₃ := hcreditReqObs₃.2
      have hadditionalMax : s.storageMap 23 receiver = 4294967296 ∨
          s.storageMap 23 receiver = minimumDeposit := by
        simpa using hcreditReqObs₃.1
      subst creditReqState₃
      rcases bind_success_elim _ _ _ _ _ h with ⟨_, creditReqState₄, hcreditReq₄, _⟩
      have hcreditReqObs₄ := require_success_observations _ _ s creditReqState₄ hcreditReq₄
      have hgranted : s.storageMap 22 receiver = add appCreditBase (s.storageMap 23 receiver) := by
        simpa using hcreditReqObs₄.1
      have hspecNonzero : clipDepositRoundingUp (mul flowRate liquidationPeriod) ≠ 0 := by
        intro hspecZero
        exact hnonzero (hcreditBaseValue.trans hspecZero)
      rw [if_neg hspecNonzero]
      refine ⟨?_, ?_, hadditionalMax.imp hsrcAdditional.trans hsrcAdditional.trans, ?_⟩
      · rw [hsrcAdditional]
        exact hadditionalDefault
      · rw [hsrcAdditional]
        exact hadditionalMinimum
      · exact hsrcGranted.trans (hgranted.trans ((congrArg
          (fun credit => add credit (s.storageMap 23 receiver)) hcreditBaseValue).trans
            (congrArg (fun additional =>
              add (clipDepositRoundingUp (mul flowRate liquidationPeriod)) additional)
              hsrcAdditional.symm)))
  rcases hfixed with
    ⟨hreceiverAppSource, hsenderAppSource, hjailedSource, hbeforeSource, hafterSource,
      hcreditUsedSource, hlevelSource, hactorSource, happAddressSource, hcontextSource,
      hdeleteSource, hnestedSource, htokenMatchSource, hselfDeleteSource,
      houterDirectSource, houterTokenSource, houterActorSource⟩
  unfold ConcreteSelfDeletingCallbackGuards
  exact ⟨hreceiverAppSource, hsenderAppSource, hjailedSource, hbeforeSource, hafterSource,
    hcreditUsedSource, hlevelSource, hactorSource, happAddressSource, hcontextSource,
    hdeleteSource, hnestedSource, htokenMatchSource, hselfDeleteSource,
    houterDirectSource, houterTokenSource, houterActorSource, hcreditGuards⟩

theorem receiverDeleteCallback_matches_factored_instance_behavior
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp : Uint256) :
    receiverDeleteCallbackFactoredInstanceBehavior source s sender receiver flowRate
      liquidationPeriod minimumDeposit operationTimestamp := by
  unfold receiverDeleteCallbackFactoredInstanceBehavior
  intro _htimestamp hsource
  dsimp only
  intro hsuccess
  have hreload := receiverDeleteCallback_reloads_final_zero source s sender receiver flowRate
    liquidationPeriod minimumDeposit operationTimestamp
  unfold receiverDeleteCallbackReloadsFinalZero at hreload
  have hreload := hreload hsource hsuccess
  unfold modelSucceeded at hsuccess
  rcases success_exists
    (runReceiverDeleteCallback s sender receiver flowRate liquidationPeriod minimumDeposit
      operationTimestamp) hsuccess with ⟨resultValue, post, hrun⟩
  have hfull :
      (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback sender receiver flowRate
        liquidationPeriod minimumDeposit operationTimestamp).run s =
          ContractResult.success resultValue post := by
    simpa [runReceiverDeleteCallback] using hrun
  have hprefixExecution := hfull
  unfold SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback runOneLevelOuterNested
    behavioralOneLevelCallback at hprefixExecution
  simp only [Bind.bind, if_true] at hprefixExecution
  rcases bind_success_elim _ _ _ _ _ hprefixExecution with
    ⟨prefixDeposit, prefixPost, hprefix, _⟩
  have hguards := receiverDeleteCallback_prefix_guards_of_success source s prefixPost sender receiver
    flowRate liquidationPeriod minimumDeposit operationTimestamp prefixDeposit hsource hprefix
  refine ⟨hguards, hreload.1, ?_, ?_⟩
  · rfl
  · rw [hreload.2.2.1]
    exact hreload.2.1

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
