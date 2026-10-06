import Benchmark.Cases.KPK.SharesSettlementAccounting.Specs
import Mathlib.Tactic.NormNum

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity Verity.Stdlib.Math
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

@[simp] theorem word_modulus : Verity.Core.Uint256.modulus = wordLimit := rfl

-- Explicit success decomposition: errors cannot be used as successful witnesses.
theorem tx_bind_ok (c : Tx α) (f : α → Tx β) (s t : State) (b : β)
    (h : (c >>= f) s = .ok (b,t)) :
    ∃ a m, c s = .ok (a,m) ∧ f a m = .ok (b,t) := by
  simp only [Bind.bind, StateT.bind, Except.bind] at h
  cases hc : c s with
  | error e => rw [hc] at h; cases h
  | ok v => rcases v with ⟨a,m⟩; exact ⟨a,m,rfl,by simpa only [hc] using h⟩

theorem word_val (n : Nat) (h : n < wordLimit) : (word n).val = n := by
  exact Nat.mod_eq_of_lt h

theorem word_val_lt (n : Nat) : (word n).val < wordLimit := (word n).isLt

theorem checkedSub_run (a b : Nat) (ha : a < wordLimit) (hb : b < wordLimit) (s : State) :
    checkedSub a b s = if b ≤ a then .ok (a-b,s) else .error "Panic(0x11): arithmetic underflow" := by
  by_cases hba : b ≤ a
  · have hr : a-b < wordLimit := by omega
    have hs : (word a - word b).val = a-b := by
      simpa only [word_val a ha, word_val b hb] using
        Verity.Core.Uint256.sub_eq_of_le (a := word a) (b := word b)
          (by simpa only [word_val a ha, word_val b hb] using hba)
    simp [checkedSub, liftCaller, subPanic, requireSomeUint, safeSub,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      Verity.pure, Verity.bind, Verity.require, hba, hs, word_val a ha, word_val b hb, show ¬a < b by omega]
  · simp [checkedSub, liftCaller, subPanic, requireSomeUint, safeSub,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      Verity.pure, Verity.bind, Verity.require, hba, word,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, show a < b by omega]

theorem checkedMul_run (a b : Nat) (ha : a < wordLimit) (hb : b < wordLimit) (s : State) :
    checkedMul a b s = if a*b < wordLimit then .ok (a*b,s) else .error "Panic(0x11): arithmetic overflow" := by
  have hm : MAX_UINT256 = wordLimit-1 := rfl
  by_cases hr : a*b < wordLimit
  · have hmax : ¬wordLimit-1 < a*b := by omega
    have hs : (word a * word b).val = a*b := by
      simpa only [word_val a ha, word_val b hb] using
        Verity.Core.Uint256.mul_eq_of_lt (a := word a) (b := word b)
          (by simpa only [word_val a ha, word_val b hb, word_modulus] using hr)
    simp [checkedMul, liftCaller, mulPanic, requireSomeUint, safeMul,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      Verity.pure, Verity.bind, Verity.require, hr, hm, hmax, hs, word_val a ha, word_val b hb]
  · have hmax : wordLimit-1 < a*b := by dsimp [wordLimit] at *; omega
    simp [checkedMul, liftCaller, mulPanic, requireSomeUint, safeMul,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      Verity.pure, Verity.bind, Verity.require, hr, hm, hmax, word,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem mulDiv_run (a b d : Nat) (ha : a < wordLimit) (hb : b < wordLimit)
    (hd : d < wordLimit) (s : State) :
    mulDiv a b d s = if d = 0 ∨ wordLimit ≤ a*b/d then .error "mulDiv overflow/division"
      else .ok (a*b/d,s) := by
  have hm : MAX_UINT256 = wordLimit-1 := rfl
  by_cases hz : d = 0
  · subst d
    simp [mulDiv, liftCaller, requireSomeUint, mulDiv512Down?,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      Verity.pure, Verity.bind, Verity.require, word]
  · by_cases hr : a*b/d < wordLimit
    · have hmax : ¬wordLimit-1 < a*b/d := by omega
      simp [mulDiv, liftCaller, requireSomeUint, mulDiv512Down?,
        Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
        Verity.pure, Verity.bind, Verity.require, hz, hr, hm, hmax, word,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd,
        Nat.mod_eq_of_lt hr, show ¬wordLimit ≤ a*b/d by omega]
    · have hmax : wordLimit-1 < a*b/d := by dsimp [wordLimit] at *; omega
      simp [mulDiv, liftCaller, requireSomeUint, mulDiv512Down?,
        Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
        Verity.pure, Verity.bind, Verity.require, hz, hr, hm, hmax, word,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd,
        show wordLimit ≤ a*b/d by omega]

-- Checked helpers do not change ANY caller, token, module or request state.
theorem checkedSub_success (a b q : Nat) (s t : State)
    (ha : a < wordLimit) (hb : b < wordLimit)
    (h : checkedSub a b s = .ok (q,t)) : b ≤ a ∧ q = a-b ∧ t = s := by
  rw [checkedSub_run a b ha hb s] at h
  split at h <;> simp_all

theorem checkedMul_success (a b q : Nat) (s t : State)
    (ha : a < wordLimit) (hb : b < wordLimit)
    (h : checkedMul a b s = .ok (q,t)) : a*b < wordLimit ∧ q = a*b ∧ t = s := by
  rw [checkedMul_run a b ha hb s] at h
  split at h <;> simp_all

theorem mulDiv_success (a b d q : Nat) (s t : State)
    (ha : a < wordLimit) (hb : b < wordLimit) (hd : d < wordLimit)
    (h : mulDiv a b d s = .ok (q,t)) :
    d ≠ 0 ∧ q = a*b/d ∧ q < wordLimit ∧ t = s := by
  rw [mulDiv_run a b d ha hb hd s] at h
  split at h <;> simp_all

-- This structural property follows from the reviewed configuration bounds.
theorem decimal_scale_bounded (d : Nat) (hd : d ≤ 36) :
    10^d < wordLimit ∧ 10^d * wad < wordLimit := by
  have hpow : 10^d ≤ 10^36 := Nat.pow_le_pow_right (by omega) hd
  constructor
  · have hc : 10^36 < wordLimit := by norm_num [wordLimit]
    omega
  · have hc : 10^36 * wad < wordLimit := by norm_num [wordLimit,wad]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right wad hpow) hc

theorem assetsToShares_success (amount price q : Nat) (asset : Address) (s t : State)
    (ha : amount < wordLimit) (hp : price < wordLimit)
    (hd : (s.config.assets asset).decimals ≤ 36)
    (h : assetsToShares amount price asset s = .ok (q,t)) :
    q = Mint amount price (s.config.assets asset).decimals ∧ q < wordLimit ∧ t = s := by
  have hw : wad*wad < wordLimit := by norm_num [wad,wordLimit]
  have hu : usd < wordLimit := by norm_num [usd,wordLimit]
  have hscale := decimal_scale_bounded _ hd
  by_cases hz : price = 0 ∨ amount = 0
  · have hzB : (price == 0 || amount == 0) = true := by simpa using hz
    simp [assetsToShares, hzB, Pure.pure, StateT.pure, Except.pure] at h
    rcases h with ⟨rfl,rfl⟩
    simp [Mint,hz,wordLimit]
  · have hzB : (price == 0 || amount == 0) = false := by simpa using hz
    simp only [assetsToShares, hzB, Bool.false_eq_true, ↓reduceIte] at h
    change ((guard (s.config.assets asset).canDeposit "NotAnApprovedAsset") >>=
      fun _ => mulDiv amount (wad*wad) price >>= fun value =>
        checkedMul (10^(s.config.assets asset).decimals) wad >>= fun scale =>
          mulDiv value usd scale) s = .ok (q,t) at h
    obtain ⟨u,m,hg,h⟩ := tx_bind_ok _ _ _ _ _ h
    have hm : m = s := by
      cases hc : (s.config.assets asset).canDeposit <;>
        simp [guard, hc, Pure.pure, StateT.pure, Except.pure,
          MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift,
          Bind.bind, Except.bind] at hg
      exact hg.symm
    subst m
    obtain ⟨value,m,hv,h⟩ := tx_bind_ok _ _ _ _ _ h
    obtain ⟨_,hvalue,hvalueBound,hmid⟩ := mulDiv_success _ _ _ _ _ _ ha hw hp hv
    subst m
    obtain ⟨scale,m,hs,h⟩ := tx_bind_ok _ _ _ _ _ h
    obtain ⟨_,hscaleEq,hmid⟩ := checkedMul_success _ _ _ _ _ hscale.1
      (by norm_num [wad,wordLimit]) hs
    subst m
    obtain ⟨_,hq,hqBound,ht⟩ := mulDiv_success _ _ _ _ _ _ hvalueBound hu
      (by simpa only [hscaleEq] using hscale.2) h
    refine ⟨?_,hqBound,ht⟩
    simp only [Mint, if_neg hz, hq, hvalue, hscaleEq]

theorem guard_success (p : Bool) (e : String) (s t : State) (u : Unit)
    (h : guard p e s = .ok (u,t)) : p = true ∧ t = s := by
  cases p <;> simp [guard, Pure.pure, StateT.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift,
    Bind.bind, Except.bind] at h ⊢
  exact h.symm

theorem sharesToAssets_success (shares price q : Nat) (asset : Address) (s t : State)
    (ha : shares < wordLimit) (hp : price < wordLimit)
    (hd : (s.config.assets asset).decimals ≤ 36)
    (h : sharesToAssets shares price asset s = .ok (q,t)) :
    q = Out shares price (s.config.assets asset).decimals ∧ q < wordLimit ∧ t = s := by
  have hw : wad*wad < wordLimit := by norm_num [wad,wordLimit]
  have hu : usd < wordLimit := by norm_num [usd,wordLimit]
  have hscale := decimal_scale_bounded _ hd
  by_cases hz : price = 0 ∨ shares = 0
  · have hzB : (price == 0 || shares == 0) = true := by simpa using hz
    simp [sharesToAssets, hzB, Pure.pure, StateT.pure, Except.pure] at h
    rcases h with ⟨rfl,rfl⟩
    simp [Out,hz,wordLimit]
  · have hzB : (price == 0 || shares == 0) = false := by simpa using hz
    simp only [sharesToAssets, hzB, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨u0,m0,hpure,h1⟩ := tx_bind_ok _ _ _ _ _ h
    have hm0 : m0 = s := by
      simpa only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
        using congrArg Prod.snd (Except.ok.inj hpure).symm
    subst m0
    obtain ⟨st,m0,hget,h2⟩ := tx_bind_ok _ _ _ _ _ h1
    have hg : st = s ∧ m0 = s := by
      simpa only [get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] using hget.symm
    rcases hg with ⟨rfl,rfl⟩
    obtain ⟨u,m,hg,h⟩ := tx_bind_ok _ _ _ _ _ h2
    have hm := (guard_success _ _ _ _ _ hg).2
    rw [hm] at h
    obtain ⟨priceWad,m,hmul,h⟩ := tx_bind_ok _ _ _ _ _ h
    obtain ⟨hpb,hpEq,hmid⟩ := checkedMul_success _ _ _ _ _ hp
      (by norm_num [wad,wordLimit]) hmul
    rw [hmid] at h
    obtain ⟨value,m,hv,h⟩ := tx_bind_ok _ _ _ _ _ h
    obtain ⟨_,hvalue,hvalueBound,hmid⟩ := mulDiv_success _ _ _ _ _ _ ha
      (by simpa only [hpEq] using hpb) hu hv
    rw [hmid] at h
    obtain ⟨_,hq,hqBound,ht⟩ := mulDiv_success _ _ _ _ _ _ hvalueBound hscale.1 hw h
    refine ⟨?_,hqBound,ht⟩
    simp only [Out, if_neg hz, hq, hvalue, hpEq]

theorem record_run (e : Effect) (s : State) :
    record e s = .ok ((), {s with trace := s.trace ++ [e]}) := rfl

theorem putExternal_run (token : Address) (slot value : Nat) (s : State) :
    putExternal token slot value s =
      .ok ((), {s with external := writeExternal s.external token.val slot value}) := rfl

theorem safeTransfer_run (env : Environment) (token fromAddr toAddr : Address)
    (amount : Nat) (s : State)
    (hc : (env.hasCode token && env.isToken token && env.tokenAccepts token) = true)
    (ht : (token != s.config.self) = true)
    (he : (fromAddr != 0 && toAddr != 0) = true)
    (ho : assetBalance s token fromAddr < wordLimit) (ha : amount < wordLimit)
    (hb : amount ≤ assetBalance s token fromAddr) :
    safeTransfer env token fromAddr toAddr amount s =
      .ok ((), {s with
        external := tokenWordTransfer s.external token fromAddr toAddr amount
        trace := s.trace ++ [.assetTransfer token fromAddr toAddr amount]}) := by
  simp only [safeTransfer, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
    guard, hc, ht, he, ↓reduceIte, checkedSub_run _ _ ho ha s, hb,
    putExternal_run, record_run]
  rfl

theorem allowance_slot_ne_balance (owner spender x : Address) :
    aslot owner spender ≠ bslot x := by
  unfold aslot bslot
  omega

theorem balance_after_allowance_write (s : State) (token owner spender x : Address)
    (value : Nat) :
    assetBalance {s with external := writeExternal s.external token.val (aslot owner spender) value}
      token x = assetBalance s token x := by
  simp [assetBalance, writeExternal, show bslot x ≠ aslot owner spender from
    Ne.symm (allowance_slot_ne_balance _ _ _)]

theorem safeTransferFrom_infinite_run (env : Environment) (token spender fromAddr toAddr : Address)
    (amount : Nat) (s : State)
    (hi : assetAllowance s token fromAddr spender = wordLimit-1)
    (hc : (env.hasCode token && env.isToken token && env.tokenAccepts token) = true)
    (ht : (token != s.config.self) = true)
    (he : (fromAddr != 0 && toAddr != 0) = true)
    (ho : assetBalance s token fromAddr < wordLimit) (ha : amount < wordLimit)
    (hb : amount ≤ assetBalance s token fromAddr) :
    safeTransferFrom env token spender fromAddr toAddr amount s =
      .ok ((), {s with
        external := tokenWordTransfer s.external token fromAddr toAddr amount
        trace := s.trace ++ [.assetTransfer token fromAddr toAddr amount]}) := by
  simp only [safeTransferFrom, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
    hi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact safeTransfer_run _ _ _ _ _ _ hc ht he ho ha hb

theorem safeTransferFrom_finite_run (env : Environment) (token spender fromAddr toAddr : Address)
    (amount : Nat) (s : State)
    (hi : assetAllowance s token fromAddr spender ≠ wordLimit-1)
    (hc : (env.hasCode token && env.isToken token && env.tokenAccepts token) = true)
    (ht : (token != s.config.self) = true)
    (he : (fromAddr != 0 && toAddr != 0) = true)
    (ho : assetBalance s token fromAddr < wordLimit) (ha : amount < wordLimit)
    (hal : assetAllowance s token fromAddr spender < wordLimit)
    (hsp : amount ≤ assetAllowance s token fromAddr spender)
    (hb : amount ≤ assetBalance s token fromAddr) :
    safeTransferFrom env token spender fromAddr toAddr amount s =
      .ok ((), {s with
        external := tokenWordTransfer
          (writeExternal s.external token.val (aslot fromAddr spender)
            (assetAllowance s token fromAddr spender - amount)) token fromAddr toAddr amount
        trace := s.trace ++ [.allowanceSpent token fromAddr spender amount,
          .assetTransfer token fromAddr toAddr amount]}) := by
  have hiB : (assetAllowance s token fromAddr spender != wordLimit-1) = true := by simpa using hi
  simp only [safeTransferFrom, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
    hiB, ↓reduceIte, checkedSub_run _ _ hal ha s, hsp,
    putExternal_run, record_run]
  let m : State := {s with
    external := writeExternal s.external token.val (aslot fromAddr spender)
      (assetAllowance s token fromAddr spender - amount)
    trace := s.trace ++ [.allowanceSpent token fromAddr spender amount]}
  have hbal : assetBalance m token fromAddr = assetBalance s token fromAddr :=
    balance_after_allowance_write _ _ _ _ _ _
  have hm := safeTransfer_run env token fromAddr toAddr amount m hc ht he
    (by rw [hbal]; exact ho) ha (by rw [hbal]; exact hb)
  simpa only [m, List.append_assoc, List.cons_append, List.nil_append] using hm

theorem safeTransfer_success (env : Environment) (token fromAddr toAddr : Address)
    (amount : Nat) (s t : State) (ha : amount < wordLimit)
    (ho : assetBalance s token fromAddr < wordLimit)
    (h : safeTransfer env token fromAddr toAddr amount s = .ok ((),t)) :
    (env.hasCode token && env.isToken token && env.tokenAccepts token) = true ∧
    (token != s.config.self) = true ∧ (fromAddr != 0 && toAddr != 0) = true ∧
    amount ≤ assetBalance s token fromAddr ∧
    t = {s with
      external := tokenWordTransfer s.external token fromAddr toAddr amount
      trace := s.trace ++ [.assetTransfer token fromAddr toAddr amount]} := by
  by_cases hc : (env.hasCode token && env.isToken token && env.tokenAccepts token) = true
  · by_cases ht : (token != s.config.self) = true
    · by_cases he : (fromAddr != 0 && toAddr != 0) = true
      · by_cases hb : amount ≤ assetBalance s token fromAddr
        · rw [safeTransfer_run _ _ _ _ _ _ hc ht he ho ha hb] at h
          exact ⟨hc,ht,he,hb,(congrArg Prod.snd (Except.ok.inj h)).symm⟩
        · simp [safeTransfer, get, getThe, MonadStateOf.get, StateT.get,
            Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
            guard, hc, ht, he, checkedSub_run _ _ ho ha s, hb,
            MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift] at h
      · simp [safeTransfer, get, getThe, MonadStateOf.get, StateT.get,
          Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
          guard, hc, ht, he, MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift] at h
    · simp [safeTransfer, get, getThe, MonadStateOf.get, StateT.get,
        Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
        guard, hc, ht, MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift] at h
  · simp [safeTransfer, get, getThe, MonadStateOf.get, StateT.get,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      guard, hc, MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift] at h

theorem setStatus_run (id : Nat) (status : RequestStatus) (s : State) :
    setStatus id status s = .ok ((), {s with requests := fun j =>
      if j == id then {s.requests id with requestStatus := status} else s.requests j}) := rfl

theorem setStatus_payload (id : Nat) (status : RequestStatus) (s t : State)
    (h : setStatus id status s = .ok ((),t)) :
    (∀ j, Payload (s.requests j) (t.requests j)) ∧
    (t.requests id).requestStatus = status ∧
    (∀ j, j ≠ id → t.requests j = s.requests j) := by
  rw [setStatus_run] at h
  have ht := (congrArg Prod.snd (Except.ok.inj h)).symm
  dsimp only at ht
  rw [ht]
  constructor
  · intro j
    by_cases hj : j = id
    · subst j; simp [Payload]
    · simp [hj,Payload]
  · constructor
    · simp
    · intro j hj; simp [hj]

theorem debitSubscription_run (asset : Address) (amount : Nat) (s : State)
    (ho : s.subscriptionAssets asset < wordLimit) (ha : amount < wordLimit)
    (hb : amount ≤ s.subscriptionAssets asset) :
    debitSubscription asset amount s = .ok ((), {s with subscriptionAssets := fun a =>
      if a == asset then (s.subscriptionAssets asset - amount) else s.subscriptionAssets a}) := by
  simp only [debitSubscription, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
    checkedSub_run _ _ ho ha s, hb, ↓reduceIte]
  rfl

theorem decrementCount_run (asset : Address) (s : State)
    (ho : s.pendingRequestsCount asset < wordLimit) (hb : 1 ≤ s.pendingRequestsCount asset) :
    decrementCount asset s = .ok ((), {s with pendingRequestsCount := fun a =>
      if a == asset then s.pendingRequestsCount asset - 1 else s.pendingRequestsCount a}) := by
  simp only [decrementCount, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
    checkedSub_run _ _ ho (by norm_num [wordLimit] : 1 < wordLimit) s, hb, ↓reduceIte]
  rfl

-- Initial lookups select a real handler or an exact no-op; this equation does
-- not replace or summarize the selected handler's token/share behavior.
theorem approveOne_dispatch (env : Environment) (asset : Address) (price id : Nat) (s : State) :
    approveOne env asset price id s =
      if !_checkValidRequest (s.requests id) then .ok ((),s)
      else if (s.requests id).asset != asset then .ok ((),s)
      else if env.now > (s.requests id).expiryAt then
        if (s.requests id).requestType == .subscription then
          _rejectSubscriptionRequest env id (s.requests id) s
        else _rejectRedeemRequest id (s.requests id) s
      else if (s.requests id).requestType == .subscription then
        _approveSubscriptionRequest env id (s.requests id) price s
      else _approveRedeemRequest env id (s.requests id) price s := by
  simp only [approveOne, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> split <;> rfl

theorem rejectOne_dispatch (env : Environment) (asset : Address) (id : Nat) (s : State) :
    rejectOne env asset id s =
      if !_checkValidRequest (s.requests id) then .ok ((),s)
      else if (s.requests id).asset != asset then .ok ((),s)
      else if (s.requests id).requestType == .subscription then
        _rejectSubscriptionRequest env id (s.requests id) s
      else _rejectRedeemRequest id (s.requests id) s := by
  simp only [rejectOne, get, getThe, MonadStateOf.get, StateT.get,
    Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> rfl

#print axioms setStatus_payload
#print axioms debitSubscription_run
#print axioms decrementCount_run
#print axioms approveOne_dispatch
#print axioms rejectOne_dispatch
#print axioms safeTransfer_success
#print axioms safeTransferFrom_finite_run
#print axioms safeTransferFrom_infinite_run
#print axioms safeTransfer_run
#print axioms assetsToShares_success
#print axioms sharesToAssets_success
#print axioms checkedSub_success
#print axioms checkedMul_success
#print axioms mulDiv_success
end Benchmark.Cases.KPK.SharesSettlementAccounting
