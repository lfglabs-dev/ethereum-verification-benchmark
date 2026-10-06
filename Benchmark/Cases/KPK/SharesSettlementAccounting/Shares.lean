import Benchmark.Cases.KPK.SharesSettlementAccounting.Accounting

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity Verity.Stdlib.Math
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

@[simp] theorem readSlot_eq_storage (s : ContractState) (slotIdx : Nat) :
    s.readSlot slotIdx = s.storage slotIdx := rfl
@[simp] theorem readAddrSlot_eq_storageAddr (s : ContractState) (slotIdx : Nat) :
    s.readAddrSlot slotIdx = s.storageAddr slotIdx := rfl
@[simp] theorem readMap_eq_storageMap (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.readMap slotIdx k = s.storageMap slotIdx k := rfl
@[simp] theorem readMapUint_eq_storageMapUint (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.readMapUint slotIdx k = s.storageMapUint slotIdx k := rfl
@[simp] theorem readMap2_eq_storageMap2 (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.readMap2 slotIdx k1 k2 = s.storageMap2 slotIdx k1 k2 := rfl
@[simp] theorem readTransient_eq_transientStorage (s : ContractState) (slotIdx : Nat) :
    s.readTransient slotIdx = s.transientStorage slotIdx := rfl
@[simp] theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl
@[simp] theorem storageAddr_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageAddr =
      s.storageAddr := rfl
@[simp] theorem storageMap_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      s.storageMap := rfl
@[simp] theorem storageMapUint_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapUint =
      s.storageMapUint := rfl
@[simp] theorem storageMap2_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap2 =
      s.storageMap2 := rfl
@[simp] theorem transientStorage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).transientStorage =
      s.transientStorage := rfl
@[simp] theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] theorem storageMap_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) :
    (s.writeSlot slotIdx value).storageMap = s.storageMap := by
  funext mapSlot mapKey; simp [ContractState.storageMap, ContractState.writeSlot]
@[simp] theorem storageMap2_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) :
    (s.writeSlot slotIdx value).storageMap2 = s.storageMap2 := by
  funext mapSlot k1 k2; simp [ContractState.storageMap2, ContractState.writeSlot]
@[simp] theorem storageMapUint_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) :
    (s.writeSlot slotIdx value).storageMapUint = s.storageMapUint := by
  funext mapSlot k; simp [ContractState.storageMapUint, ContractState.writeSlot]
@[simp] theorem storageAddr_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) :
    (s.writeSlot slotIdx value).storageAddr = s.storageAddr := by
  funext addrSlot; simp [ContractState.storageAddr, ContractState.writeSlot]
@[simp] theorem transientStorage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) :
    (s.writeSlot slotIdx value).transientStorage = s.transientStorage := by
  funext tSlot; simp [ContractState.transientStorage, ContractState.writeSlot]
@[simp] theorem storageMap_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256)
    (slotIdx' : Nat) (key' : Address) :
    (s.writeMap slotIdx key value).storageMap slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMap slotIdx' key' := by
  simp [ContractState.storageMap, ContractState.writeMap]
@[simp] theorem storage_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slotIdx key value).storage = s.storage := by
  funext wordSlot; simp [ContractState.storage, ContractState.writeMap]
@[simp] theorem storageMap2_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slotIdx key value).storageMap2 = s.storageMap2 := by
  funext mapSlot k1 k2; simp [ContractState.storageMap2, ContractState.writeMap]
@[simp] theorem storageMapUint_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slotIdx key value).storageMapUint = s.storageMapUint := by
  funext mapSlot k; simp [ContractState.storageMapUint, ContractState.writeMap]
@[simp] theorem storageAddr_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slotIdx key value).storageAddr = s.storageAddr := by
  funext addrSlot; simp [ContractState.storageAddr, ContractState.writeMap]
@[simp] theorem transientStorage_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slotIdx key value).transientStorage = s.transientStorage := by
  funext tSlot; simp [ContractState.transientStorage, ContractState.writeMap]
@[simp] theorem memory_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256) :
    (s.writeMap slotIdx key value).memory = s.memory := rfl

def shareWrite (s : State) (a : Address) (v : Uint256) : State :=
  {s with caller := {s.caller.writeMap balanceSlot.slot a v with
    knownAddresses := fun slot => if slot == balanceSlot.slot then
      (s.caller.knownAddresses slot).insert a else s.caller.knownAddresses slot}}
def supplyWrite (s : State) (v : Uint256) : State :=
  {s with caller := s.caller.writeSlot supplySlot.slot v}

theorem shareWrite_balance (s : State) (a x : Address) (v : Uint256) :
    shareBalance (shareWrite s a v) x = if x = a then v.val else shareBalance s x := by
  simp [shareBalance,shareWrite,balanceSlot]

theorem shareWrite_supply (s : State) (a : Address) (v : Uint256) :
    totalSupply (shareWrite s a v) = totalSupply s := by
  simp [totalSupply,shareWrite]

theorem supplyWrite_balance (s : State) (v : Uint256) (x : Address) :
    shareBalance (supplyWrite s v) x = shareBalance s x := by
  simp [shareBalance,supplyWrite]

theorem supplyWrite_supply (s : State) (v : Uint256) :
    totalSupply (supplyWrite s v) = v.val := by
  simp [totalSupply,supplyWrite]

theorem shareBalance_bounded (s : State) (a : Address) : shareBalance s a < wordLimit :=
  (s.caller.readMap balanceSlot.slot a).isLt

theorem totalSupply_bounded (s : State) : totalSupply s < wordLimit :=
  (s.caller.readSlot supplySlot.slot).isLt

theorem ledger_balance_le_supply (s : State) (hl : LedgerCoherent s) (x : Address) :
    shareBalance s x ≤ totalSupply s := by
  obtain ⟨accounts,hn,hs,he,hz⟩ := hl
  by_cases hx : x ∈ accounts
  · have hh := support_member_bound accounts (shareBalance s) x hx; omega
  · rw [hs x hx]; omega

theorem mint_run (s : State) (toAddr : Address) (amount : Nat)
    (hto : toAddr ≠ 0) (ha : amount < wordLimit)
    (hs : totalSupply s + amount < wordLimit) :
    _mint toAddr amount s = .ok ((),
      { (shareWrite (supplyWrite s ((s.caller.readSlot supplySlot.slot) + word amount))
          toAddr ((s.caller.readMap balanceSlot.slot toAddr) + word amount)) with
        trace := s.trace ++ [.mint toAddr amount]}) := by
  have hmax : ¬ MAX_UINT256 < totalSupply s + amount := by
    change ¬wordLimit-1 < totalSupply s + amount; omega
  simp only [_mint,_update,guard,show (toAddr != 0) = true by simpa using hto,
    show (toAddr == 0) = false by simpa using hto,beq_self_eq_true,
    liftCaller,getStorage,setStorage,getMapping,setMapping,
    addPanic,requireSomeUint,safeAdd,word_val amount ha,
    show ¬MAX_UINT256 < (s.caller.readSlot supplySlot.slot).val + amount from hmax,
    Bind.bind,StateT.bind,Except.bind,Pure.pure,StateT.pure,Except.pure,
    Verity.bind,Verity.pure,Verity.require,↓reduceIte,record_run]
  rfl

theorem transfer_run (s : State) (fromAddr toAddr : Address) (amount : Nat)
    (hf : fromAddr ≠ 0) (ht : toAddr ≠ 0)
    (ha : amount ≤ shareBalance s fromAddr) :
    _transfer fromAddr toAddr amount s = .ok ((),
      { (shareWrite (shareWrite s fromAddr (word (shareBalance s fromAddr - amount)))
          toAddr (((shareWrite s fromAddr (word (shareBalance s fromAddr - amount))).caller.readMap balanceSlot.slot toAddr) + word amount)) with
        trace := s.trace ++ [.shareTransfer fromAddr toAddr amount]}) := by
  simp only [_transfer,_update,guard,show (fromAddr != 0) = true by simpa using hf,
    show (toAddr != 0) = true by simpa using ht,
    show (fromAddr == 0) = false by simpa using hf,
    show (toAddr == 0) = false by simpa using ht,
    liftCaller,getStorage,setStorage,getMapping,setMapping,
    show ((s.caller.readMap balanceSlot.slot fromAddr).val >= amount) = true by simpa [shareBalance,ContractState.readMap] using ha,
    Bind.bind,StateT.bind,Except.bind,Pure.pure,StateT.pure,Except.pure,
    Bool.false_eq_true,↓reduceIte,record_run]
  rfl

theorem burn_run (s : State) (fromAddr : Address) (amount : Nat)
    (hf : fromAddr ≠ 0) (ha : amount ≤ shareBalance s fromAddr) :
    _burn fromAddr amount s = .ok ((),
      { (supplyWrite (shareWrite s fromAddr (word (shareBalance s fromAddr - amount)))
          ((s.caller.readSlot supplySlot.slot) - word amount)) with
        trace := s.trace ++ [.burn fromAddr amount]}) := by
  simp only [_burn,_update,guard,show (fromAddr != 0) = true by simpa using hf,
    show (fromAddr == 0) = false by simpa using hf,beq_self_eq_true,
    liftCaller,getStorage,setStorage,getMapping,setMapping,
    show ((s.caller.readMap balanceSlot.slot fromAddr).val >= amount) = true by simpa [shareBalance,ContractState.readMap] using ha,
    Bind.bind,StateT.bind,Except.bind,Pure.pure,StateT.pure,Except.pure,
    Bool.false_eq_true,↓reduceIte,record_run]
  rfl

theorem mint_success (s t : State) (toAddr : Address) (amount : Nat)
    (ha : amount < wordLimit) (h : _mint toAddr amount s = .ok ((),t)) :
    toAddr ≠ 0 ∧ totalSupply s + amount < wordLimit ∧
    t = { (shareWrite (supplyWrite s ((s.caller.readSlot supplySlot.slot) + word amount))
      toAddr ((s.caller.readMap balanceSlot.slot toAddr) + word amount)) with
      trace := s.trace ++ [.mint toAddr amount]} := by
  by_cases ht : toAddr = 0
  · subst toAddr
    simp [_mint,guard,Bind.bind,StateT.bind,Except.bind,
      MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h
  · by_cases hs : totalSupply s + amount < wordLimit
    · rw [mint_run s toAddr amount ht ha hs] at h
      exact ⟨ht,hs,(congrArg Prod.snd (Except.ok.inj h)).symm⟩
    · have hm : MAX_UINT256 < totalSupply s + amount := by
        change wordLimit-1 < totalSupply s + amount; omega
      change MAX_UINT256 < (s.caller.storage supplySlot.slot).val + amount at hm
      simp [_mint,_update,guard,ht,liftCaller,getStorage,addPanic,requireSomeUint,safeAdd,
        totalSupply,word_val amount ha,hm,Bind.bind,StateT.bind,Except.bind,
        Pure.pure,StateT.pure,Except.pure,Verity.bind,Verity.pure,Verity.require,
        MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h

theorem transfer_success (s t : State) (fromAddr toAddr : Address) (amount : Nat)
    (h : _transfer fromAddr toAddr amount s = .ok ((),t)) :
    fromAddr ≠ 0 ∧ toAddr ≠ 0 ∧ amount ≤ shareBalance s fromAddr ∧
    t = { (shareWrite (shareWrite s fromAddr (word (shareBalance s fromAddr - amount)))
      toAddr (((shareWrite s fromAddr (word (shareBalance s fromAddr - amount))).caller.readMap balanceSlot.slot toAddr) + word amount)) with
      trace := s.trace ++ [.shareTransfer fromAddr toAddr amount]} := by
  by_cases hf : fromAddr = 0
  · subst fromAddr
    simp [_transfer,guard,Bind.bind,StateT.bind,Except.bind,
      MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h
  · by_cases ht : toAddr = 0
    · subst toAddr
      simp [_transfer,guard,hf,Bind.bind,StateT.bind,Except.bind,
        Pure.pure,StateT.pure,Except.pure,
        MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h
    · by_cases hb : amount ≤ shareBalance s fromAddr
      · rw [transfer_run s fromAddr toAddr amount hf ht hb] at h
        exact ⟨hf,ht,hb,(congrArg Prod.snd (Except.ok.inj h)).symm⟩
      · change ¬amount ≤ (s.caller.storageMap balanceSlot.slot fromAddr).val at hb
        simp [_transfer,_update,guard,hf,ht,liftCaller,getMapping,
          shareBalance,ContractState.readMap,hb,Bind.bind,StateT.bind,Except.bind,
          Pure.pure,StateT.pure,Except.pure,
          MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h

theorem burn_success (s t : State) (fromAddr : Address) (amount : Nat)
    (h : _burn fromAddr amount s = .ok ((),t)) :
    fromAddr ≠ 0 ∧ amount ≤ shareBalance s fromAddr ∧
    t = { (supplyWrite (shareWrite s fromAddr (word (shareBalance s fromAddr - amount)))
      ((s.caller.readSlot supplySlot.slot) - word amount)) with
      trace := s.trace ++ [.burn fromAddr amount]} := by
  by_cases hf : fromAddr = 0
  · subst fromAddr
    simp [_burn,guard,Bind.bind,StateT.bind,Except.bind,
      MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h
  · by_cases hb : amount ≤ shareBalance s fromAddr
    · rw [burn_run s fromAddr amount hf hb] at h
      exact ⟨hf,hb,(congrArg Prod.snd (Except.ok.inj h)).symm⟩
    · change ¬amount ≤ (s.caller.storageMap balanceSlot.slot fromAddr).val at hb
      simp [_burn,_update,guard,hf,liftCaller,getMapping,
        shareBalance,ContractState.readMap,hb,Bind.bind,StateT.bind,Except.bind,
        Pure.pure,StateT.pure,Except.pure,
        MonadExcept.throw,throwThe,MonadExceptOf.throw,StateT.lift] at h

theorem shareWrite_frame (s : State) (a : Address) (v : Uint256) (asset : Address) :
    CallerFrame s (shareWrite s a v) asset := by
  simp [CallerFrame,shareWrite]
  constructor <;> intros <;> contradiction

theorem supplyWrite_frame (s : State) (v : Uint256) (asset : Address) :
    CallerFrame s (supplyWrite s v) asset := by
  simp [CallerFrame,supplyWrite]
  intros; contradiction

theorem sum_change_balance (accounts : List Address) (f g : Address → Nat)
    (a : Address) (debit credit : Nat)
    (h : ∀ x, g x + (if x = a then debit else 0) = f x + (if x = a then credit else 0)) :
    (accounts.map g).sum + (accounts.map fun x => if x = a then debit else 0).sum =
      (accounts.map f).sum + (accounts.map fun x => if x = a then credit else 0).sum := by
  induction accounts with
  | nil => simp
  | cons x xs ih =>
    have hh := h x
    simp only [List.map_cons,List.sum_cons]; omega

theorem support_change_preserved (accounts : List Address) (f g : Address → Nat)
    (hn : accounts.Nodup) (hs : ∀ x, x ∉ accounts → f x = 0)
    (a : Address) (debit credit : Nat)
    (h : ∀ x, g x + (if x = a then debit else 0) = f x + (if x = a then credit else 0)) :
    ∃ next : List Address, next.Nodup ∧ (∀ x, x ∉ next → g x = 0) ∧
      (next.map g).sum + debit = (accounts.map f).sum + credit := by
  obtain ⟨hn',hs',he⟩ := support_insert accounts f hn hs a
  refine ⟨accounts.insert a,hn',?_,?_⟩
  · intro x hx
    have hxa : x ≠ a := by intro he; subst x; exact hx (by simp)
    have hh := h x
    simp only [if_neg hxa,Nat.add_zero] at hh
    rw [hh]; exact hs' x hx
  · have hh := sum_change_balance (accounts.insert a) f g a debit credit h
    rw [sum_indicator _ _ _ hn',sum_indicator _ _ _ hn',
      if_pos (show a ∈ accounts.insert a by simp),he] at hh
    simpa only [if_pos (show a ∈ accounts.insert a by simp)] using hh

theorem mint_effects (s t : State) (toAddr : Address) (amount : Nat)
    (hl : LedgerCoherent s) (ha : amount < wordLimit)
    (h : _mint toAddr amount s = .ok ((),t)) :
    totalSupply t = totalSupply s + amount ∧
    (∀ x, shareBalance t x = shareBalance s x + if x = toAddr then amount else 0) ∧
    LedgerCoherent t := by
  obtain ⟨hto,hs,hnxt⟩ := mint_success s t toAddr amount ha h
  have hsupply : ((s.caller.readSlot supplySlot.slot) + word amount).val = totalSupply s + amount := by
    have hh := Verity.Core.Uint256.add_eq_of_lt (a := s.caller.readSlot supplySlot.slot) (b := word amount)
      (by simpa only [word_val amount ha,word_modulus,totalSupply,shareBalance] using hs)
    simpa only [word_val amount ha,totalSupply,shareBalance] using hh
  have hcredit : shareBalance s toAddr + amount < wordLimit := by
    have hb := ledger_balance_le_supply s hl toAddr; omega
  have hrecipient : ((s.caller.readMap balanceSlot.slot toAddr) + word amount).val = shareBalance s toAddr + amount := by
    have hh := Verity.Core.Uint256.add_eq_of_lt (a := s.caller.readMap balanceSlot.slot toAddr) (b := word amount)
      (by simpa only [word_val amount ha,word_modulus,totalSupply,shareBalance] using hcredit)
    simpa only [word_val amount ha,totalSupply,shareBalance] using hh
  have hts : totalSupply t = totalSupply s + amount := by
    rw [hnxt]
    change totalSupply (shareWrite (supplyWrite s _) toAddr _) = _
    rw [shareWrite_supply,supplyWrite_supply,hsupply]
  have hbal : ∀ x, shareBalance t x = shareBalance s x + if x = toAddr then amount else 0 := by
    intro x
    rw [hnxt]
    change shareBalance (shareWrite (supplyWrite s _) toAddr _) x = _
    rw [shareWrite_balance,supplyWrite_balance,hrecipient]
    split_ifs with hx
    · subst x; rfl
    · omega
  refine ⟨hts,hbal,?_⟩
  obtain ⟨accounts,hn,hzero,hsum,h0⟩ := hl
  have hdelta (x : Address) : shareBalance t x + (if x = toAddr then 0 else 0) =
      shareBalance s x + (if x = toAddr then amount else 0) := by simp only [ite_self,Nat.add_zero,hbal]
  obtain ⟨next,hn',hzero',hsum'⟩ := support_change_preserved accounts (shareBalance s) (shareBalance t)
    hn hzero toAddr 0 amount hdelta
  refine ⟨next,hn',hzero',?_,?_⟩
  · rw [hts]; omega
  · rw [hbal,if_neg (Ne.symm hto),h0]

theorem burn_effects (s t : State) (fromAddr : Address) (amount : Nat)
    (hl : LedgerCoherent s) (h : _burn fromAddr amount s = .ok ((),t)) :
    amount ≤ totalSupply s ∧ totalSupply t = totalSupply s - amount ∧
    (∀ x, shareBalance t x = if x = fromAddr then shareBalance s x - amount else shareBalance s x) ∧
    LedgerCoherent t := by
  obtain ⟨hf,ha,hnxt⟩ := burn_success s t fromAddr amount h
  have hle := ledger_balance_le_supply s hl fromAddr
  have hat : amount ≤ totalSupply s := by omega
  have haB : amount < wordLimit := lt_of_le_of_lt ha (shareBalance_bounded s fromAddr)
  have hsupply : ((s.caller.readSlot supplySlot.slot) - word amount).val = totalSupply s - amount := by
    have hh := Verity.Core.Uint256.sub_eq_of_le (a := s.caller.readSlot supplySlot.slot) (b := word amount)
      (by simpa only [word_val amount haB,totalSupply] using hat)
    simpa only [word_val amount haB,totalSupply] using hh
  have hword : (word (shareBalance s fromAddr - amount)).val = shareBalance s fromAddr - amount :=
    word_val _ (lt_of_le_of_lt (Nat.sub_le _ _) (shareBalance_bounded s fromAddr))
  have hts : totalSupply t = totalSupply s - amount := by
    rw [hnxt]
    change totalSupply (supplyWrite (shareWrite s fromAddr _) _) = _
    rw [supplyWrite_supply,hsupply]
  have hbal : ∀ x, shareBalance t x = if x = fromAddr then shareBalance s x - amount else shareBalance s x := by
    intro x
    rw [hnxt]
    change shareBalance (supplyWrite (shareWrite s fromAddr _) _) x = _
    rw [supplyWrite_balance,shareWrite_balance,hword]
    split_ifs with hx
    · subst x; rfl
    · rfl
  refine ⟨hat,hts,hbal,?_⟩
  obtain ⟨accounts,hn,hzero,hsum,h0⟩ := hl
  have hdelta (x : Address) : shareBalance t x + (if x = fromAddr then amount else 0) =
      shareBalance s x + (if x = fromAddr then 0 else 0) := by
    rw [hbal]
    by_cases hx : x = fromAddr
    · subst x; simp only [if_pos rfl,if_true]; omega
    · simp [hx]
  obtain ⟨next,hn',hzero',hsum'⟩ := support_change_preserved accounts (shareBalance s) (shareBalance t)
    hn hzero fromAddr amount 0 hdelta
  refine ⟨next,hn',hzero',?_,?_⟩
  · rw [hts]; omega
  · rw [hbal,if_neg (Ne.symm hf)]; exact h0

theorem transfer_effects (s t : State) (fromAddr toAddr : Address) (amount : Nat)
    (hl : LedgerCoherent s) (h : _transfer fromAddr toAddr amount s = .ok ((),t)) :
    totalSupply t = totalSupply s ∧
    (∀ x, (shareBalance t x : Int) - shareBalance s x =
      indicator x toAddr amount - indicator x fromAddr amount) ∧ LedgerCoherent t := by
  obtain ⟨hf,ht,ha,hnxt⟩ := transfer_success s t fromAddr toAddr amount h
  have haB : amount < wordLimit := lt_of_le_of_lt ha (shareBalance_bounded s fromAddr)
  let debited := shareWrite s fromAddr (word (shareBalance s fromAddr - amount))
  have hword : (word (shareBalance s fromAddr - amount)).val = shareBalance s fromAddr - amount :=
    word_val _ (lt_of_le_of_lt (Nat.sub_le _ _) (shareBalance_bounded s fromAddr))
  have hd (x : Address) : shareBalance debited x =
      if x = fromAddr then shareBalance s fromAddr - amount else shareBalance s x := by
    exact (shareWrite_balance s fromAddr x _).trans (by rw [hword])
  have hcredit : shareBalance debited toAddr + amount < wordLimit := by
    rw [hd]
    by_cases he : toAddr = fromAddr
    · rw [if_pos he]
      have hh := shareBalance_bounded s fromAddr; omega
    · rw [if_neg he]
      obtain ⟨accounts,hn,hs,heq,hzero⟩ := hl
      have hp := support_pair_bound accounts (shareBalance s) hn hs toAddr fromAddr he
      have hb := totalSupply_bounded s
      omega
  have hrecipient : ((debited.caller.readMap balanceSlot.slot toAddr) + word amount).val =
      shareBalance debited toAddr + amount := by
    have hh := Verity.Core.Uint256.add_eq_of_lt (a := debited.caller.readMap balanceSlot.slot toAddr) (b := word amount)
      (by simpa only [word_val amount haB,word_modulus,shareBalance] using hcredit)
    simpa only [word_val amount haB,shareBalance] using hh
  have hts : totalSupply t = totalSupply s := by
    rw [hnxt]
    change totalSupply (shareWrite debited toAddr _) = _
    rw [shareWrite_supply,shareWrite_supply]
  have hbal (x : Address) : shareBalance t x =
      if x = toAddr then (if toAddr = fromAddr then shareBalance s fromAddr - amount else shareBalance s toAddr) + amount
      else if x = fromAddr then shareBalance s fromAddr - amount else shareBalance s x := by
    rw [hnxt]
    change shareBalance (shareWrite debited toAddr _) x = _
    rw [shareWrite_balance,hrecipient,hd,hd]
  have heffect (x : Address) : (shareBalance t x : Int) - shareBalance s x =
      indicator x toAddr amount - indicator x fromAddr amount := by
    rw [hbal]
    by_cases hxt : x = toAddr
    · subst x
      by_cases he : toAddr = fromAddr
      · subst toAddr; simp [indicator]; omega
      · simp [he,indicator]
    · by_cases hxf : x = fromAddr
      · subst x; simp [hxt,indicator]; omega
      · simp [hxt,hxf,indicator]
  refine ⟨hts,heffect,?_⟩
  obtain ⟨accounts,hn,hs,heq,hzero⟩ := hl
  have hdelta (x : Address) : shareBalance t x + (if x = fromAddr then amount else 0) =
      shareBalance s x + (if x = toAddr then amount else 0) := by
    have hh := heffect x
    dsimp only [indicator] at hh
    have hifrom : (if x = fromAddr then (amount : Int) else 0) =
        ((if x = fromAddr then amount else 0 : Nat) : Int) := by split <;> rfl
    have hito : (if x = toAddr then (amount : Int) else 0) =
        ((if x = toAddr then amount else 0 : Nat) : Int) := by split <;> rfl
    rw [hifrom,hito] at hh; omega
  obtain ⟨next,hn',hs',heq'⟩ := support_transfer_preserved accounts (shareBalance s) (shareBalance t)
    hn hs fromAddr toAddr amount hdelta
  refine ⟨next,hn',hs',by rw [heq',heq,hts],?_⟩
  rw [hbal,if_neg (Ne.symm ht),if_neg (Ne.symm hf)]; exact hzero

theorem callerFrame_trans (s m t : State) (asset : Address)
    (h1 : CallerFrame s m asset) (h2 : CallerFrame m t asset) : CallerFrame s t asset := by
  rcases h1 with ⟨h1price,h1storage,h1map,h1map2,h1mapUint,h1addr,h1array,h1transient,h1memory,h1events,h1sender,h1self,h1origin,h1value,h1balance,h1time,h1number,h1chain,h1blob,h1size,h1calldata,h1known⟩
  rcases h2 with ⟨h2price,h2storage,h2map,h2map2,h2mapUint,h2addr,h2array,h2transient,h2memory,h2events,h2sender,h2self,h2origin,h2value,h2balance,h2time,h2number,h2chain,h2blob,h2size,h2calldata,h2known⟩
  exact ⟨by intro a ha; exact (h2price a ha).trans (h1price a ha),
    by intro slot hs; exact (h2storage slot hs).trans (h1storage slot hs),
    by intro slot a hs; exact (h2map slot a hs).trans (h1map slot a hs),
    h2map2.trans h1map2,
    h2mapUint.trans h1mapUint,
    h2addr.trans h1addr,
    h2array.trans h1array,
    h2transient.trans h1transient,
    h2memory.trans h1memory,
    h2events.trans h1events,
    h2sender.trans h1sender,
    h2self.trans h1self,
    h2origin.trans h1origin,
    h2value.trans h1value,
    h2balance.trans h1balance,
    h2time.trans h1time,
    h2number.trans h1number,
    h2chain.trans h1chain,
    h2blob.trans h1blob,
    h2size.trans h1size,
    h2calldata.trans h1calldata,
    by intro slot hs; exact (h2known slot hs).trans (h1known slot hs)⟩

theorem mint_frame (s t : State) (toAddr : Address) (amount : Nat) (asset : Address)
    (ha : amount < wordLimit) (h : _mint toAddr amount s = .ok ((),t)) : CallerFrame s t asset := by
  obtain ⟨_,_,ht⟩ := mint_success s t toAddr amount ha h
  rw [ht]
  change CallerFrame s (shareWrite (supplyWrite s _) toAddr _) asset
  exact callerFrame_trans _ _ _ _ (supplyWrite_frame _ _ _) (shareWrite_frame _ _ _ _)

theorem burn_frame (s t : State) (fromAddr : Address) (amount : Nat) (asset : Address)
    (h : _burn fromAddr amount s = .ok ((),t)) : CallerFrame s t asset := by
  obtain ⟨_,_,ht⟩ := burn_success s t fromAddr amount h
  rw [ht]
  change CallerFrame s (supplyWrite (shareWrite s fromAddr _) _) asset
  exact callerFrame_trans _ _ _ _ (shareWrite_frame _ _ _ _) (supplyWrite_frame _ _ _)

theorem transfer_frame (s t : State) (fromAddr toAddr : Address) (amount : Nat) (asset : Address)
    (h : _transfer fromAddr toAddr amount s = .ok ((),t)) : CallerFrame s t asset := by
  obtain ⟨_,_,_,ht⟩ := transfer_success s t fromAddr toAddr amount h
  rw [ht]
  change CallerFrame s (shareWrite (shareWrite s fromAddr _) toAddr _) asset
  exact callerFrame_trans _ _ _ _ (shareWrite_frame _ _ _ _) (shareWrite_frame _ _ _ _)

theorem mint_integer_effect (s t : State) (toAddr : Address) (amount : Nat)
    (hl : LedgerCoherent s) (ha : amount < wordLimit) (h : _mint toAddr amount s = .ok ((),t)) :
    (totalSupply t : Int) - totalSupply s = amount ∧
    (∀ x, (shareBalance t x : Int) - shareBalance s x = indicator x toAddr amount) := by
  obtain ⟨hs,hb,_⟩ := mint_effects s t toAddr amount hl ha h
  constructor
  · rw [hs]; omega
  · intro x
    rw [hb]
    by_cases hx : x = toAddr <;> simp [hx,indicator]

theorem burn_integer_effect (s t : State) (fromAddr : Address) (amount : Nat)
    (hl : LedgerCoherent s) (h : _burn fromAddr amount s = .ok ((),t)) :
    (totalSupply t : Int) - totalSupply s = -(amount : Int) ∧
    (∀ x, (shareBalance t x : Int) - shareBalance s x = -indicator x fromAddr amount) := by
  obtain ⟨ha,hs,hb,_⟩ := burn_effects s t fromAddr amount hl h
  obtain ⟨_,haB,_⟩ := burn_success s t fromAddr amount h
  constructor
  · rw [hs]; omega
  · intro x
    rw [hb]
    by_cases hx : x = fromAddr
    · subst x; simp only [if_pos rfl,indicator,if_true]; omega
    · simp [hx,indicator]

#print axioms callerFrame_trans
#print axioms mint_frame
#print axioms burn_frame
#print axioms transfer_frame
#print axioms mint_integer_effect
#print axioms burn_integer_effect
#print axioms transfer_effects
#print axioms sum_change_balance
#print axioms support_change_preserved
#print axioms mint_effects
#print axioms burn_effects
#print axioms mint_success
#print axioms transfer_success
#print axioms burn_success
#print axioms shareWrite_frame
#print axioms supplyWrite_frame
#print axioms mint_run
#print axioms transfer_run
#print axioms burn_run
#print axioms ledger_balance_le_supply
end Benchmark.Cases.KPK.SharesSettlementAccounting
