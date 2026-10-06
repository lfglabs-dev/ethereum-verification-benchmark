import Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.DamnVulnerableDeFi.SideEntrance

open Verity
open Verity.EVM.Uint256

@[simp] private theorem readSlot_eq_storage (s : ContractState) (slotIdx : Nat) :
    s.readSlot slotIdx = s.storage slotIdx := rfl
@[simp] private theorem readAddrSlot_eq_storageAddr (s : ContractState) (slotIdx : Nat) :
    s.readAddrSlot slotIdx = s.storageAddr slotIdx := rfl
@[simp] private theorem readMap_eq_storageMap (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.readMap slotIdx k = s.storageMap slotIdx k := rfl
@[simp] private theorem readMapUint_eq_storageMapUint (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.readMapUint slotIdx k = s.storageMapUint slotIdx k := rfl
@[simp] private theorem readMap2_eq_storageMap2 (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.readMap2 slotIdx k1 k2 = s.storageMap2 slotIdx k1 k2 := rfl
@[simp] private theorem readTransient_eq_transientStorage (s : ContractState) (slotIdx : Nat) :
    s.readTransient slotIdx = s.transientStorage slotIdx := rfl
@[simp] private theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl
@[simp] private theorem storageAddr_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageAddr =
      s.storageAddr := rfl
@[simp] private theorem storageMap_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      s.storageMap := rfl
@[simp] private theorem storageMapUint_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapUint =
      s.storageMapUint := rfl
@[simp] private theorem storageMap2_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap2 =
      s.storageMap2 := rfl
@[simp] private theorem address_ofNat_storageWords_addr (s : ContractState) (slotIdx : Nat) :
    Verity.Core.Address.ofNat (s.storageWords (.addr slotIdx)).val = s.storageAddr slotIdx := rfl


private theorem deposit_slot_writes
    (amount : Uint256) (s : ContractState) :
    let s' := ((SideEntrance.deposit amount).run s).snd
    s'.storage 0 = add (s.storage 0) amount ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount := by
  constructor
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]

private theorem flashLoanViaDeposit_slot_writes
    (amount : Uint256) (s : ContractState)
    (hBorrow : amount <= s.storage 0) :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]

private theorem withdraw_slot_write
    (s : ContractState)
    (hCredit : s.storageMap 2 s.sender <= s.storage 0) :
    let s' := ((SideEntrance.withdraw).run s).snd
    s'.storage 0 = sub (s.storage 0) (s.storageMap 2 s.sender) := by
  have hCredit' : (s.storageMap 2 s.sender <= s.storage 0) = true := by simp [hCredit]
  simp [SideEntrance.withdraw, SideEntrance.poolBalance, SideEntrance.totalCredits,
    SideEntrance.creditOf, hCredit', getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, msgSender]

theorem deposit_sets_pool_balance
    (amount : Uint256) (s : ContractState) :
    let s' := ((SideEntrance.deposit amount).run s).snd
    deposit_sets_pool_balance_spec amount s s' := by
  simpa [deposit_sets_pool_balance_spec] using (deposit_slot_writes amount s).1

theorem deposit_sets_sender_credit
    (amount : Uint256) (s : ContractState) :
    let s' := ((SideEntrance.deposit amount).run s).snd
    deposit_sets_sender_credit_spec amount s s' := by
  simpa [deposit_sets_sender_credit_spec] using (deposit_slot_writes amount s).2

theorem flashLoanViaDeposit_preserves_pool_balance
    (amount : Uint256) (s : ContractState)
    (hBorrow : amount <= s.storage 0) :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    flashLoanViaDeposit_preserves_pool_balance_spec amount s s' := by
  simpa [flashLoanViaDeposit_preserves_pool_balance_spec] using
    (flashLoanViaDeposit_slot_writes amount s hBorrow).1

theorem flashLoanViaDeposit_sets_sender_credit
    (amount : Uint256) (s : ContractState)
    (hBorrow : amount <= s.storage 0) :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    flashLoanViaDeposit_sets_sender_credit_spec amount s s' := by
  simpa [flashLoanViaDeposit_sets_sender_credit_spec] using
    (flashLoanViaDeposit_slot_writes amount s hBorrow).2.1

theorem exploit_trace_drains_pool
    (amount : Uint256) (s : ContractState)
    (hBorrow : amount <= s.storage 0)
    (hFresh : s.storageMap 2 s.sender = 0) :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    let s'' := ((SideEntrance.withdraw).run s').snd
    exploit_trace_drains_pool_spec amount s s'' := by
  have hFlash := flashLoanViaDeposit_slot_writes amount s hBorrow
  have hPoolEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0 = s.storage 0 :=
    hFlash.1
  have hCreditEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2 s.sender =
      add (s.storageMap 2 s.sender) amount := hFlash.2.1
  have hSenderEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender = s.sender :=
    hFlash.2.2
  rw [hFresh] at hCreditEq
  have hCredit : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
      ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender = amount := by
    rw [hSenderEq, hCreditEq]
    exact Verity.Core.Uint256.zero_add amount
  have hCreditBound : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
      ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender <=
      ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0 := by
    rw [hCredit, hPoolEq]
    exact hBorrow
  have hWithdraw := withdraw_slot_write ((SideEntrance.flashLoanViaDeposit amount).run s).snd hCreditBound
  unfold exploit_trace_drains_pool_spec
  calc ((SideEntrance.withdraw).run ((SideEntrance.flashLoanViaDeposit amount).run s).snd).snd.storage 0
      = sub (((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0)
            (((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
             ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender) := hWithdraw
    _ = sub (s.storage 0) amount := by rw [hPoolEq, hCredit]

end Benchmark.Cases.DamnVulnerableDeFi.SideEntrance
