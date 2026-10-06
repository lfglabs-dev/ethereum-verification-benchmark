import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] private theorem storageAddr_writeAddrSlot (s : ContractState) (slotIdx : Nat) (value : Address) (slotIdx' : Nat) :
    (s.writeAddrSlot slotIdx value).storageAddr slotIdx' =
      if slotIdx' == slotIdx then value else s.storageAddr slotIdx' := by
  by_cases h : slotIdx' = slotIdx
  · subst h; simp
  · simp [ContractState.storageAddr_writeAddrSlot_other s h value, h]
@[simp] private theorem storageMap_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256)
    (slotIdx' : Nat) (key' : Address) :
    (s.writeMap slotIdx key value).storageMap slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMap slotIdx' key' := by
  simp [ContractState.storageMap, ContractState.writeMap]
@[simp] private theorem storageMapUint_writeMapUint (s : ContractState) (slotIdx : Nat) (key value : Uint256)
    (slotIdx' : Nat) (key' : Uint256) :
    (s.writeMapUint slotIdx key value).storageMapUint slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMapUint slotIdx' key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint]
@[simp] private theorem storage_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storage = s.storage := by
  funext wordSlot; simp [ContractState.storage, ContractState.writeMap2]
@[simp] private theorem storageAddr_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageAddr = s.storageAddr := by
  funext addrSlot; simp [ContractState.storageAddr, ContractState.writeMap2]
@[simp] private theorem storageMap_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap = s.storageMap := by
  funext mapSlot mapKey; simp [ContractState.storageMap, ContractState.writeMap2]
@[simp] private theorem storageMapUint_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey; simp [ContractState.storageMapUint, ContractState.writeMap2]
@[simp] private theorem storageMap2_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256)
    (slotIdx' : Nat) (key1' key2' : Address) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap2 slotIdx' key1' key2' =
      if slotIdx' == slotIdx && key1' == key1 && key2' == key2 then value else s.storageMap2 slotIdx' key1' key2' := by
  simp [ContractState.storageMap2, ContractState.writeMap2, and_assoc]
@[simp] private theorem storageWords_slot_eq (s : ContractState) (slotIdx : Nat) :
    s.storageWords (.slot slotIdx) = s.storage slotIdx := rfl
@[simp] private theorem storageWords_map_eq (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.storageWords (.map slotIdx k) = s.storageMap slotIdx k := rfl
@[simp] private theorem storageWords_mapUint_eq (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.storageWords (.mapUint slotIdx k) = s.storageMapUint slotIdx k := rfl
@[simp] private theorem storageWords_map2_eq (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.storageWords (.map2 slotIdx k1 k2) = s.storageMap2 slotIdx k1 k2 := rfl


private theorem address_ne_of_neq_zero {a : Address}
    (h : (a != zeroAddress) = true) : a ≠ (0 : Address) := by
  have hNe : a ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at h
  simpa [zeroAddress] using hNe

private theorem uint256_mod_uint64_of_lt {x : Uint256}
    (hx : x < UINT64_MOD) : x % 18446744073709551616 = x := by
  cases hBal : x with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        norm_num [hBal, UINT64_MOD, Verity.Core.Uint256.ofNat,
          Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] at hx
        exact lt_of_lt_of_le hx (by decide)
      show (({ val := val, isLt := hlt } : Uint256) % 18446744073709551616) =
          ({ val := val, isLt := hlt } : Uint256)
      apply Verity.Core.Uint256.ext
      change (val % 18446744073709551616) % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt

/--
The exact-source `FHE.isInitialized(fromBalance)` guard fires before modeled
accounting writes. At the transfer-slice entry point, a passed wrapper predicate
and valid nonzero addresses therefore produce the modeled `ERC7984ZeroBalance`
error class with the original modeled accounting state.
-/
theorem uninitialized_sender_reverts_without_writes
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hAmount64 : amount < UINT64_MOD)
    (hUninitialized : s.storageMap 2 sender = 0) :
    uninitialized_sender_reverts_without_writes_spec
      ((ERC7984UpgradeableExact.confidentialTransferSlice
        sender recipient amount wrapperPreconditionsPassed).run s) s := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold uninitialized_sender_reverts_without_writes_spec
  simp [ERC7984UpgradeableExact.confidentialTransferSlice,
    ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
    ERC7984UpgradeableExact.balances,
    ERC7984UpgradeableExact.balanceInitialized,
    getMapping, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run,
    hWrapper, hSenderNZ, hRecipientNZ, hUninitialized]

/--
Once wrapper/plaintext guards pass and the sender handle is initialized, the
source's encrypted sufficiency result selects a transferred amount but cannot
select success versus revert.
-/
theorem initialized_transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender)
    (hAmount64 : amount < UINT64_MOD)
    (hSender64 : balanceOf s sender < UINT64_MOD)
    (hRecipient64 : balanceOf s recipient < UINT64_MOD) :
    initialized_transfer_no_balance_revert_spec
      ((ERC7984UpgradeableExact.confidentialTransferSlice
        sender recipient amount wrapperPreconditionsPassed).run s) := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold initialized_transfer_no_balance_revert_spec balanceIsInitialized at *
  simp [ERC7984UpgradeableExact.confidentialTransferSlice,
    ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
    ERC7984UpgradeableExact.balances,
    ERC7984UpgradeableExact.balanceInitialized,
    getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
    hWrapper, hSenderNZ, hRecipientNZ, hInitialized]

/--
For an initialized insufficient sender, the call succeeds with transferred = 0
and preserves the two plaintext-equivalent balances.
-/
theorem initialized_insufficient_transfer_zero
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender)
    (hAmount64 : amount < UINT64_MOD)
    (hSender64 : balanceOf s sender < UINT64_MOD)
    (hRecipient64 : balanceOf s recipient < UINT64_MOD)
    (hDistinct : sender ≠ recipient)
    (hInsufficient : ¬ (balanceOf s sender >= amount)) :
    initialized_insufficient_transfer_zero_spec sender recipient s
      ((ERC7984UpgradeableExact.confidentialTransferSlice
        sender recipient amount wrapperPreconditionsPassed).run s) := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
    simpa [balanceOf] using hInsufficient
  unfold initialized_insufficient_transfer_zero_spec balanceIsInitialized balanceOf at *
  constructor
  · simp [ERC7984UpgradeableExact.confidentialTransferSlice,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient']
  constructor
  · simp [ERC7984UpgradeableExact.confidentialTransferSlice,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.fst,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient']
  constructor
  · simp [ERC7984UpgradeableExact.confidentialTransferSlice,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient', hDistinct]
  · have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
    simp [ERC7984UpgradeableExact.confidentialTransferSlice,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient',
      hDistinct, hDistinct']
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd,
      Verity.Core.Uint256.add_zero]
    exact uint256_mod_uint64_of_lt hRecipient64

/--
Pairwise accounting conservation with every arithmetic/domain condition stated
explicitly. In particular, the theorem does not cover aliasing or uint64 wrap.
-/
theorem initialized_transfer_pair_conservation
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender)
    (hAmount64 : amount < UINT64_MOD)
    (hSender64 : balanceOf s sender < UINT64_MOD)
    (hRecipient64 : balanceOf s recipient < UINT64_MOD)
    (hDistinct : sender ≠ recipient)
    (hRecipientNoWrap :
      balanceOf s recipient + selectedTransferAmount s sender amount < UINT64_MOD) :
    let s' := ((ERC7984UpgradeableExact.confidentialTransferSlice
      sender recipient amount wrapperPreconditionsPassed).run s).snd
    initialized_transfer_pair_conservation_spec sender recipient s s' := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold initialized_transfer_pair_conservation_spec balanceIsInitialized balanceOf at *
  by_cases hSufficient : s.storageMap 1 sender >= amount
  · dsimp
    have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    have hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD := by
      simpa only [selectedTransferAmount, balanceOf, if_pos hSufficient]
        using hRecipientNoWrap
    simp [ERC7984UpgradeableExact.confidentialTransferSlice,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hSufficient',
      hDistinct, Ne.symm hDistinct]
    have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
        s.storageMap 1 recipient + amount :=
      uint256_mod_uint64_of_lt hToNoWrap
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [hToAddMod]
    calc
      sub (s.storageMap 1 sender) amount + (s.storageMap 1 recipient + amount)
          = (sub (s.storageMap 1 sender) amount + amount) + s.storageMap 1 recipient := by
              rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
              rw [← Verity.Core.Uint256.add_assoc]
      _ = s.storageMap 1 sender + s.storageMap 1 recipient := by
            change ((s.storageMap 1 sender - amount) + amount) + s.storageMap 1 recipient =
              s.storageMap 1 sender + s.storageMap 1 recipient
            rw [Verity.Core.Uint256.sub_add_cancel_left]
  · dsimp
    have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    have hToBal64 : s.storageMap 1 recipient < UINT64_MOD := by
      simpa only [selectedTransferAmount, balanceOf, if_neg hSufficient,
        Verity.Core.Uint256.add_zero] using hRecipientNoWrap
    simp [ERC7984UpgradeableExact.confidentialTransferSlice,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient',
      hDistinct, Ne.symm hDistinct, hToBal64]
    have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
        s.storageMap 1 recipient := by
      rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd,
        Verity.Core.Uint256.add_zero]
      exact uint256_mod_uint64_of_lt hToBal64
    rw [hZeroAddMod]

end Benchmark.Cases.Zama.ERC7984UpgradeableExactSource
