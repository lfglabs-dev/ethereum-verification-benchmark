import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

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

set_option linter.unusedSimpArgs false

@[simp] private theorem wordToAddress_addressToWord (a : Address) :
    wordToAddress (addressToWord a) = a := by
  simp [addressToWord, wordToAddress, Verity.Core.Address.ofNat, Verity.Core.Address.toNat,
    Verity.Core.Uint256.ofNat]
  ext
  change a.val % Verity.Core.Uint256.modulus % Verity.Core.Address.modulus = a.val
  simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS]
  have hlt : a.val < 2 ^ 160 := a.isLt
  omega

@[simp] private theorem addressOfNat_toNat_mod_uint256 (a : Address) :
    Verity.Core.Address.ofNat (Verity.Core.Address.toNat a % Verity.Core.Uint256.modulus) = a := by
  simpa [addressToWord, wordToAddress, Verity.Core.Uint256.ofNat] using
    wordToAddress_addressToWord a

theorem depositPegOut_registers_required_amount
    (quoteHash : Address)
    (value callFee gasFee penaltyFee msgValue dustThreshold : Uint256)
    (changeRefundSucceeds : Bool)
    (lpRskAddress rskRefundAddress : Address)
    (blockTimestamp : Uint256)
    (expireDate expireBlock : Uint256)
    (s : ContractState)
    (hValueAndCallNoOverflow : (add value callFee >= value) = true)
    (hRequiredNoOverflow : (add (add value callFee) gasFee >= add value callFee) = true)
    (hFresh : (s.storageMap 7 quoteHash == 0) = true)
    (hIncomplete : (s.storageMap 2 quoteHash == 0) = true)
    (hEnough : (add (add value callFee) gasFee <= msgValue) = true)
    (hChangeRefund :
      (if sub msgValue (add (add value callFee) gasFee) >= dustThreshold then
        changeRefundSucceeds
      else
        true) = true) :
    let s' := ((PegOutLifecycle.depositPegOut quoteHash value callFee gasFee
      penaltyFee msgValue dustThreshold changeRefundSucceeds lpRskAddress rskRefundAddress blockTimestamp
      expireDate expireBlock).run s).snd
    depositPegOut_registers_required_amount_spec
      quoteHash value callFee gasFee penaltyFee msgValue dustThreshold changeRefundSucceeds
      lpRskAddress rskRefundAddress blockTimestamp expireDate expireBlock s s' := by
  by_cases hChange : sub msgValue (add (add value callFee) gasFee) >= dustThreshold
  · have hRefundSucceeds : changeRefundSucceeds = true := by
      simpa [hChange] using hChangeRefund
    simp [depositPegOut_registers_required_amount_spec, depositedAmount, depositTimestampOf,
      expireDateOf, expireBlockOf, lpRecipientOf, userRefundRecipientOf,
      PegOutLifecycle.depositPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteDepositTimestamp,
      PegOutLifecycle.quoteExpireDate, PegOutLifecycle.quoteExpireBlock,
      PegOutLifecycle.quoteLpRskAddress, PegOutLifecycle.quoteRskRefundAddress,
      hValueAndCallNoOverflow, hRequiredNoOverflow, hFresh, hIncomplete, hEnough,
      hChange, hRefundSucceeds,
      getMapping, setMapping, setMappingAddr, addressToWord, wordToAddress,
      Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]
  · simp [depositPegOut_registers_required_amount_spec, depositedAmount, depositTimestampOf,
      expireDateOf, expireBlockOf, lpRecipientOf, userRefundRecipientOf,
      PegOutLifecycle.depositPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteDepositTimestamp,
      PegOutLifecycle.quoteExpireDate, PegOutLifecycle.quoteExpireBlock,
      PegOutLifecycle.quoteLpRskAddress, PegOutLifecycle.quoteRskRefundAddress,
      hValueAndCallNoOverflow, hRequiredNoOverflow, hFresh, hIncomplete, hEnough,
      hChange, getMapping, setMapping, setMappingAddr, addressToWord, wordToAddress,
      Verity.require, Verity.bind, Bind.bind,
      Pure.pure, Contract.run, ContractResult.snd]

theorem refundPegOut_conserves_quote_amount
    (quoteHash : Address)
    (transferSucceeds : Bool)
    (transferTime btcBlockTime firstConfirmationTimestamp
      expireDate currentTimestamp expireBlock currentBlock : Uint256)
    (s : ContractState)
    (hPenaltyDeadlineNoOverflow :
      add (s.storageMap 8 quoteHash) transferTime >= s.storageMap 8 quoteHash)
    (hPenaltyExpectedNoOverflow :
      add (add (s.storageMap 8 quoteHash) transferTime) btcBlockTime >=
        add (s.storageMap 8 quoteHash) transferTime)
    (hFallbackNoOverflow :
      add (s.storageMap 5 (lpRecipientOf s quoteHash)) (s.storageMap 0 quoteHash) >=
        s.storageMap 5 (lpRecipientOf s quoteHash))
    (hRegistered : (s.storageMap 7 quoteHash == completedFlag) = true)
    (hIncomplete : (s.storageMap 2 quoteHash == 0) = true) :
    let s' := ((PegOutLifecycle.refundPegOut quoteHash transferSucceeds transferTime
      btcBlockTime firstConfirmationTimestamp expireDate currentTimestamp expireBlock currentBlock).run s).snd
    refundPegOut_conserves_quote_amount_spec quoteHash transferSucceeds transferTime
      btcBlockTime firstConfirmationTimestamp expireDate currentTimestamp expireBlock currentBlock s s' := by
  have hRegistered' : (s.storageMap 7 quoteHash == 1) = true := by
    simpa [completedFlag] using hRegistered
  have hPenaltyDeadlineNoOverflow' :
      (s.storageMap 8 quoteHash).val <= (add (s.storageMap 8 quoteHash) transferTime).val := by
    simpa [GE.ge] using hPenaltyDeadlineNoOverflow
  have hPenaltyExpectedNoOverflow' :
      (add (s.storageMap 8 quoteHash) transferTime).val <=
        (add (add (s.storageMap 8 quoteHash) transferTime) btcBlockTime).val := by
    simpa [GE.ge] using hPenaltyExpectedNoOverflow
  have hFallbackNoOverflow' :
      (s.storageMap 5 (lpRecipientOf s quoteHash)).val <=
        (add (s.storageMap 5 (lpRecipientOf s quoteHash)) (s.storageMap 0 quoteHash)).val := by
    simpa [GE.ge, lpRecipientOf, wordToAddress] using hFallbackNoOverflow
  have hFallbackNoOverflowStored :
      (s.storageMap 5 (Verity.Core.Address.ofNat (s.storageMap 11 quoteHash).val)).val <=
        (add (s.storageMap 5 (Verity.Core.Address.ofNat (s.storageMap 11 quoteHash).val))
          (s.storageMap 0 quoteHash)).val := by
    simpa [lpRecipientOf, wordToAddress] using hFallbackNoOverflow'
  cases transferSucceeds <;>
    by_cases hPenalize :
      (((add (add (s.storageMap 8 quoteHash) transferTime) btcBlockTime).val <
          firstConfirmationTimestamp.val ∨
        expireDate.val < currentTimestamp.val) ∨
        expireBlock.val < currentBlock.val) <;>
    simp [refundPegOut_conserves_quote_amount_spec, slashCallMatchesPenalty,
      lpQuoteAmountAssigned,
      depositedAmount, penaltyAmount, completed, registered,
      paidToLp, fallbackBalance, slashCallAmountOf, depositTimestampOf, lpRecipientOf, wordToAddress,
      completedFlag,
      PegOutLifecycle.refundPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.lpPaid,
      PegOutLifecycle.internalBalance, PegOutLifecycle.slashCallAmount,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteDepositTimestamp,
      PegOutLifecycle.quoteLpRskAddress,
      hRegistered', hIncomplete, hPenaltyDeadlineNoOverflow', hPenaltyExpectedNoOverflow',
      hFallbackNoOverflow', hFallbackNoOverflowStored, hPenalize, getMapping, getMappingAddr, setMapping,
      Verity.require, Verity.bind, Bind.bind, Pure.pure,
      Contract.run, ContractResult.snd]

theorem refundUserPegOut_conserves_quote_amount
    (quoteHash : Address)
    (transferSucceeds : Bool)
    (currentTimestamp currentBlock : Uint256)
    (s : ContractState)
    (hFallbackNoOverflow :
      add (s.storageMap 5 (userRefundRecipientOf s quoteHash)) (s.storageMap 0 quoteHash) >=
        s.storageMap 5 (userRefundRecipientOf s quoteHash))
    (hRegistered : (s.storageMap 7 quoteHash == completedFlag) = true)
    (hExpiredDate : (currentTimestamp > s.storageMap 9 quoteHash) = true)
    (hExpiredBlock : (currentBlock > s.storageMap 10 quoteHash) = true)
    :
    let s' := ((PegOutLifecycle.refundUserPegOut quoteHash transferSucceeds currentTimestamp currentBlock).run s).snd
    refundUserPegOut_conserves_quote_amount_spec quoteHash transferSucceeds currentTimestamp currentBlock s s' := by
  have hRegistered' : (s.storageMap 7 quoteHash == 1) = true := by
    simpa [completedFlag] using hRegistered
  have hFallbackNoOverflow' :
      (s.storageMap 5 (userRefundRecipientOf s quoteHash)).val <=
        (add (s.storageMap 5 (userRefundRecipientOf s quoteHash)) (s.storageMap 0 quoteHash)).val := by
    simpa [GE.ge, userRefundRecipientOf, wordToAddress] using hFallbackNoOverflow
  have hFallbackNoOverflowStored :
      (s.storageMap 5 (Verity.Core.Address.ofNat (s.storageMap 12 quoteHash).val)).val <=
        (add (s.storageMap 5 (Verity.Core.Address.ofNat (s.storageMap 12 quoteHash).val))
          (s.storageMap 0 quoteHash)).val := by
    simpa [userRefundRecipientOf, wordToAddress] using hFallbackNoOverflow'
  cases transferSucceeds <;>
    simp [refundUserPegOut_conserves_quote_amount_spec,
      userQuoteAmountAssigned,
      depositedAmount, penaltyAmount, completed, registered,
      paidToUser, fallbackBalance, slashCallAmountOf, completedFlag,
      expireDateOf, expireBlockOf, userRefundRecipientOf, wordToAddress,
      PegOutLifecycle.refundUserPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.userPaid,
      PegOutLifecycle.internalBalance, PegOutLifecycle.slashCallAmount,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteExpireDate, PegOutLifecycle.quoteExpireBlock,
      PegOutLifecycle.quoteRskRefundAddress,
      hRegistered', hExpiredDate, hExpiredBlock, hFallbackNoOverflow', hFallbackNoOverflowStored,
      getMapping, getMappingAddr, setMapping,
      Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
