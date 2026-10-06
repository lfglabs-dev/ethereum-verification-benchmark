import Benchmark.Cases.Hypernova.SettledPayoutSafety.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.Hypernova.SettledPayoutSafety

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

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
@[simp] private theorem readMapChain_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).readMapChain =
      s.readMapChain := rfl
@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] private theorem storageMap_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256)
    (slotIdx' : Nat) (key' : Address) :
    (s.writeMap slotIdx key value).storageMap slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMap slotIdx' key' := by
  simp [ContractState.storageMap, ContractState.writeMap]
@[simp] private theorem ecmCallWords_abiEncodeStaticWords_stub
    (resVar : String) (n : Nat) (args : List Uint256) (siteId : Nat) (s : ContractState) :
    Contracts.ecmCallWords (Compiler.Modules.Hashing.abiEncodeStaticWordsModule resVar n)
      Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub args siteId s =
      ContractResult.success (Contracts.externalCallStubWord "abiEncodeStaticWords" args)
        { s with
          calls := s.calls ++ [{ (Contracts.linkedCallEntry "abiEncodeStaticWords" args .success
            [Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stubWord "abiEncodeStaticWords"
              (args.map (fun word => (word : Nat)))] siteId) with kind := .staticcall }]
          returndata := [Compiler.CompilationModel.Denote.wordNormalize
            (Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stubWord "abiEncodeStaticWords"
              (args.map (fun word => (word : Nat))))] } := rfl
@[simp] private theorem ecmCallWords_eip712Digest_stub
    (resVar : String) (args : List Uint256) (siteId : Nat) (s : ContractState) :
    Contracts.ecmCallWords (Compiler.Modules.Hashing.eip712DigestModule resVar)
      Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub args siteId s =
      ContractResult.success (Contracts.externalCallStubWord "eip712Digest" args)
        { s with
          calls := s.calls ++ [{ (Contracts.linkedCallEntry "eip712Digest" args .success
            [Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stubWord "eip712Digest"
              (args.map (fun word => (word : Nat)))] siteId) with kind := .staticcall }]
          returndata := [Compiler.CompilationModel.Denote.wordNormalize
            (Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stubWord "eip712Digest"
              (args.map (fun word => (word : Nat))))] } := rfl
@[simp] private theorem ecrecover_apply
    (digest v r signatureS : Uint256) (s : ContractState) :
    Contracts.ecrecover digest v r signatureS s =
      ContractResult.success
        (Verity.wordToAddress (Verity.Env.defaultCallOracle "ecrecover" [digest, v, r, signatureS]))
        s := rfl

private def setMappingState (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256)
    (state : ContractState) : ContractState :=
  ((setMapping s key value).run state).snd

@[simp] private theorem setMapping_apply (s : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) :
    setMapping s key value state = ContractResult.success () (setMappingState s key value state) := rfl

@[simp] private theorem storage_setMappingState (s : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) :
    (setMappingState s key value state).storage = state.storage := by
  funext slotIdx
  simp [setMappingState, setMapping, Contract.run, ContractResult.snd]

@[simp] private theorem storageAddr_setMappingState (s : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) :
    (setMappingState s key value state).storageAddr = state.storageAddr := by
  funext slotIdx
  simp [setMappingState, setMapping, Contract.run, ContractResult.snd]

@[simp] private theorem storageMap_setMappingState (s : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) (slotIdx' : Nat) (key' : Address) :
    (setMappingState s key value state).storageMap slotIdx' key' =
      if slotIdx' == s.slot && key' == key then value else state.storageMap slotIdx' key' := by
  simp [setMappingState, setMapping, Contract.run, ContractResult.snd]

@[simp] private theorem readMapChain_setMappingState (s : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) (slotIdx : Nat) (keys : List Nat) (offset : Nat) :
    (setMappingState s key value state).readMapChain slotIdx keys offset =
      state.readMapChain slotIdx keys offset := by
  simp [setMappingState, setMapping, Contract.run, ContractResult.snd]

private def recoverSignerPostState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) : ContractState :=
  (HypernovaPayoutSystem._recoverPayoutSigner trader fundedAccountId amount nonce
    deadline v r signatureS s).snd

@[simp] private theorem recoverPayoutSigner_run
    (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) (s : ContractState) :
    HypernovaPayoutSystem._recoverPayoutSigner trader fundedAccountId amount nonce
      deadline v r signatureS s =
      ContractResult.success
        (payoutRecoveredSigner s trader fundedAccountId amount nonce deadline v r signatureS)
        (recoverSignerPostState s trader fundedAccountId amount nonce deadline v r signatureS) := by
  simp [payoutRecoveredSigner, recoverSignerPostState, HypernovaPayoutSystem._recoverPayoutSigner,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    ContractResult.fst, ContractResult.snd, getStorage, getStorageAddr]

@[simp] private theorem storage_recoverSignerPostState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) :
    (recoverSignerPostState s trader fundedAccountId amount nonce deadline v r signatureS).storage =
      s.storage := by
  funext slotIdx
  simp [recoverSignerPostState, HypernovaPayoutSystem._recoverPayoutSigner,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, ContractResult.snd, getStorage, getStorageAddr]

@[simp] private theorem storageAddr_recoverSignerPostState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) :
    (recoverSignerPostState s trader fundedAccountId amount nonce deadline v r signatureS).storageAddr =
      s.storageAddr := by
  funext slotIdx
  simp [recoverSignerPostState, HypernovaPayoutSystem._recoverPayoutSigner,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, ContractResult.snd, getStorage, getStorageAddr]

@[simp] private theorem storageMap_recoverSignerPostState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) :
    (recoverSignerPostState s trader fundedAccountId amount nonce deadline v r signatureS).storageMap =
      s.storageMap := by
  funext slotIdx key
  simp [recoverSignerPostState, HypernovaPayoutSystem._recoverPayoutSigner,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, ContractResult.snd, getStorage, getStorageAddr]

@[simp] private theorem readMapChain_recoverSignerPostState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) :
    (recoverSignerPostState s trader fundedAccountId amount nonce deadline v r signatureS).readMapChain =
      s.readMapChain := by
  funext slotIdx keys offset
  simp [recoverSignerPostState, HypernovaPayoutSystem._recoverPayoutSigner,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, ContractResult.snd, getStorage, getStorageAddr]

@[simp] private theorem payoutRecoveredSigner_setMappingState
    (field : StorageSlot (Address → Uint256)) (key : Address) (val : Uint256)
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) :
    payoutRecoveredSigner (setMappingState field key val s)
      trader fundedAccountId amount nonce deadline v r signatureS =
      payoutRecoveredSigner s trader fundedAccountId amount nonce deadline v r signatureS := by
  simp [payoutRecoveredSigner, HypernovaPayoutSystem._recoverPayoutSigner,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    ContractResult.fst, getStorage, getStorageAddr]

@[simp] private theorem storageWordUint256_roundtrip (word : Uint256) :
    (Contracts.StorageWord.fromWord
      (Contracts.StorageWord.toWord word) : Uint256) = word :=
  rfl

@[simp] private theorem blockTimestamp_setMappingState (s : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) :
    (setMappingState s key value state).blockTimestamp = state.blockTimestamp := rfl

@[simp] private theorem bne_eq_decide_ne [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a != b) = decide (a ≠ b) := by
  cases h : a != b <;> simp_all

@[simp] private theorem bind_getStorage_raw (sl : StorageSlot Uint256)
    (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind (getStorage sl) f s = f (s.storage sl.slot) s := rfl

@[simp] private theorem bind_getStorageAddr_raw (sl : StorageSlot Address)
    (f : Address → Contract α) (s : ContractState) :
    Verity.bind (getStorageAddr sl) f s = f (s.storageAddr sl.slot) s := rfl

@[simp] private theorem bind_getMapping_raw (sl : StorageSlot (Address → Uint256)) (k : Address)
    (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind (getMapping sl k) f s = f (s.storageMap sl.slot k) s := rfl

@[simp] private theorem bind_setMapping_raw (sl : StorageSlot (Address → Uint256)) (k : Address)
    (v : Uint256) (f : Unit → Contract α) (s : ContractState) :
    Verity.bind (setMapping sl k v) f s = f () (setMappingState sl k v s) := rfl

@[simp] private theorem bind_require_true_raw (msg : String)
    (f : Unit → Contract α) (s : ContractState) :
    Verity.bind (Verity.require true msg) f s = f () s := rfl

@[simp] private theorem bind_requireSomeUint_some_raw (v : Uint256) (msg : String)
    (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind (Verity.Stdlib.Math.requireSomeUint (some v) msg) f s = f v s := rfl

@[simp] private theorem bind_blockTimestamp_raw (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind blockTimestamp f s = f s.blockTimestamp s := rfl

@[simp] private theorem bind_pure_raw (x : α) (f : α → Contract β) (s : ContractState) :
    Verity.bind (Verity.pure x) f s = f x s := rfl

@[simp] private theorem pure_apply_raw (x : α) (s : ContractState) :
    (Verity.pure x : Contract α) s = ContractResult.success x s := rfl

@[simp] private theorem bind_structMember2At_raw {κ₁ κ₂ α β : Type}
    [Contracts.StorageKey κ₁] [Contracts.StorageKey κ₂] [Contracts.StorageWord α]
    (baseSlot wordOffset : Nat) (packed : Option (Nat × Nat)) (key1 : κ₁) (key2 : κ₂)
    (f : α → Contract β) (s : ContractState) :
    Verity.bind (Contracts.structMember2At (α := α) baseSlot wordOffset packed key1 key2) f s =
      f (Contracts.StorageWord.fromWord (match packed with
        | none => s.readMapChain baseSlot [Contracts.StorageKey.toWord key1, Contracts.StorageKey.toWord key2] wordOffset
        | some (offset, width) => Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr offset
              (s.readMapChain baseSlot [Contracts.StorageKey.toWord key1, Contracts.StorageKey.toWord key2] wordOffset))
            ((2 ^ width - 1 : Nat) : Uint256))) s := rfl

@[simp] private theorem structMember2At_apply_raw {κ₁ κ₂ α : Type}
    [Contracts.StorageKey κ₁] [Contracts.StorageKey κ₂] [Contracts.StorageWord α]
    (baseSlot wordOffset : Nat) (packed : Option (Nat × Nat)) (key1 : κ₁) (key2 : κ₂)
    (s : ContractState) :
    Contracts.structMember2At (α := α) baseSlot wordOffset packed key1 key2 s =
      ContractResult.success (Contracts.StorageWord.fromWord (match packed with
        | none => s.readMapChain baseSlot [Contracts.StorageKey.toWord key1, Contracts.StorageKey.toWord key2] wordOffset
        | some (offset, width) => Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr offset
              (s.readMapChain baseSlot [Contracts.StorageKey.toWord key1, Contracts.StorageKey.toWord key2] wordOffset))
            ((2 ^ width - 1 : Nat) : Uint256))) s := rfl

@[simp] private theorem bind_setStructMember2At_none_raw {κ₁ κ₂ α β : Type}
    [Contracts.StorageKey κ₁] [Contracts.StorageKey κ₂] [Contracts.StorageWord α]
    (baseSlot wordOffset : Nat) (key1 : κ₁) (key2 : κ₂)
    (value : α) (f : Unit → Contract β) (s : ContractState) :
    Verity.bind (Contracts.setStructMember2At baseSlot wordOffset none key1 key2 value) f s =
      f () (s.writeMapChain baseSlot [Contracts.StorageKey.toWord key1, Contracts.StorageKey.toWord key2]
        wordOffset (Contracts.StorageWord.toWord value)) := rfl

@[simp] private theorem bind_recoverPayoutSigner_raw
    (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32)
    (f : Address → Contract α) (s : ContractState) :
    Verity.bind (HypernovaPayoutSystem._recoverPayoutSigner trader fundedAccountId amount nonce
      deadline v r signatureS) f s =
      f (payoutRecoveredSigner s trader fundedAccountId amount nonce deadline v r signatureS)
        (recoverSignerPostState s trader fundedAccountId amount nonce deadline v r signatureS) := by
  dsimp [Verity.bind]
  rw [recoverPayoutSigner_run]

private theorem div_val_of_ne_zero (a b : Uint256) (hb : b.val ≠ 0)
    (hDivLt : a.val / b.val < modulus) :
    (div a b).val = a.val / b.val := by
  show (Verity.Core.Uint256.div a b).val = a.val / b.val
  unfold Verity.Core.Uint256.div
  rw [if_neg hb]
  show (Verity.Core.Uint256.ofNat (a.val / b.val)).val = a.val / b.val
  rw [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hDivLt

private theorem bpsDenominator_val : BPS_DENOMINATOR.val = 10000 := by
  native_decide

private theorem pinnedVault_ne_zero : HypernovaPayoutSystem.pinnedVault ≠ zeroAddress := by
  native_decide

private theorem active_ne_zero : (2 : Uint256) ≠ 0 := by
  native_decide

private theorem one_sub_one_eq_zero : sub (1 : Uint256) 1 = 0 := by
  native_decide

/-- The clamped basis-point formula never exceeds its gross input, even after
`Uint256` modular multiplication. Successful source execution is therefore not needed
for this arithmetic bound. -/
private theorem traderPayoutAmount_le_amount
    (s : ContractState) (trader : Address) (amount : Uint256) :
    traderPayoutAmount s trader amount <= amount := by
  let split := effectiveTraderSplit
    (s.storageMap 12 HypernovaPayoutSystem.pinnedVault)
    (s.storageMap 5 trader)
  have hSplitLe : split.val ≤ 10000 := by
    dsimp [split, effectiveTraderSplit]
    simp only [Verity.Core.Uint256.val_ite, Verity.Core.Uint256.lt_def,
      bpsDenominator_val]
    by_cases h :
        10000 < (add (s.storageMap 12 HypernovaPayoutSystem.pinnedVault)
          (s.storageMap 5 trader)).val
    · simp [h]
    · simp [h, Nat.le_of_not_gt h]
  have hBpsNe : BPS_DENOMINATOR.val ≠ 0 := by
    rw [bpsDenominator_val]
    decide
  have hDivLt :
      (mul amount split).val / BPS_DENOMINATOR.val < modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (mul amount split).isLt
  have hDivVal :
      (div (mul amount split) BPS_DENOMINATOR).val =
        (mul amount split).val / BPS_DENOMINATOR.val :=
    div_val_of_ne_zero _ _ hBpsNe hDivLt
  have hMulVal :
      (mul amount split).val =
        (amount.val * split.val) % modulus := by
    rfl
  change (div (mul amount split) BPS_DENOMINATOR).val ≤ amount.val
  rw [hDivVal, hMulVal, bpsDenominator_val]
  calc
    (amount.val * split.val) % modulus / 10000 ≤
        (amount.val * split.val) / 10000 :=
      Nat.div_le_div_right (Nat.mod_le _ _)
    _ ≤ (amount.val * 10000) / 10000 :=
      Nat.div_le_div_right (Nat.mul_le_mul_left amount.val hSplitLe)
    _ = amount.val := Nat.mul_div_cancel _ (by decide)

private def requestPayoutPreExecuteState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32) : ContractState :=
  let s1 := setMappingState HypernovaPayoutSystem.nonces trader (add (s.storageMap 8 trader) 1) s
  recoverSignerPostState s1 trader fundedAccountId amount (s.storageMap 8 trader)
    deadline v r signatureS

private def executePayoutPreProcessState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32) : ContractState :=
  let s2 := requestPayoutPreExecuteState s trader fundedAccountId amount deadline v r signatureS
  let keys := [Core.Address.toNat trader, fundedAccountId.val]
  let newEquity := sub (s.readMapChain 3 keys 3) amount
  let s3 := s2.writeMapChain 3 keys 3 newEquity
  s3.writeMapChain 3 keys 4 0

private def settledPayoutPostState
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32) : ContractState :=
  let s4 := executePayoutPreProcessState s trader fundedAccountId amount deadline v r signatureS
  let traderAmount := traderPayoutAmount s trader amount
  let s5 := setMappingState HypernovaPayoutSystem.traderUsdcBalances trader
    (add (s.storageMap 14 trader) traderAmount) s4
  setMappingState HypernovaPayoutSystem.vaultUsdcBalance HypernovaPayoutSystem.pinnedVault
    (sub (s.storageMap 13 HypernovaPayoutSystem.pinnedVault) traderAmount) s5

private theorem processPayout_eq_of_valid
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool)
    (hValid : validSettledPayoutRequest s trader fundedAccountId amount deadline v r signatureS transferSucceeds) :
    HypernovaPayoutSystem.processPayout trader amount (s.storageMap 5 trader) transferSucceeds
        (executePayoutPreProcessState s trader fundedAccountId amount deadline v r signatureS) =
      ContractResult.success ()
        (settledPayoutPostState s trader fundedAccountId amount deadline v r signatureS) := by
  rcases hValid with
    ⟨_, _, _, _, hVault, _, _, _, _, _, hTotalBalance,
      hTraderNonzero, hAmountAllocated, hSplitAdd, hSplitMul,
      hTraderAmountBalance, _, hTraderAdd, hTransfer⟩
  rcases hVault with ⟨_, hVaultImmutable, _, hDistinct⟩
  have hVaultImmutableLiteral :
      s.storageAddr 15 = HypernovaPayoutSystem.pinnedTradingAccounts := by
    simpa [HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts] using
      hVaultImmutable
  have hVaultSub := Verity.Proofs.Stdlib.Math.safeSub_some
    (s.storageMap 13 HypernovaPayoutSystem.pinnedVault)
    (traderPayoutAmount s trader amount) hTraderAmountBalance
  have hTraderLeAmount := traderPayoutAmount_le_amount s trader amount
  have hProtocolSub := Verity.Proofs.Stdlib.Math.safeSub_some
    amount (traderPayoutAmount s trader amount) hTraderLeAmount
  have hAmountAllocatedVal :
      amount.val <= (s.storageMap 11 HypernovaPayoutSystem.pinnedVault).val :=
    hAmountAllocated
  simp [zeroAddress] at hTraderNonzero
  simp [traderPayoutAmount, effectiveTraderSplit, BPS_DENOMINATOR]
    at hSplitAdd hSplitMul hTraderLeAmount hTraderAmountBalance hTraderAdd
      hVaultSub hProtocolSub
  unfold settledPayoutPostState executePayoutPreProcessState requestPayoutPreExecuteState
  simp [HypernovaPayoutSystem.processPayout,
    BPS_DENOMINATOR,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    HypernovaPayoutSystem.nonces,
    HypernovaPayoutSystem.vaultPaused,
    HypernovaPayoutSystem.maxWithdrawalLimit,
    HypernovaPayoutSystem.profitSplit,
    HypernovaPayoutSystem.vaultUsdcBalance,
    HypernovaPayoutSystem.traderUsdcBalances,
    effectiveTraderSplit, traderPayoutAmount,
    requireSomeUint,
    HSub.hSub, Bind.bind, Pure.pure,
    Contract.run, ContractResult.fst, ContractResult.snd,
    hVaultImmutable, hVaultImmutableLiteral, hDistinct,
    hTotalBalance, hTraderNonzero,
    hAmountAllocated, hAmountAllocatedVal, hSplitAdd, hSplitMul,
    hTraderLeAmount, hTraderAmountBalance, hTraderAdd, hTransfer,
    hVaultSub, hProtocolSub]

private theorem executePayout_eq_of_valid
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool)
    (hValid : validSettledPayoutRequest s trader fundedAccountId amount deadline v r signatureS transferSucceeds) :
    HypernovaPayoutSystem._executePayout trader fundedAccountId amount transferSucceeds
        (requestPayoutPreExecuteState s trader fundedAccountId amount deadline v r signatureS) =
      ContractResult.success ()
        (settledPayoutPostState s trader fundedAccountId amount deadline v r signatureS) := by
  have hProcess := processPayout_eq_of_valid s trader fundedAccountId amount deadline v r signatureS transferSucceeds hValid
  dsimp [executePayoutPreProcessState, requestPayoutPreExecuteState, HypernovaPayoutSystem.nonces, sub] at hProcess
  rcases hValid with
    ⟨_, _, _, _, hVault, hStatusActive,
      hCanWithdraw, hEquity, hAmountLeProfit, _, _, _, _, _, _, _, _, _, _⟩
  rcases hVault with ⟨_, hVaultImmutable, hDomain, hDistinct⟩
  have hEquityVal : (initialEquityAt s trader fundedAccountId).val < (equityAt s trader fundedAccountId).val :=
    hEquity
  have hProfitSub := Verity.Proofs.Stdlib.Math.safeSub_some
    (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)
    (Nat.le_of_lt hEquity)
  have hProfitLeEquity := Verity.Proofs.Stdlib.Math.safeSub_result_le
    (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)
    (settledProfit s trader fundedAccountId) hProfitSub
  have hAmountLeEquity : amount.val <= (equityAt s trader fundedAccountId).val :=
    Nat.le_trans hAmountLeProfit hProfitLeEquity
  have hEquitySub := Verity.Proofs.Stdlib.Math.safeSub_some
    (equityAt s trader fundedAccountId) amount hAmountLeEquity
  have hOneSubOne := one_sub_one_eq_zero
  simp [fundedStatusAt, canWithdrawAt, equityAt, initialEquityAt,
    settledProfit, HypernovaPayoutSystem.fundedStatusOf,
    HypernovaPayoutSystem.canWithdrawOf, HypernovaPayoutSystem.equityOf,
    HypernovaPayoutSystem.initialEquityOf, HypernovaPayoutSystem.structMember2,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    Bind.bind, Pure.pure, Contract.run, ContractResult.fst,
    hVaultImmutable, hDomain, ACTIVE]
    at hStatusActive hCanWithdraw hEquity hEquityVal hAmountLeProfit hProfitSub hEquitySub
  unfold requestPayoutPreExecuteState
  simp [HypernovaPayoutSystem._executePayout,
    HypernovaPayoutSystem.fundedStatusOf,
    HypernovaPayoutSystem.initialEquityOf,
    HypernovaPayoutSystem.equityOf,
    HypernovaPayoutSystem.canWithdrawOf,
    HypernovaPayoutSystem.structMember2,
    HypernovaPayoutSystem.setStructMember2,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    HypernovaPayoutSystem.userBonusBps,
    HypernovaPayoutSystem.nonces,
    requireSomeUint,
    HSub.hSub, Bind.bind, Pure.pure,
    Contract.run, ContractResult.fst, ContractResult.snd,
    hVaultImmutable, hDomain, hDistinct,
    hStatusActive, hCanWithdraw, hEquity, hEquityVal, hAmountLeProfit,
    hProfitSub, hEquitySub, hOneSubOne, hProcess]

private theorem payoutResult_eq_of_valid
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool)
    (hValid : validSettledPayoutRequest s trader fundedAccountId amount deadline v r signatureS transferSucceeds) :
    payoutResult s trader fundedAccountId amount deadline v r signatureS transferSucceeds =
      ContractResult.success ()
        (settledPayoutPostState s trader fundedAccountId amount deadline v r signatureS) := by
  have hExec := executePayout_eq_of_valid s trader fundedAccountId amount deadline v r signatureS transferSucceeds hValid
  dsimp [requestPayoutPreExecuteState, HypernovaPayoutSystem.nonces] at hExec
  rcases hValid with
    ⟨hExists, hSuspended, hDeadline, hAmount, hVault, hStatusActive,
      _, _, _, hSigner, _, _, _, _, _, _, hNonceAdd, _, _⟩
  rcases hVault with ⟨hConfiguredVault, hVaultImmutable, hDomain, _⟩
  have hDeadlineVal : s.blockTimestamp.val <= deadline.val := hDeadline
  have hPinnedVaultNonzero := pinnedVault_ne_zero
  have hConfiguredNonzero : s.storageAddr 0 ≠ zeroAddress := by
    rw [hConfiguredVault]
    exact hPinnedVaultNonzero
  have hActiveNonzeroLiteral := active_ne_zero
  have hStatusExists : fundedStatusAt s trader fundedAccountId ≠ 0 := by
    rw [hStatusActive]
    exact hActiveNonzeroLiteral
  simp [zeroAddress] at hPinnedVaultNonzero hConfiguredNonzero
  simp [fundedStatusAt, HypernovaPayoutSystem.fundedStatusOf,
    HypernovaPayoutSystem.structMember2,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    Bind.bind, Pure.pure, Contract.run, ContractResult.fst,
    hVaultImmutable, hDomain, ACTIVE]
    at hStatusActive hStatusExists
  unfold payoutResult
  simp [HypernovaPayoutSystem.requestPayout,
    HypernovaPayoutSystem.fundedStatusOf,
    HypernovaPayoutSystem.structMember2,
    HypernovaPayoutSystem.vault,
    ACTIVE,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    HypernovaPayoutSystem.userSuspended,
    HypernovaPayoutSystem.userExists,
    HypernovaPayoutSystem.nonces,
    requireSomeUint,
    Bind.bind, Pure.pure,
    Contract.run, ContractResult.fst, ContractResult.snd,
    hSuspended, hExists, hDeadline, hDeadlineVal, hAmount, hConfiguredVault,
    hPinnedVaultNonzero, hConfiguredNonzero,
    hVaultImmutable, hDomain,
    hStatusActive, hStatusExists, hActiveNonzeroLiteral,
    hSigner, hNonceAdd, hExec]

/-- A valid settled payout request preserves the requested accounting guarantees. -/
theorem validSettledPayout_is_safe
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool)
    (hValid : validSettledPayoutRequest s trader fundedAccountId amount deadline v r signatureS transferSucceeds) :
    settledPayoutSafety s trader fundedAccountId amount deadline v r signatureS transferSucceeds := by
  have hRun := payoutResult_eq_of_valid s trader fundedAccountId amount deadline v r signatureS transferSucceeds hValid
  rcases hValid with
    ⟨_, _, _, _, hVault, _, _, hEquity, hAmountLeProfit, _, _, _, _, _, _, _, _, _, _⟩
  rcases hVault with ⟨_, hVaultImmutable, _, hDistinct⟩
  have hProfitSub := Verity.Proofs.Stdlib.Math.safeSub_some
    (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)
    (Nat.le_of_lt hEquity)
  have hProfitLeEquity := Verity.Proofs.Stdlib.Math.safeSub_result_le
    (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)
    (settledProfit s trader fundedAccountId) hProfitSub
  have hAmountLeEquity : amount.val <= (equityAt s trader fundedAccountId).val :=
    Nat.le_trans hAmountLeProfit hProfitLeEquity
  have hTraderLeAmount := traderPayoutAmount_le_amount s trader amount
  have hPostEquityGeInitial :
      sub (equityAt s trader fundedAccountId) amount >=
        initialEquityAt s trader fundedAccountId := by
    simp only [Verity.Core.Uint256.le_def]
    have hPostSubVal :
        (sub (equityAt s trader fundedAccountId) amount).val =
          (equityAt s trader fundedAccountId).val - amount.val := by
      change
        (((equityAt s trader fundedAccountId) - amount : Uint256) : Nat) =
          (equityAt s trader fundedAccountId).val - amount.val
      exact Verity.Core.Uint256.sub_eq_of_le hAmountLeEquity
    rw [hPostSubVal]
    have hProfitVal :
        (settledProfit s trader fundedAccountId).val =
          (equityAt s trader fundedAccountId).val -
            (initialEquityAt s trader fundedAccountId).val := by
      unfold settledProfit
      exact Verity.Core.Uint256.sub_eq_of_le (Nat.le_of_lt hEquity)
    have hAmountLeProfitVal :
        amount.val <=
          (equityAt s trader fundedAccountId).val -
            (initialEquityAt s trader fundedAccountId).val := by
      calc
        amount.val <= (settledProfit s trader fundedAccountId).val := hAmountLeProfit
        _ = (equityAt s trader fundedAccountId).val -
            (initialEquityAt s trader fundedAccountId).val := hProfitVal
    have hAmountPlusInitialLeEquity :
        amount.val + (initialEquityAt s trader fundedAccountId).val <=
          (equityAt s trader fundedAccountId).val :=
      Nat.add_le_of_le_sub (Nat.le_of_lt hEquity) hAmountLeProfitVal
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using hAmountPlusInitialLeEquity
  have hPostEquityGeInitialRaw :
      (s.readMapChain 3 [Core.Address.toNat trader, fundedAccountId.val] 1).val <=
        (sub (s.readMapChain 3 [Core.Address.toNat trader, fundedAccountId.val] 3) amount).val := by
    simpa [initialEquityAt, equityAt, HypernovaPayoutSystem.initialEquityOf,
      HypernovaPayoutSystem.equityOf, HypernovaPayoutSystem.structMember2,
      Contracts.structMember2At, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.fst, getStorage, getStorageAddr] using
      hPostEquityGeInitial
  unfold settledPayoutSafety
  rw [hRun]
  simp [settledPayoutPostState, executePayoutPreProcessState, requestPayoutPreExecuteState,
    fundedStatusAt, initialEquityAt, equityAt, canWithdrawAt,
    HypernovaPayoutSystem.fundedStatusOf,
    HypernovaPayoutSystem.initialEquityOf,
    HypernovaPayoutSystem.equityOf,
    HypernovaPayoutSystem.canWithdrawOf,
    HypernovaPayoutSystem.structMember2,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.nonces,
    HypernovaPayoutSystem.vaultUsdcBalance,
    HypernovaPayoutSystem.traderUsdcBalances,
    Contracts.structMember2At,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.fst, ContractResult.snd, ContractResult.isSuccess,
    getStorageAddr, getStorage,
    hVaultImmutable, hDistinct, hTraderLeAmount, hAmountLeProfit,
    hPostEquityGeInitial, hPostEquityGeInitialRaw]

/-- Every successful payout transfers no more than its authorized gross amount. -/
theorem successfulPayout_never_overpays
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) :
    successfulPayoutNeverOverpays s trader fundedAccountId amount deadline v r signatureS
      transferSucceeds := by
  unfold successfulPayoutNeverOverpays
  intro _ _
  exact traderPayoutAmount_le_amount s trader amount

end Benchmark.Cases.Hypernova.SettledPayoutSafety
