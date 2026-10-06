import Benchmark.Cases.Polygon.AgglayerBridge.Contract
import Benchmark.Cases.Polygon.AgglayerBridge.Specs
import Aesop

namespace Benchmark.Cases.Polygon.AgglayerBridge

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
Reference proofs for the AgglayerBridge claim membership/nullifier invariant.
-/

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
@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] private theorem storageMapUint_writeMapUint (s : ContractState) (slotIdx : Nat) (key value : Uint256) (slotIdx' : Nat) (key' : Uint256) :
    (s.writeMapUint slotIdx key value).storageMapUint slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMapUint slotIdx' key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint]
@[simp] private theorem externalArgWord_zero_nat :
    Contracts.externalArgWord (0 : Nat) = 0 := rfl
@[simp] private theorem externalArgWord_zero_uint :
    Contracts.externalArgWord (0 : Uint256) = 0 := rfl
@[simp] private theorem getElem?_zero_getD_eq_getElem (arr : Array Uint256) (h : 0 < arr.size) :
    arr[0]?.getD 0 = arr[0] := by
  simp [h]


private theorem setAndCheckClaimed_consumes
    (s : ContractState)
    (leafIndex sourceBridgeNetwork : Uint256) :
    match (AgglayerBridge._setAndCheckClaimed leafIndex sourceBridgeNetwork).run s with
    | ContractResult.success _ s' =>
        nullifierConsumed_spec s s' (s.storage 2) leafIndex sourceBridgeNetwork
    | ContractResult.revert _ _ => True := by
  cases hrun : ((AgglayerBridge._setAndCheckClaimed leafIndex sourceBridgeNetwork).run s) with
  | success value s' =>
      unfold AgglayerBridge._setAndCheckClaimed at hrun
      simp [
        AgglayerBridge._bitmapPositions,
        nullifierConsumed_spec,
        nullifierConsumable_spec,
        claimedWord,
        nullifierGlobalIndex,
        globalIndexForNullifierModel,
        _bitmapPositions_wordPos,
        _bitmapPositions_bitPos,
        _bitmapPositions_mask,
        MAINNET_NETWORK_ID,
        ZKEVM_NETWORK_ID,
        MAX_LEAFS_PER_NETWORK,
        LOW_8_MASK,
        Contract.run,
        require,
        Verity.require,
        Bind.bind,
        Pure.pure,
        Verity.bind,
        Verity.pure,
        getStorage,
        getMappingUint,
        setMappingUint
      ] at hrun ⊢
      repeat' split at * <;> simp_all [
        require, Verity.require, Bind.bind, Pure.pure, Verity.bind, Verity.pure,
        MAINNET_NETWORK_ID, ZKEVM_NETWORK_ID, MAX_LEAFS_PER_NETWORK, LOW_8_MASK,
        getMappingUint, setMappingUint, AgglayerBridge.networkID
      ]
      all_goals
        subst_vars
        simp_all [AgglayerBridge.claimedBitMap]
  | «revert» msg s' =>
      simp [hrun]

private theorem setAndCheckClaimed_consumes_of_success
    (s : ContractState)
    (leafIndex sourceBridgeNetwork : Uint256)
    (value : Unit)
    (s' : ContractState)
    (h :
      AgglayerBridge._setAndCheckClaimed leafIndex sourceBridgeNetwork s =
        ContractResult.success value s') :
    nullifierConsumed_spec s s' (s.storage 2) leafIndex sourceBridgeNetwork := by
  have hmatch := setAndCheckClaimed_consumes s leafIndex sourceBridgeNetwork
  simp [Contract.run, h] at hmatch
  exact hmatch

private theorem claimAsset_valid_leaf_and_reaches_nullifier_helper
    (s : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originTokenAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) :
    match
      (AgglayerBridge.claimAsset
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash).run s
    with
    | ContractResult.success _ s' =>
        claimAsset_valid_leaf_and_reaches_nullifier_helper_spec
          s s' smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
          originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash
    | ContractResult.revert _ _ => True := by
  cases hrun :
    ((AgglayerBridge.claimAsset
      smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
      originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash).run s) with
  | success value s' =>
      simp [
        AgglayerBridge.claimAsset,
        AgglayerBridge.getLeafValue,
        AgglayerBridge.calculateGlobalExitRoot,
        AgglayerBridge.hashPair,
        AgglayerBridge._validateAndDecodeGlobalIndex,
        AgglayerBridge._bitmapPositions,
        claimAsset_valid_leaf_and_reaches_nullifier_helper_spec,
        validClaimLeaf_spec,
        isClaimed_spec,
        nullifierConsumable_spec,
        nullifierConsumed_spec,
        nullifierHelperSucceeded_spec,
        claimedWord,
        nullifierGlobalIndex,
        globalIndexForNullifierModel,
        calculateGlobalExitRoot_spec,
        calculateRoot_spec,
        getLeafValue_spec,
        _validateAndDecodeGlobalIndex_leafIndex,
        _validateAndDecodeGlobalIndex_indexRollup,
        _validateAndDecodeGlobalIndex_sourceBridgeNetwork,
        _validateAndDecodeGlobalIndex_valid,
        _bitmapPositions_wordPos,
        _bitmapPositions_bitPos,
        _bitmapPositions_mask,
        Contract.run,
        Contracts.arrayElementChecked,
        require,
        Verity.require,
        Bind.bind,
        Pure.pure,
        Verity.bind,
        Verity.pure,
        getStorage,
        getMappingUint,
        setMappingUint
      ] at hrun ⊢
      repeat'
        first
        | simp_all [
            require, Verity.require, Bind.bind, Pure.pure, Verity.bind, Verity.pure,
            Contract.run, Contracts.arrayElementChecked, getMappingUint, setMappingUint,
            AgglayerBridge.networkID, AgglayerBridge.globalExitRootMap,
            MAINNET_NETWORK_ID, ZKEVM_NETWORK_ID, LEAF_TYPE_ASSET, LEAF_TYPE_MESSAGE,
            GLOBAL_INDEX_MAINNET_FLAG, LOW_32_MASK, LOW_8_MASK, MAX_LEAFS_PER_NETWORK
          ]
        | split at *
        | split
        | contradiction
      all_goals aesop
  | «revert» msg s' =>
      simp [hrun]

theorem claimAsset_valid_leaf_and_consumes_unique_nullifier
    (s : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originTokenAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) :
    match
      (AgglayerBridge.claimAsset
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash).run s
    with
    | ContractResult.success _ s' =>
        claimAsset_valid_leaf_and_consumes_unique_nullifier_spec
          s s' smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
          originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash
    | ContractResult.revert _ _ => True := by
  cases hrun :
    ((AgglayerBridge.claimAsset
      smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
      originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash).run s) with
  | success value s' =>
      have hclaim := claimAsset_valid_leaf_and_reaches_nullifier_helper
        s smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash
      simp [hrun, claimAsset_valid_leaf_and_reaches_nullifier_helper_spec, nullifierHelperSucceeded_spec] at hclaim
      rcases hclaim with ⟨hdest, hleaf, helperValue, hhelper⟩
      refine ⟨hdest, hleaf, ?_⟩
      exact setAndCheckClaimed_consumes_of_success
        s (_validateAndDecodeGlobalIndex_leafIndex globalIndex)
        (_validateAndDecodeGlobalIndex_sourceBridgeNetwork globalIndex) helperValue s' hhelper
  | «revert» msg s' =>
      simp [hrun]

theorem claimAsset_valid_leaf_and_nullifier_consumed_direct
    (s s' : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originTokenAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256)
    (h :
      (AgglayerBridge.claimAsset
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash).run s =
        ContractResult.success () s') :
    let leafIndex := _validateAndDecodeGlobalIndex_leafIndex globalIndex
    let sourceBridgeNetwork := _validateAndDecodeGlobalIndex_sourceBridgeNetwork globalIndex
    let leafValue := getLeafValue_spec LEAF_TYPE_ASSET originNetwork originTokenAddress
      destinationAddress destinationNetwork amount metadataHash
    destinationNetwork = s.storage 2 ∧
    validClaimLeaf_spec s smtProofLocalExitRoot smtProofRollupExitRoot
      globalIndex mainnetExitRoot rollupExitRoot leafValue ∧
    nullifierConsumed_spec s s' (s.storage 2) leafIndex sourceBridgeNetwork := by
  have hclaim := claimAsset_valid_leaf_and_consumes_unique_nullifier
    s smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
    originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash
  simpa [h, claimAsset_valid_leaf_and_consumes_unique_nullifier_spec] using hclaim

private theorem claimMessage_valid_leaf_and_reaches_nullifier_helper
    (s : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) :
    match
      (AgglayerBridge.claimMessage
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originAddress destinationNetwork destinationAddress amount metadataHash).run s
    with
    | ContractResult.success _ s' =>
        claimMessage_valid_leaf_and_reaches_nullifier_helper_spec
          s s' smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
          originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
    | ContractResult.revert _ _ => True := by
  cases hrun :
    ((AgglayerBridge.claimMessage
      smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
      originNetwork originAddress destinationNetwork destinationAddress amount metadataHash).run s) with
  | success value s' =>
      simp [
        AgglayerBridge.claimMessage,
        AgglayerBridge.getLeafValue,
        AgglayerBridge.calculateGlobalExitRoot,
        AgglayerBridge.hashPair,
        AgglayerBridge._validateAndDecodeGlobalIndex,
        AgglayerBridge._bitmapPositions,
        claimMessage_valid_leaf_and_reaches_nullifier_helper_spec,
        validClaimLeaf_spec,
        isClaimed_spec,
        nullifierConsumable_spec,
        nullifierConsumed_spec,
        nullifierHelperSucceeded_spec,
        claimedWord,
        nullifierGlobalIndex,
        globalIndexForNullifierModel,
        calculateGlobalExitRoot_spec,
        calculateRoot_spec,
        getLeafValue_spec,
        _validateAndDecodeGlobalIndex_leafIndex,
        _validateAndDecodeGlobalIndex_indexRollup,
        _validateAndDecodeGlobalIndex_sourceBridgeNetwork,
        _validateAndDecodeGlobalIndex_valid,
        _bitmapPositions_wordPos,
        _bitmapPositions_bitPos,
        _bitmapPositions_mask,
        Contract.run,
        Contracts.arrayElementChecked,
        require,
        Verity.require,
        Bind.bind,
        Pure.pure,
        Verity.bind,
        Verity.pure,
        getStorage,
        getMappingUint,
        setMappingUint
      ] at hrun ⊢
      repeat'
        first
        | simp_all [
            require, Verity.require, Bind.bind, Pure.pure, Verity.bind, Verity.pure,
            Contract.run, Contracts.arrayElementChecked, getMappingUint, setMappingUint,
            AgglayerBridge.networkID, AgglayerBridge.globalExitRootMap,
            MAINNET_NETWORK_ID, ZKEVM_NETWORK_ID, LEAF_TYPE_ASSET, LEAF_TYPE_MESSAGE,
            GLOBAL_INDEX_MAINNET_FLAG, LOW_32_MASK, LOW_8_MASK, MAX_LEAFS_PER_NETWORK
          ]
        | split at *
        | split
        | contradiction
      all_goals aesop
  | «revert» msg s' =>
      simp [hrun]

theorem claimMessage_valid_leaf_and_consumes_unique_nullifier
    (s : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) :
    match
      (AgglayerBridge.claimMessage
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originAddress destinationNetwork destinationAddress amount metadataHash).run s
    with
    | ContractResult.success _ s' =>
        claimMessage_valid_leaf_and_consumes_unique_nullifier_spec
          s s' smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
          originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
    | ContractResult.revert _ _ => True := by
  cases hrun :
    ((AgglayerBridge.claimMessage
      smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
      originNetwork originAddress destinationNetwork destinationAddress amount metadataHash).run s) with
  | success value s' =>
      have hclaim := claimMessage_valid_leaf_and_reaches_nullifier_helper
        s smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
      simp [hrun, claimMessage_valid_leaf_and_reaches_nullifier_helper_spec, nullifierHelperSucceeded_spec] at hclaim
      rcases hclaim with ⟨hdest, hleaf, helperValue, hhelper⟩
      refine ⟨hdest, hleaf, ?_⟩
      exact setAndCheckClaimed_consumes_of_success
        s (_validateAndDecodeGlobalIndex_leafIndex globalIndex)
        (_validateAndDecodeGlobalIndex_sourceBridgeNetwork globalIndex) helperValue s' hhelper
  | «revert» msg s' =>
      simp [hrun]

theorem claimMessage_valid_leaf_and_nullifier_consumed_direct
    (s s' : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256)
    (h :
      (AgglayerBridge.claimMessage
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originAddress destinationNetwork destinationAddress amount metadataHash).run s =
        ContractResult.success () s') :
    let leafIndex := _validateAndDecodeGlobalIndex_leafIndex globalIndex
    let sourceBridgeNetwork := _validateAndDecodeGlobalIndex_sourceBridgeNetwork globalIndex
    let leafValue := getLeafValue_spec LEAF_TYPE_MESSAGE originNetwork originAddress
      destinationAddress destinationNetwork amount metadataHash
    destinationNetwork = s.storage 2 ∧
    validClaimLeaf_spec s smtProofLocalExitRoot smtProofRollupExitRoot
      globalIndex mainnetExitRoot rollupExitRoot leafValue ∧
    nullifierConsumed_spec s s' (s.storage 2) leafIndex sourceBridgeNetwork := by
  have hclaim := claimMessage_valid_leaf_and_consumes_unique_nullifier
    s smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
    originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
  simpa [h, claimMessage_valid_leaf_and_consumes_unique_nullifier_spec] using hclaim

end Benchmark.Cases.Polygon.AgglayerBridge
