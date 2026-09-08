import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private theorem nonce_slot : TydroPositionAccount.nonce.slot = 0 := rfl
private theorem active_hash_slot : TydroPositionAccount.activeCallbackHash.slot = 1 := rfl
private theorem active_kind_slot : TydroPositionAccount.activeCallbackKind.slot = 2 := rfl
private theorem observed_hash_slot : TydroPositionAccount.effectObservedActiveHash.slot = 3 := rfl
private theorem completion_kind_slot : TydroPositionAccount.callbackCompletionKind.slot = 4 := rfl
private theorem emode_slot : TydroPositionAccount.modeledEModeCategory.slot = 5 := rfl
private theorem atoken_recipient_slot : TydroPositionAccount.aTokenRecoveryRecipient.slot = 6 := rfl
private theorem raw_supply_recipient_slot : TydroPositionAccount.rawSupplyRecoveryRecipient.slot = 7 := rfl
private theorem raw_borrow_recipient_slot : TydroPositionAccount.rawBorrowRecoveryRecipient.slot = 8 := rfl

macro "simp_tydro" : tactic =>
  `(tactic| simp_all (config := { maxSteps := 1000000 }) [
    TydroPositionAccount.checkOpenFloors, TydroPositionAccount.checkCloseFloors,
    TydroPositionAccount.consumeLifecycleAuthority,
    TydroPositionAccount.executeSignedOpenBoundary,
    TydroPositionAccount.executeSignedCloseBoundary,
    TydroPositionAccount.executeOperationAuthority,
    TydroPositionAccount.setEModeCategory, TydroPositionAccount.claimATokens,
    TydroPositionAccount.claimRawSupply, TydroPositionAccount.claimRawBorrow,
    ownerOf, poolOf, supplyAssetOf, borrowAssetOf, nonceOf, activeHashOf, activeKindOf,
    observedActiveHashOf, completionKindOf, eModeOf, aTokenRecipientOf,
    rawSupplyRecipientOf, rawBorrowRecipientOf, requireSomeUint,
    Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd, ContractResult.isSuccess,
    msgSender, contractAddress, blockTimestamp, getStorage, getStorageAddr,
    setStorage, setStorageAddr, nonce_slot, active_hash_slot, active_kind_slot,
    observed_hash_slot, completion_kind_slot, emode_slot, atoken_recipient_slot,
    raw_supply_recipient_slot, raw_borrow_recipient_slot])

 theorem open_enforces_signed_floors
    (minOut out minSupply supplied maxBorrowed borrowed minHealth health : Uint256)
    (settles : Bool) (s : ContractState) :
    open_floor_spec minOut out minSupply supplied maxBorrowed borrowed minHealth health settles s := by
  unfold open_floor_spec
  intro h
  by_cases h1 : minOut.val ≤ out.val <;> simp_tydro
  by_cases h2 : minSupply.val ≤ supplied.val <;> simp_tydro
  by_cases h3 : borrowed.val ≤ maxBorrowed.val <;> simp_tydro
  by_cases h4 : minHealth.val ≤ health.val <;> simp_tydro

 theorem close_enforces_signed_floors
    (minWithdraw withdrawn minOut out maxDebt debt maxCollateral collateral minHealth health : Uint256)
    (settles : Bool) (s : ContractState) :
    close_floor_spec minWithdraw withdrawn minOut out maxDebt debt maxCollateral collateral
      minHealth health settles s := by
  unfold close_floor_spec
  intro h
  by_cases h1 : minWithdraw.val ≤ withdrawn.val <;> simp_tydro
  by_cases h2 : minOut.val ≤ out.val <;> simp_tydro
  by_cases h3 : debt.val ≤ maxDebt.val <;> simp_tydro
  by_cases h4 : minHealth.val ≤ health.val <;> simp_tydro
  by_cases h5 : collateral.val ≤ maxCollateral.val <;> simp_tydro

 theorem lifecycle_success_requires_owner_authority
    (signedAccount signedOwner signedPool signedSupply signedBorrow authorizedCaller : Address)
    (signedNonce deadline : Uint256) (recoveredSigner : Address) (s : ContractState) :
    lifecycle_authority_spec signedAccount signedOwner signedPool signedSupply signedBorrow
      authorizedCaller signedNonce deadline recoveredSigner s := by
  unfold lifecycle_authority_spec
  dsimp only
  intro h
  by_cases h1 : signedAccount = s.thisAddress <;> simp_tydro
  by_cases h2 : signedOwner = ownerOf s <;> simp_tydro
  by_cases h3 : signedPool = poolOf s <;> simp_tydro
  by_cases h4 : signedSupply = supplyAssetOf s <;> simp_tydro
  by_cases h5 : signedBorrow = borrowAssetOf s <;> simp_tydro
  by_cases h6 : s.blockTimestamp.val ≤ deadline.val <;> simp_tydro
  by_cases h7 : authorizedCaller = zeroAddress
  · simp_tydro
    by_cases h9 : signedNonce = nonceOf s <;> simp_tydro
    by_cases h10 : recoveredSigner = ownerOf s <;> simp_tydro
    by_cases hov : nonceOf s = TydroPositionAccount.maxUint256 <;> simp_tydro
  · simp_tydro
    by_cases h8 : authorizedCaller = s.sender <;> simp_tydro
    by_cases h9 : signedNonce = nonceOf s <;> simp_tydro
    by_cases h10 : recoveredSigner = ownerOf s <;> simp_tydro
    by_cases hov : nonceOf s = TydroPositionAccount.maxUint256 <;> simp_tydro

theorem open_typed_fields_are_source_bounded
    (eModeCategory : Uint256) (s : ContractState) :
    open_typed_fields_spec eModeCategory s := by
  unfold open_typed_fields_spec
  intro h
  by_cases hwidth : eModeCategory.val ≤ (255 : Uint256).val
  · exact hwidth
  · simp [TydroPositionAccount.checkOpenTypedFields, hwidth] at h
    simp_tydro

theorem signed_open_success_respects_floor_and_authority
    (account owner pool supplyAsset borrowAsset authorizedCaller : Address)
    (intentNonce intentDeadline : Uint256)
    (route : Address) (routeConfigHash : Uint256) (assetIn : Address)
    (amountIn maxAmountIn : Uint256) (assetOut : Address) (minAmountOut : Uint256)
    (recipient : Address) (conversionDeadline routeDataHash : Uint256)
    (debtToken : Address)
    (initialCollateralAmount eModeCategory flashLoanAmount minSuppliedTokenAmount
      maxBorrowedTokenAmount minHealthFactor : Uint256)
    (digest signature : Uint256) (recoveredSigner : Address)
    (measuredAmountOut suppliedTokenAmount borrowedTokenAmount healthFactor : Uint256)
    (finalPoolSettlementSucceeds : Bool) (s : ContractState) :
    signed_open_floor_authority_spec account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken initialCollateralAmount
      eModeCategory flashLoanAmount minSuppliedTokenAmount maxBorrowedTokenAmount minHealthFactor
      digest signature recoveredSigner measuredAmountOut suppliedTokenAmount borrowedTokenAmount
      healthFactor finalPoolSettlementSucceeds s := by
  unfold signed_open_floor_authority_spec
  dsimp only
  unfold openStagesSucceed
  rintro ⟨hdigest, hrecovery, htypedFields, hlifecycle, hfloors⟩
  have heModeWidthProof := open_typed_fields_are_source_bounded eModeCategory s
  unfold open_typed_fields_spec at heModeWidthProof
  have heModeWidth := heModeWidthProof htypedFields
  have hauthority := lifecycle_success_requires_owner_authority account owner pool supplyAsset
    borrowAsset authorizedCaller intentNonce intentDeadline recoveredSigner s
  unfold lifecycle_authority_spec at hauthority
  dsimp only at hauthority
  rcases hauthority hlifecycle with
    ⟨haccount, howner, hpool, hsupply, hborrow, hdeadline, hcaller, hnonce, hsigner,
      hnoncePost⟩
  have hfloor := open_enforces_signed_floors minAmountOut measuredAmountOut
    minSuppliedTokenAmount suppliedTokenAmount maxBorrowedTokenAmount borrowedTokenAmount
    minHealthFactor healthFactor finalPoolSettlementSucceeds
    (((TydroPositionAccount.consumeLifecycleAuthority account owner pool supplyAsset borrowAsset
      authorizedCaller intentNonce intentDeadline recoveredSigner).run s).snd)
  unfold open_floor_spec at hfloor
  rcases hfloor hfloors with ⟨hout, hsupplied, hborrowed, hhealth⟩
  unfold signedOpenBoundaryHolds lifecycleAuthorityHolds openFloorBoundsHold
  exact ⟨hdigest, hrecovery, heModeWidth,
    ⟨haccount, howner, hpool, hsupply, hborrow, hdeadline, hcaller, hnonce, hsigner, hnoncePost⟩,
    ⟨hout, hsupplied, hborrowed, hhealth⟩⟩

theorem signed_close_success_respects_floor_and_authority
    (account owner pool supplyAsset borrowAsset authorizedCaller : Address)
    (intentNonce intentDeadline : Uint256)
    (route : Address) (routeConfigHash : Uint256) (assetIn : Address)
    (amountIn maxAmountIn : Uint256) (assetOut : Address) (minAmountOut : Uint256)
    (recipient : Address) (conversionDeadline routeDataHash : Uint256)
    (debtToken : Address)
    (maxRepayAmount maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt
      maxRemainingCollateral minHealthFactor : Uint256)
    (residualReceiver : Address)
    (digest signature : Uint256) (recoveredSigner : Address)
    (withdrawnAmount measuredAmountOut remainingDebt remainingCollateral healthFactor : Uint256)
    (finalPoolSettlementSucceeds : Bool) (s : ContractState) :
    signed_close_floor_authority_spec account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken maxRepayAmount
      maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt maxRemainingCollateral
      minHealthFactor residualReceiver digest signature recoveredSigner withdrawnAmount
      measuredAmountOut remainingDebt remainingCollateral healthFactor
      finalPoolSettlementSucceeds s := by
  unfold signed_close_floor_authority_spec
  dsimp only
  unfold closeStagesSucceed
  rintro ⟨hdigest, hrecovery, hlifecycle, hfloors⟩
  have hauthority := lifecycle_success_requires_owner_authority account owner pool supplyAsset
    borrowAsset authorizedCaller intentNonce intentDeadline recoveredSigner s
  unfold lifecycle_authority_spec at hauthority
  dsimp only at hauthority
  rcases hauthority hlifecycle with
    ⟨haccount, howner, hpool, hsupply, hborrow, hdeadline, hcaller, hnonce, hsigner,
      hnoncePost⟩
  have hfloor := close_enforces_signed_floors minWithdrawAmount withdrawnAmount minAmountOut
    measuredAmountOut maxRemainingDebt remainingDebt maxRemainingCollateral remainingCollateral
    minHealthFactor healthFactor finalPoolSettlementSucceeds
    (((TydroPositionAccount.consumeLifecycleAuthority account owner pool supplyAsset borrowAsset
      authorizedCaller intentNonce intentDeadline recoveredSigner).run s).snd)
  unfold close_floor_spec at hfloor
  rcases hfloor hfloors with ⟨hwithdrawn, hout, hdebt, hhealth, hcollateral⟩
  unfold signedCloseBoundaryHolds lifecycleAuthorityHolds closeFloorBoundsHold
  exact ⟨hdigest, hrecovery,
    ⟨haccount, howner, hpool, hsupply, hborrow, hdeadline, hcaller, hnonce, hsigner, hnoncePost⟩,
    ⟨hwithdrawn, hout, hdebt, hhealth, hcollateral⟩⟩

 theorem callback_success_requires_bound_context
    (initiator asset : Address) (paramsHash : Uint256) (effectsSucceed : Bool)
    (s : ContractState) : callback_authority_spec initiator asset paramsHash effectsSucceed s := by
  unfold callback_authority_spec
  dsimp only
  intro h
  by_cases h1 : s.sender = poolOf s <;> simp_tydro
  by_cases h2 : initiator = s.thisAddress <;> simp_tydro
  by_cases h3 : asset = borrowAssetOf s <;> simp_tydro
  by_cases h4 : activeHashOf s = 0 <;> simp_tydro
  by_cases h5 : activeKindOf s = 1
  · simp_tydro
    by_cases h7 : paramsHash = activeHashOf s <;> simp_tydro
    by_cases h8 : effectsSucceed = true <;> simp_tydro
  · simp_tydro
    by_cases h6 : activeKindOf s = 2 <;> simp_tydro
    by_cases h7 : paramsHash = activeHashOf s <;> simp_tydro
    by_cases h8 : effectsSucceed = true <;> simp_tydro

 theorem emode_success_requires_owner
    (category : Uint256) (poolSucceeds : Bool) (s : ContractState) :
    emode_authority_spec category poolSucceeds s := by
  unfold emode_authority_spec
  dsimp only
  intro h
  by_cases h1 : s.sender = ownerOf s <;> simp_tydro
  by_cases h2 : category.val ≤ (255 : Uint256).val <;> simp_tydro
  by_cases h3 : poolSucceeds = true <;> simp_tydro

 theorem atoken_recovery_requires_owner
    (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) :
    atoken_authority_spec amount transferSucceeds s := by
  unfold atoken_authority_spec
  dsimp only
  intro h
  by_cases h1 : s.sender = ownerOf s <;> simp_tydro
  by_cases h2 : amount = 0 <;> simp_tydro
  by_cases h3 : transferSucceeds = true <;> simp_tydro

 theorem raw_supply_recovery_requires_owner
    (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) :
    raw_supply_authority_spec amount transferSucceeds s := by
  unfold raw_supply_authority_spec
  dsimp only
  intro h
  by_cases h1 : s.sender = ownerOf s <;> simp_tydro
  by_cases h2 : amount = 0 <;> simp_tydro
  by_cases h3 : transferSucceeds = true <;> simp_tydro

 theorem raw_borrow_recovery_requires_owner
    (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) :
    raw_borrow_authority_spec amount transferSucceeds s := by
  unfold raw_borrow_authority_spec
  dsimp only
  intro h
  by_cases h1 : s.sender = ownerOf s <;> simp_tydro
  by_cases h2 : amount = 0 <;> simp_tydro
  by_cases h3 : transferSucceeds = true <;> simp_tydro

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
