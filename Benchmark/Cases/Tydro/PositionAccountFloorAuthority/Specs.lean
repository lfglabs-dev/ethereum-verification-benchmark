import Verity.Specs.Common
import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Contract

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

abbrev OwnerSlot := TydroPositionAccount.__verity_immutable_slot_immutableOwner.slot
abbrev PoolSlot := TydroPositionAccount.__verity_immutable_slot_immutablePool.slot
abbrev SupplyAssetSlot := TydroPositionAccount.__verity_immutable_slot_immutableSupplyAsset.slot
abbrev BorrowAssetSlot := TydroPositionAccount.__verity_immutable_slot_immutableBorrowAsset.slot

def ownerOf (s : ContractState) : Address := s.storageAddr OwnerSlot
def poolOf (s : ContractState) : Address := s.storageAddr PoolSlot
def supplyAssetOf (s : ContractState) : Address := s.storageAddr SupplyAssetSlot
def borrowAssetOf (s : ContractState) : Address := s.storageAddr BorrowAssetSlot
def nonceOf (s : ContractState) : Uint256 := s.storage 0
def activeHashOf (s : ContractState) : Uint256 := s.storage 1
def activeKindOf (s : ContractState) : Uint256 := s.storage 2
def observedActiveHashOf (s : ContractState) : Uint256 := s.storage 3
def completionKindOf (s : ContractState) : Uint256 := s.storage 4
def eModeOf (s : ContractState) : Uint256 := s.storage 5
def aTokenRecipientOf (s : ContractState) : Address := s.storageAddr 6
def rawSupplyRecipientOf (s : ContractState) : Address := s.storageAddr 7
def rawBorrowRecipientOf (s : ContractState) : Address := s.storageAddr 8

def open_floor_spec
    (minOut out minSupply supplied maxBorrowed borrowed minHealth health : Uint256)
    (settles : Bool) (s : ContractState) : Prop :=
  ((TydroPositionAccount.checkOpenFloors minOut out minSupply supplied maxBorrowed borrowed
      minHealth health settles).run s).isSuccess = true →
    out >= minOut ∧ supplied >= minSupply ∧ borrowed <= maxBorrowed ∧ health >= minHealth

def close_floor_spec
    (minWithdraw withdrawn minOut out maxDebt debt maxCollateral collateral minHealth health : Uint256)
    (settles : Bool) (s : ContractState) : Prop :=
  ((TydroPositionAccount.checkCloseFloors minWithdraw withdrawn minOut out maxDebt debt
      maxCollateral collateral minHealth health settles).run s).isSuccess = true →
    withdrawn >= minWithdraw ∧ out >= minOut ∧ debt <= maxDebt ∧
    health >= minHealth ∧ collateral <= maxCollateral

def lifecycle_authority_spec
    (signedAccount signedOwner signedPool signedSupply signedBorrow authorizedCaller : Address)
    (signedNonce deadline : Uint256) (recoveredSigner : Address) (s : ContractState) : Prop :=
  let post := ((TydroPositionAccount.consumeLifecycleAuthority signedAccount signedOwner signedPool
    signedSupply signedBorrow authorizedCaller signedNonce deadline recoveredSigner).run s).snd
  ((TydroPositionAccount.consumeLifecycleAuthority signedAccount signedOwner signedPool signedSupply
    signedBorrow authorizedCaller signedNonce deadline recoveredSigner).run s).isSuccess = true →
    signedAccount = s.thisAddress ∧ signedOwner = ownerOf s ∧ signedPool = poolOf s ∧
    signedSupply = supplyAssetOf s ∧ signedBorrow = borrowAssetOf s ∧
    s.blockTimestamp <= deadline ∧
    (authorizedCaller = zeroAddress ∨ authorizedCaller = s.sender) ∧
    signedNonce = nonceOf s ∧ recoveredSigner = ownerOf s ∧ nonceOf post = add (nonceOf s) 1

def open_typed_fields_spec (eModeCategory : Uint256) (s : ContractState) : Prop :=
  ((TydroPositionAccount.checkOpenTypedFields eModeCategory).run s).isSuccess = true →
    eModeCategory.val ≤ (255 : Uint256).val

def signed_open_floor_authority_spec
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
    (finalPoolSettlementSucceeds : Bool) (s : ContractState) : Prop :=
  let typedFields := TydroPositionAccount.checkOpenTypedFields eModeCategory
  let lifecycle := TydroPositionAccount.consumeLifecycleAuthority account owner pool supplyAsset
    borrowAsset authorizedCaller intentNonce intentDeadline recoveredSigner
  let post := (lifecycle.run s).snd
  let floors := TydroPositionAccount.checkOpenFloors minAmountOut measuredAmountOut
    minSuppliedTokenAmount suppliedTokenAmount maxBorrowedTokenAmount borrowedTokenAmount
    minHealthFactor healthFactor finalPoolSettlementSucceeds
  (digest = trustedOpenIntentDigest account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken initialCollateralAmount
      eModeCategory flashLoanAmount minSuppliedTokenAmount maxBorrowedTokenAmount minHealthFactor ∧
    recoveredSigner = trustedRecover digest signature ∧
    (typedFields.run s).isSuccess = true ∧
    (lifecycle.run s).isSuccess = true ∧
    (floors.run post).isSuccess = true) →
    digest = trustedOpenIntentDigest account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken initialCollateralAmount
      eModeCategory flashLoanAmount minSuppliedTokenAmount maxBorrowedTokenAmount minHealthFactor ∧
    recoveredSigner = trustedRecover digest signature ∧
    eModeCategory.val ≤ (255 : Uint256).val ∧
    account = s.thisAddress ∧ owner = ownerOf s ∧ pool = poolOf s ∧
    supplyAsset = supplyAssetOf s ∧ borrowAsset = borrowAssetOf s ∧
    s.blockTimestamp <= intentDeadline ∧
    (authorizedCaller = zeroAddress ∨ authorizedCaller = s.sender) ∧
    intentNonce = nonceOf s ∧ recoveredSigner = ownerOf s ∧
    nonceOf post = add (nonceOf s) 1 ∧
    measuredAmountOut >= minAmountOut ∧
    suppliedTokenAmount >= minSuppliedTokenAmount ∧
    borrowedTokenAmount <= maxBorrowedTokenAmount ∧
    healthFactor >= minHealthFactor

def signed_close_floor_authority_spec
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
    (finalPoolSettlementSucceeds : Bool) (s : ContractState) : Prop :=
  let lifecycle := TydroPositionAccount.consumeLifecycleAuthority account owner pool supplyAsset
    borrowAsset authorizedCaller intentNonce intentDeadline recoveredSigner
  let post := (lifecycle.run s).snd
  let floors := TydroPositionAccount.checkCloseFloors minWithdrawAmount withdrawnAmount
    minAmountOut measuredAmountOut maxRemainingDebt remainingDebt maxRemainingCollateral
    remainingCollateral minHealthFactor healthFactor finalPoolSettlementSucceeds
  (digest = trustedCloseIntentDigest account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken maxRepayAmount
      maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt maxRemainingCollateral
      minHealthFactor residualReceiver ∧
    recoveredSigner = trustedRecover digest signature ∧
    (lifecycle.run s).isSuccess = true ∧
    (floors.run post).isSuccess = true) →
    digest = trustedCloseIntentDigest account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken maxRepayAmount
      maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt maxRemainingCollateral
      minHealthFactor residualReceiver ∧
    recoveredSigner = trustedRecover digest signature ∧
    account = s.thisAddress ∧ owner = ownerOf s ∧ pool = poolOf s ∧
    supplyAsset = supplyAssetOf s ∧ borrowAsset = borrowAssetOf s ∧
    s.blockTimestamp <= intentDeadline ∧
    (authorizedCaller = zeroAddress ∨ authorizedCaller = s.sender) ∧
    intentNonce = nonceOf s ∧ recoveredSigner = ownerOf s ∧
    nonceOf post = add (nonceOf s) 1 ∧
    withdrawnAmount >= minWithdrawAmount ∧ measuredAmountOut >= minAmountOut ∧
    remainingDebt <= maxRemainingDebt ∧ healthFactor >= minHealthFactor ∧
    remainingCollateral <= maxRemainingCollateral

def callback_authority_spec
    (initiator asset : Address) (paramsHash : Uint256) (effectsSucceed : Bool)
    (s : ContractState) : Prop :=
  let post := ((TydroPositionAccount.executeOperationAuthority initiator asset paramsHash
    effectsSucceed).run s).snd
  ((TydroPositionAccount.executeOperationAuthority initiator asset paramsHash
    effectsSucceed).run s).isSuccess = true →
    s.sender = poolOf s ∧ initiator = s.thisAddress ∧ asset = borrowAssetOf s ∧
    activeHashOf s != 0 ∧ (activeKindOf s = 1 ∨ activeKindOf s = 2) ∧
    paramsHash = activeHashOf s ∧ activeHashOf post = 0 ∧ activeKindOf post = 0 ∧
    observedActiveHashOf post = 0 ∧ completionKindOf post = activeKindOf s

def emode_authority_spec (category : Uint256) (poolSucceeds : Bool) (s : ContractState) : Prop :=
  let post := ((TydroPositionAccount.setEModeCategory category poolSucceeds).run s).snd
  ((TydroPositionAccount.setEModeCategory category poolSucceeds).run s).isSuccess = true →
    s.sender = ownerOf s ∧ eModeOf post = category

def atoken_authority_spec (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) : Prop :=
  let post := ((TydroPositionAccount.claimATokens amount transferSucceeds).run s).snd
  ((TydroPositionAccount.claimATokens amount transferSucceeds).run s).isSuccess = true →
    s.sender = ownerOf s ∧ aTokenRecipientOf post = ownerOf s

def raw_supply_authority_spec (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) : Prop :=
  let post := ((TydroPositionAccount.claimRawSupply amount transferSucceeds).run s).snd
  ((TydroPositionAccount.claimRawSupply amount transferSucceeds).run s).isSuccess = true →
    s.sender = ownerOf s ∧ rawSupplyRecipientOf post = ownerOf s

def raw_borrow_authority_spec (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) : Prop :=
  let post := ((TydroPositionAccount.claimRawBorrow amount transferSucceeds).run s).snd
  ((TydroPositionAccount.claimRawBorrow amount transferSucceeds).run s).isSuccess = true →
    s.sender = ownerOf s ∧ rawBorrowRecipientOf post = ownerOf s

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
