import Contracts.Common
import Verity.Stdlib.Math

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts hiding ite blockTimestamp

abbrev requireSomeUint := Verity.Stdlib.Math.requireSomeUint
abbrev safeAdd := Verity.Stdlib.Math.safeAdd

/-!
`bytes32` digests, `bytes` signatures, EIP-712 encoding, Keccak-256, and ECDSA recovery
are represented here by `Uint256` values and opaque trusted functions.  These functions
are deliberately outside `verity_contract`: they are an explicit cryptographic abstraction,
not an executable model or an axiom about cryptographic correctness.  Every Solidity struct
field encoded by `_hashIntentCommonStruct`, `_hashConversionLegStruct`, `_hashOpenIntent`,
and `_hashCloseIntent` is an argument of the corresponding digest function.
-/
opaque trustedOpenIntentDigest
    (account owner pool supplyAsset borrowAsset authorizedCaller : Address)
    (intentNonce intentDeadline : Uint256)
    (route : Address) (routeConfigHash : Uint256) (assetIn : Address)
    (amountIn maxAmountIn : Uint256) (assetOut : Address) (minAmountOut : Uint256)
    (recipient : Address) (conversionDeadline routeDataHash : Uint256)
    (debtToken : Address)
    (initialCollateralAmount eModeCategory flashLoanAmount minSuppliedTokenAmount
      maxBorrowedTokenAmount minHealthFactor : Uint256) : Uint256

opaque trustedCloseIntentDigest
    (account owner pool supplyAsset borrowAsset authorizedCaller : Address)
    (intentNonce intentDeadline : Uint256)
    (route : Address) (routeConfigHash : Uint256) (assetIn : Address)
    (amountIn maxAmountIn : Uint256) (assetOut : Address) (minAmountOut : Uint256)
    (recipient : Address) (conversionDeadline routeDataHash : Uint256)
    (debtToken : Address)
    (maxRepayAmount maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt
      maxRemainingCollateral minHealthFactor : Uint256)
    (residualReceiver : Address) : Uint256

opaque trustedRecover (digest signature : Uint256) : Address

/-!
A focused Verity model of the source-enforced floor and authority checks in
`TydroPositionAccount.sol`, from the public Ink Blockscout verified factory bundle at
`0xc3cd1e023a596066270E43Eb5399B1DB445D0286`.

The selected slices are the successful-return guards, not the superseded swap-route case.
External Aave, route, token, EIP-712 hashing, and ECDSA behavior are explicit inputs. Thus
`recoveredSigner` and measured post-operation values must be connected to the real external
systems by review; no cryptographic, oracle, Aave-accounting, or bytecode refinement claim is
made. The callback slots are ordinary model slots standing for the source's transaction-local
EIP-1153 cells; the one-shot ordering inside the modeled call is preserved.
-/

verity_contract TydroPositionAccount where
  storage
    nonce : Uint256 := slot 0
    activeCallbackHash : Uint256 := slot 1
    activeCallbackKind : Uint256 := slot 2
    effectObservedActiveHash : Uint256 := slot 3
    callbackCompletionKind : Uint256 := slot 4
    modeledEModeCategory : Uint256 := slot 5
    aTokenRecoveryRecipient : Address := slot 6
    rawSupplyRecoveryRecipient : Address := slot 7
    rawBorrowRecoveryRecipient : Address := slot 8

  constants
    maxUint256 : Uint256 :=
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

  immutables
    immutableOwner : Address := zeroAddress
    immutablePool : Address := zeroAddress
    immutableSupplyAsset : Address := zeroAddress
    immutableBorrowAsset : Address := zeroAddress

  /- ABI/source-type boundary for `OpenIntent.eModeCategory : uint8`. -/
  function checkOpenTypedFields (eModeCategory : Uint256) : Unit := do
    require (eModeCategory <= 255) "InvalidUint8EModeCategory"

  /- Source checks after a successful open callback and before final Pool settlement. -/
  function checkOpenFloors
      (minAmountOut : Uint256, measuredAmountOut : Uint256,
       minSuppliedTokenAmount : Uint256, suppliedTokenAmount : Uint256,
       maxBorrowedTokenAmount : Uint256, borrowedTokenAmount : Uint256,
       minHealthFactor : Uint256, healthFactor : Uint256,
       finalPoolSettlementSucceeds : Bool) : Unit := do
    require (measuredAmountOut >= minAmountOut) "InsufficientOutput"
    require (suppliedTokenAmount >= minSuppliedTokenAmount) "SuppliedAmountBelowMinimum"
    require (borrowedTokenAmount <= maxBorrowedTokenAmount) "BorrowedAmountAboveMaximum"
    require (healthFactor >= minHealthFactor) "HealthFactorTooLow"
    require finalPoolSettlementSucceeds "PoolSettlementFailed"

  /- Source checks after close execution. The health floor is unconditional in Solidity. -/
  function checkCloseFloors
      (minWithdrawAmount : Uint256, withdrawnAmount : Uint256,
       minAmountOut : Uint256, measuredAmountOut : Uint256,
       maxRemainingDebt : Uint256, remainingDebt : Uint256,
       maxRemainingCollateral : Uint256, remainingCollateral : Uint256,
       minHealthFactor : Uint256, healthFactor : Uint256,
       finalPoolSettlementSucceeds : Bool) : Unit := do
    require (withdrawnAmount >= minWithdrawAmount) "WithdrawBelowMinimum"
    require (measuredAmountOut >= minAmountOut) "InsufficientOutput"
    require (remainingDebt <= maxRemainingDebt) "RemainingDebtTooHigh"
    require (healthFactor >= minHealthFactor) "HealthFactorTooLow"
    require (remainingCollateral <= maxRemainingCollateral) "RemainingCollateralTooHigh"
    require finalPoolSettlementSucceeds "PoolSettlementFailed"

  /- Common open/close lifecycle authority boundary; the operation-specific signed digest is
     represented by `recoveredSigner`, an explicit cryptographic boundary input. -/
  function consumeLifecycleAuthority
      (signedAccount : Address, signedOwner : Address, signedPool : Address,
       signedSupplyAsset : Address, signedBorrowAsset : Address,
       authorizedCaller : Address, signedNonce : Uint256, deadline : Uint256,
       recoveredSigner : Address) : Unit := do
    let self ← Verity.contractAddress
    let caller ← msgSender
    let now ← blockTimestamp
    require (signedAccount == self) "InvalidLifecycleIntent(account)"
    require (signedOwner == immutableOwner) "InvalidLifecycleIntent(owner)"
    require (signedPool == immutablePool) "InvalidLifecycleIntent(pool)"
    require (signedSupplyAsset == immutableSupplyAsset) "InvalidLifecycleIntent(supplyAsset)"
    require (signedBorrowAsset == immutableBorrowAsset) "InvalidLifecycleIntent(borrowAsset)"
    require (now <= deadline) "IntentExpired"
    require (authorizedCaller == zeroAddress || authorizedCaller == caller)
      "Unauthorized(relayer)"
    let expectedNonce ← getStorage nonce
    require (signedNonce == expectedNonce) "InvalidNonce"
    require (recoveredSigner == immutableOwner) "InvalidSignature"
    require (expectedNonce != maxUint256) "Panic(0x11)"
    setStorage nonce (add expectedNonce 1)

  /- `executeOperation` authority and one-shot active-context slice. -/
  function executeOperationAuthority
      (initiator : Address, asset : Address, paramsHash : Uint256,
       effectsSucceed : Bool) : Bool := do
    let self ← Verity.contractAddress
    let caller ← msgSender
    require (caller == immutablePool) "Unauthorized(pool)"
    require (initiator == self) "Unauthorized(initiator)"
    require (asset == immutableBorrowAsset) "InvalidCallbackAsset"
    let activeHash ← getStorage activeCallbackHash
    let activeKind ← getStorage activeCallbackKind
    require (activeHash != 0) "UnexpectedCallback"
    require (activeKind == 1 || activeKind == 2) "InvalidCallbackKind"
    require (paramsHash == activeHash) "InvalidCallbackHash"
    setStorage activeCallbackHash 0
    setStorage activeCallbackKind 0
    let observed ← getStorage activeCallbackHash
    setStorage effectObservedActiveHash observed
    require effectsSucceed "CallbackEffectFailed"
    setStorage callbackCompletionKind activeKind
    return true

  function setEModeCategory (categoryId : Uint256, poolCallSucceeds : Bool) : Unit := do
    let caller ← msgSender
    require (caller == immutableOwner) "Unauthorized(owner)"
    require (categoryId <= 255) "InvalidUint8Category"
    require poolCallSucceeds "PoolSetEModeFailed"
    setStorage modeledEModeCategory categoryId

  function claimATokens (claimedAmount : Uint256, transferSucceeds : Bool) : Uint256 := do
    let caller ← msgSender
    require (caller == immutableOwner) "Unauthorized(owner)"
    require (claimedAmount != 0) "InvalidAmount"
    require transferSucceeds "ATokenTransferFailed"
    setStorageAddr aTokenRecoveryRecipient immutableOwner
    return claimedAmount

  function claimRawSupply (amount : Uint256, transferSucceeds : Bool) : Uint256 := do
    let caller ← msgSender
    require (caller == immutableOwner) "Unauthorized(owner)"
    require (amount != 0) "InvalidAmount"
    require transferSucceeds "SupplyTransferFailed"
    setStorageAddr rawSupplyRecoveryRecipient immutableOwner
    return amount

  function claimRawBorrow (amount : Uint256, transferSucceeds : Bool) : Uint256 := do
    let caller ← msgSender
    require (caller == immutableOwner) "Unauthorized(owner)"
    require (amount != 0) "InvalidAmount"
    require transferSucceeds "BorrowTransferFailed"
    setStorageAddr rawBorrowRecoveryRecipient immutableOwner
    return amount

namespace TydroPositionAccount

/- Source-shaped correspondence witness for the signed-open stages used by the
   stage-composition theorem; the theorem reasons from each successful stage directly. -/
def executeSignedOpenBoundary
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
    (finalPoolSettlementSucceeds : Bool) : Contract Unit := do
  Verity.require
    (digest == trustedOpenIntentDigest account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken initialCollateralAmount
      eModeCategory flashLoanAmount minSuppliedTokenAmount maxBorrowedTokenAmount minHealthFactor)
    "InvalidOpenIntentDigest"
  Verity.require (recoveredSigner == trustedRecover digest signature)
    "InvalidRecoveredSigner"
  checkOpenTypedFields eModeCategory
  consumeLifecycleAuthority account owner pool supplyAsset borrowAsset authorizedCaller
    intentNonce intentDeadline recoveredSigner
  checkOpenFloors minAmountOut measuredAmountOut minSuppliedTokenAmount suppliedTokenAmount
    maxBorrowedTokenAmount borrowedTokenAmount minHealthFactor healthFactor
    finalPoolSettlementSucceeds

/- Source-shaped correspondence witness for the signed-close stages used by the
   stage-composition theorem.  The close health floor remains unconditional. -/
def executeSignedCloseBoundary
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
    (finalPoolSettlementSucceeds : Bool) : Contract Unit := do
  Verity.require
    (digest == trustedCloseIntentDigest account owner pool supplyAsset borrowAsset authorizedCaller
      intentNonce intentDeadline route routeConfigHash assetIn amountIn maxAmountIn assetOut
      minAmountOut recipient conversionDeadline routeDataHash debtToken maxRepayAmount
      maxFlashLoanRepayment minWithdrawAmount maxRemainingDebt maxRemainingCollateral
      minHealthFactor residualReceiver)
    "InvalidCloseIntentDigest"
  Verity.require (recoveredSigner == trustedRecover digest signature)
    "InvalidRecoveredSigner"
  consumeLifecycleAuthority account owner pool supplyAsset borrowAsset authorizedCaller
    intentNonce intentDeadline recoveredSigner
  checkCloseFloors minWithdrawAmount withdrawnAmount minAmountOut measuredAmountOut
    maxRemainingDebt remainingDebt maxRemainingCollateral remainingCollateral minHealthFactor
    healthFactor finalPoolSettlementSucceeds

end TydroPositionAccount

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
