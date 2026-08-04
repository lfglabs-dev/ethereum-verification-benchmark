import Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Automation
open Verity.Proofs.Stdlib.Math (safeAdd_some safeSub_some)

set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
set_option compiler.extract_closed false
set_option compiler.maxRecInline 0
set_option compiler.maxRecInlineIfReduce 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem totalAssetsStoredSlot : BorrowLiquiditySafety.totalAssetsStored.slot = 0 := by native_decide
private theorem isClosedSlot : BorrowLiquiditySafety.isClosed.slot = 1 := by native_decide
private theorem accruedProtocolFeesSlot : BorrowLiquiditySafety.accruedProtocolFees.slot = 2 := by native_decide
private theorem normalizedUnclaimedWithdrawalsSlot :
    BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot = 3 := by native_decide
private theorem scaledTotalSupplySlot : BorrowLiquiditySafety.scaledTotalSupply.slot = 4 := by native_decide
private theorem scaledPendingWithdrawalsSlot :
    BorrowLiquiditySafety.scaledPendingWithdrawals.slot = 5 := by native_decide
private theorem reserveRatioBipsSlot : BorrowLiquiditySafety.reserveRatioBips.slot = 6 := by native_decide
private theorem scaleFactorSlot : BorrowLiquiditySafety.scaleFactor.slot = 7 := by native_decide
private theorem pendingProtocolFeeDeltaSlot :
    BorrowLiquiditySafety.pendingProtocolFeeDelta.slot = 8 := by native_decide
private theorem borrowerFlaggedSlot : BorrowLiquiditySafety.borrowerFlagged.slot = 9 := by native_decide
private theorem hookAllowsBorrowSlot : BorrowLiquiditySafety.hookAllowsBorrow.slot = 10 := by native_decide

attribute [local simp] totalAssetsStoredSlot isClosedSlot accruedProtocolFeesSlot
  normalizedUnclaimedWithdrawalsSlot scaledTotalSupplySlot scaledPendingWithdrawalsSlot
  reserveRatioBipsSlot scaleFactorSlot pendingProtocolFeeDeltaSlot borrowerFlaggedSlot
  hookAllowsBorrowSlot
attribute [local simp] BIP HALF_BIP RAY HALF_RAY

private theorem uint256_add_notation (a b : Uint256) : a + b = add a b := rfl
private theorem uint256_sub_notation (a b : Uint256) : a - b = sub a b := rfl
private theorem uint256_mul_notation (a b : Uint256) : a * b = mul a b := rfl
private theorem uint256_div_notation (a b : Uint256) : a / b = div a b := rfl

attribute [local simp] uint256_add_notation uint256_sub_notation
  uint256_mul_notation uint256_div_notation

private def updatedFeesExpr' (s : ContractState) : Uint256 :=
  s.storage 2 + s.storage 8

private def scaledOutstandingExpr' (s : ContractState) : Uint256 :=
  s.storage 4 - s.storage 5

private def reserveNumeratorExpr' (s : ContractState) : Uint256 :=
  scaledOutstandingExpr' s * s.storage 6 + HALF_BIP

private def scaledRequiredExpr' (s : ContractState) : Uint256 :=
  reserveNumeratorExpr' s / BIP + s.storage 5

private def normalizeNumeratorExpr' (s : ContractState) : Uint256 :=
  scaledRequiredExpr' s * s.storage 7 + HALF_RAY

private def normalizedRequiredExpr' (s : ContractState) : Uint256 :=
  normalizeNumeratorExpr' s / RAY

private def liquidityRequiredExpr' (s : ContractState) : Uint256 :=
  normalizedRequiredExpr' s + updatedFeesExpr' s + s.storage 3

private theorem updatedFees_eq (s : ContractState) :
    updatedFeesExpr' s = updatedAccruedProtocolFeesOf s := rfl

private theorem scaledRequired_eq (s : ContractState) :
    scaledRequiredExpr' s = scaledRequiredReservesOf s := by
  unfold scaledRequiredExpr' scaledRequiredReservesOf reserveNumeratorExpr'
    scaledOutstandingExpr' scaledOutstandingSupplyOf outstandingSupply bipMulHalfUp
    scaledPendingWithdrawalsOf reserveRatioBipsOf scaledTotalSupplyOf
  rw [Verity.Core.Uint256.add_comm]

private theorem normalizedRequired_eq (s : ContractState) :
    normalizedRequiredExpr' s = normalizedRequiredReservesOf s := by
  unfold normalizedRequiredExpr' normalizedRequiredReservesOf normalizeAmount rayMulHalfUp
    normalizeNumeratorExpr' scaleFactorOf
  rw [scaledRequired_eq, Verity.Core.Uint256.mul_comm]

private theorem liquidityRequired_eq (s : ContractState) :
    liquidityRequiredExpr' s = requiredLiquidityAfterUpdate s := by
  calc
    liquidityRequiredExpr' s
      = normalizedRequiredExpr' s + updatedFeesExpr' s + s.storage 3 := rfl
    _ = normalizedRequiredReservesOf s + updatedAccruedProtocolFeesOf s + s.storage 3 := by
      rw [normalizedRequired_eq s, updatedFees_eq s]
    _ = normalizeAmount (scaledRequiredReservesOf s) (scaleFactorOf s) +
          updatedAccruedProtocolFeesOf s + normalizedUnclaimedWithdrawalsOf s := by
      rfl
    _ = requiredLiquidityAfterUpdate s := by
      rfl

private theorem borrowerFlagged_raw
    (preState : ContractState)
    (hFlaggedSlot : borrowerFlaggedOf preState = 0) :
    preState.storage BorrowLiquiditySafety.borrowerFlagged.slot = 0 := by
  simpa [borrowerFlaggedOf] using hFlaggedSlot

private theorem isClosed_raw
    (preState : ContractState)
    (hClosedSlot : isClosedOf preState = 0) :
    preState.storage BorrowLiquiditySafety.isClosed.slot = 0 := by
  simpa [isClosedOf] using hClosedSlot

private theorem hookAllowsBorrow_raw
    (preState : ContractState)
    (hHookSlot : hookAllowsBorrowOf preState != 0) :
    preState.storage BorrowLiquiditySafety.hookAllowsBorrow.slot != 0 := by
  simpa [hookAllowsBorrowOf] using hHookSlot

private structure BorrowReads where
  totalAssets : Uint256
  isClosed : Uint256
  accruedProtocolFees : Uint256
  normalizedUnclaimedWithdrawals : Uint256
  scaledTotalSupply : Uint256
  scaledPendingWithdrawals : Uint256
  reserveRatioBips : Uint256
  scaleFactor : Uint256
  pendingProtocolFeeDelta : Uint256
  hookAllowsBorrow : Uint256

private def readsOf (s : ContractState) : BorrowReads where
  totalAssets := s.storage BorrowLiquiditySafety.totalAssetsStored.slot
  isClosed := s.storage BorrowLiquiditySafety.isClosed.slot
  accruedProtocolFees := s.storage BorrowLiquiditySafety.accruedProtocolFees.slot
  normalizedUnclaimedWithdrawals :=
    s.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot
  scaledTotalSupply := s.storage BorrowLiquiditySafety.scaledTotalSupply.slot
  scaledPendingWithdrawals := s.storage BorrowLiquiditySafety.scaledPendingWithdrawals.slot
  reserveRatioBips := s.storage BorrowLiquiditySafety.reserveRatioBips.slot
  scaleFactor := s.storage BorrowLiquiditySafety.scaleFactor.slot
  pendingProtocolFeeDelta := s.storage BorrowLiquiditySafety.pendingProtocolFeeDelta.slot
  hookAllowsBorrow := s.storage BorrowLiquiditySafety.hookAllowsBorrow.slot

private def readBorrowInputs : Contract BorrowReads := do
  let totalAssets_ ← getStorage BorrowLiquiditySafety.totalAssetsStored
  let isClosed_ ← getStorage BorrowLiquiditySafety.isClosed
  let accruedProtocolFees_ ← getStorage BorrowLiquiditySafety.accruedProtocolFees
  let normalizedUnclaimedWithdrawals_ ←
    getStorage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals
  let scaledTotalSupply_ ← getStorage BorrowLiquiditySafety.scaledTotalSupply
  let scaledPendingWithdrawals_ ← getStorage BorrowLiquiditySafety.scaledPendingWithdrawals
  let reserveRatioBips_ ← getStorage BorrowLiquiditySafety.reserveRatioBips
  let scaleFactor_ ← getStorage BorrowLiquiditySafety.scaleFactor
  let pendingProtocolFeeDelta_ ← getStorage BorrowLiquiditySafety.pendingProtocolFeeDelta
  let hookAllowsBorrow_ ← getStorage BorrowLiquiditySafety.hookAllowsBorrow
  Verity.pure {
    totalAssets := totalAssets_
    isClosed := isClosed_
    accruedProtocolFees := accruedProtocolFees_
    normalizedUnclaimedWithdrawals := normalizedUnclaimedWithdrawals_
    scaledTotalSupply := scaledTotalSupply_
    scaledPendingWithdrawals := scaledPendingWithdrawals_
    reserveRatioBips := reserveRatioBips_
    scaleFactor := scaleFactor_
    pendingProtocolFeeDelta := pendingProtocolFeeDelta_
    hookAllowsBorrow := hookAllowsBorrow_
  }

private theorem readBorrowInputs_run (preState : ContractState) :
    readBorrowInputs.run preState = ContractResult.success (readsOf preState) preState := by
  unfold readBorrowInputs readsOf
  simp [Bind.bind, Verity.bind, Contract.run, getStorage, Verity.pure]

private def borrowTailAfterLiquidityRequiredFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityRequired_ : Uint256) : Contract Unit := do
  let borrowable_ := ite (r.totalAssets > liquidityRequired_) (sub r.totalAssets liquidityRequired_) 0
  require (amount <= borrowable_) "BorrowAmountTooHigh"
  require (r.hookAllowsBorrow != 0) "BorrowHookFailed"
  setStorage BorrowLiquiditySafety.totalAssetsStored (sub r.totalAssets amount)
  setStorage BorrowLiquiditySafety.accruedProtocolFees updatedAccruedProtocolFees_
  setStorage BorrowLiquiditySafety.pendingProtocolFeeDelta 0

private def borrowTailAfterLiquidityWithFeesFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ : Uint256) : Contract Unit := do
  let liquidityRequired_ ← requireSomeUint
    (safeAdd liquidityWithFees_ r.normalizedUnclaimedWithdrawals)
    "LiquidityRequirementOverflow"
  borrowTailAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_ liquidityRequired_

private def borrowTailAfterNormalizedNumeratorFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ : Uint256) : Contract Unit := do
  let normalizedRequiredLiquidity_ := div normalizedNumerator_ 1000000000000000000000000000
  let liquidityWithFees_ ← requireSomeUint
    (safeAdd normalizedRequiredLiquidity_ updatedAccruedProtocolFees_)
    "LiquidityRequirementOverflow"
  borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_ liquidityWithFees_

private def borrowTailAfterReserveFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ reserveNumerator_ : Uint256) : Contract Unit := do
  let scaledReserveRatioRequirement_ := div reserveNumerator_ 10000
  let scaledRequiredLiquidity_ := add scaledReserveRatioRequirement_ r.scaledPendingWithdrawals
  let normalizedNumerator_ ← requireSomeUint
    (safeAdd (mul scaledRequiredLiquidity_ r.scaleFactor) 500000000000000000000000000)
    "NormalizeAmountOverflow"
  borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_ normalizedNumerator_

private def borrowTailAfterOutstandingFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256) : Contract Unit := do
  let reserveProduct_ := mul scaledOutstandingSupply_ r.reserveRatioBips
  let reserveNumerator_ ← requireSomeUint
    (safeAdd reserveProduct_ 5000)
    "ReserveRequirementOverflow"
  borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_ reserveNumerator_

private def borrowTailAfterUpdatedFeesFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ : Uint256) : Contract Unit := do
  let scaledOutstandingSupply_ ← requireSomeUint
    (safeSub r.scaledTotalSupply r.scaledPendingWithdrawals)
    "OutstandingSupplyUnderflow"
  borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_ scaledOutstandingSupply_

private def borrowTailFromReads (amount : Uint256) (r : BorrowReads) : Contract Unit := do
  let updatedAccruedProtocolFees_ ← requireSomeUint
    (safeAdd r.accruedProtocolFees r.pendingProtocolFeeDelta)
    "ProtocolFeeOverflow"
  require (r.isClosed == 0) "BorrowFromClosedMarket"
  borrowTailAfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_

private def borrowAfterBorrowerCheck (amount : Uint256) : Contract Unit := do
  let r ← readBorrowInputs
  borrowTailFromReads amount r

private def borrowerFlagPrefix : Contract Unit := do
  let borrowerFlagged_ ← getStorage BorrowLiquiditySafety.borrowerFlagged
  require (borrowerFlagged_ == 0) "BorrowWhileSanctioned"

private def borrowFactored (amount : Uint256) : Contract Unit := do
  borrowerFlagPrefix
  let r ← readBorrowInputs
  borrowTailFromReads amount r

private theorem borrow_eq_factored (amount : Uint256) :
    BorrowLiquiditySafety.borrow amount = borrowFactored amount := by
  rfl

private theorem bind_runState_of_success_same
    {α β : Type} (m : Contract α) (k : α → Contract β) (s : ContractState) (a : α)
    (h : m.run s = ContractResult.success a s) :
    (Verity.bind m k).runState s = (k a).runState s := by
  unfold Contract.run at h
  cases hm : m s <;> simp [Verity.bind, Contract.runState, hm] at h ⊢
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem borrowerFlagPrefix_run
    (preState : ContractState)
    (hFlaggedSlot : borrowerFlaggedOf preState = 0) :
    borrowerFlagPrefix.run preState = ContractResult.success () preState := by
  have hFlaggedRaw := borrowerFlagged_raw preState hFlaggedSlot
  simp only [borrowerFlaggedSlot] at hFlaggedRaw
  unfold borrowerFlagPrefix Contract.run getStorage require
  simp [Bind.bind, Verity.bind, hFlaggedRaw]

private theorem borrow_reduces_to_borrowAfterBorrowerCheck
    (amount : Uint256) (preState : ContractState)
    (hFlaggedSlot : borrowerFlaggedOf preState = 0) :
    (BorrowLiquiditySafety.borrow amount).runState preState =
      (borrowAfterBorrowerCheck amount).runState preState := by
  rw [borrow_eq_factored]
  unfold borrowFactored
  change (Verity.bind borrowerFlagPrefix
      (fun _ => borrowAfterBorrowerCheck amount)).runState preState = _
  exact
    (bind_runState_of_success_same borrowerFlagPrefix
      (fun _ => borrowAfterBorrowerCheck amount) preState ()
      (borrowerFlagPrefix_run preState hFlaggedSlot))

private theorem borrow_reduces_to_tailFromReads
    (amount : Uint256) (preState : ContractState)
    (hFlaggedSlot : borrowerFlaggedOf preState = 0) :
    (BorrowLiquiditySafety.borrow amount).runState preState =
      (borrowTailFromReads amount (readsOf preState)).runState preState := by
  rw [borrow_reduces_to_borrowAfterBorrowerCheck amount preState hFlaggedSlot]
  unfold borrowAfterBorrowerCheck
  change (Verity.bind readBorrowInputs
      (fun r => borrowTailFromReads amount r)).runState preState = _
  exact
    (bind_runState_of_success_same readBorrowInputs
      (fun r => borrowTailFromReads amount r) preState (readsOf preState)
      (readBorrowInputs_run preState))

private theorem updatedFees_some
    (preState : ContractState)
    (hFees :
      (accruedProtocolFeesOf preState : Nat) + (pendingProtocolFeeDeltaOf preState : Nat) <= MAX_UINT256) :
    safeAdd
      (preState.storage BorrowLiquiditySafety.accruedProtocolFees.slot)
      (preState.storage BorrowLiquiditySafety.pendingProtocolFeeDelta.slot) =
      some (updatedFeesExpr' preState) := by
  simpa [updatedFeesExpr'] using
    (safeAdd_some (preState.storage 2) (preState.storage 8) hFees)

private theorem outstanding_some
    (preState : ContractState)
    (hPendingLeTotal : scaledPendingWithdrawalsOf preState <= scaledTotalSupplyOf preState) :
    safeSub
      (preState.storage BorrowLiquiditySafety.scaledTotalSupply.slot)
      (preState.storage BorrowLiquiditySafety.scaledPendingWithdrawals.slot) =
      some (scaledOutstandingExpr' preState) := by
  simpa [scaledOutstandingExpr', outstandingSupply] using
    (safeSub_some (preState.storage 4) (preState.storage 5) hPendingLeTotal)

private theorem reserveNumerator_some
    (preState : ContractState)
    (hPendingLeTotal : scaledPendingWithdrawalsOf preState <= scaledTotalSupplyOf preState)
    (hReserve :
      (scaledOutstandingSupplyOf preState : Nat) * (reserveRatioBipsOf preState : Nat) + (HALF_BIP : Nat)
        <= MAX_UINT256) :
    safeAdd
      (mul (scaledOutstandingExpr' preState)
        (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot))
      5000 = some (reserveNumeratorExpr' preState) := by
  have hReserveBound :
      ((scaledOutstandingExpr' preState : Nat) *
          (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot : Nat)) +
        (HALF_BIP : Nat) <= MAX_UINT256 := by
    simpa [scaledOutstandingExpr', scaledOutstandingSupplyOf, outstandingSupply,
      scaledTotalSupplyOf, scaledPendingWithdrawalsOf, reserveRatioBipsOf] using hReserve
  have hReserveMulLt :
      (scaledOutstandingExpr' preState : Nat) *
          (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot : Nat) <
        Verity.Core.Uint256.modulus := by
    have h' :
        (scaledOutstandingExpr' preState : Nat) *
            (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot : Nat) <
          MAX_UINT256 + 1 := by
      omega
    simpa [Verity.Proofs.Stdlib.Automation.modulus_eq_max_uint256_succ] using h'
  have hReserveMulVal :
      ((mul (scaledOutstandingExpr' preState)
          (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot) : Uint256) : Nat) =
        (scaledOutstandingExpr' preState : Nat) *
          (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot : Nat) := by
    simpa [mul] using Verity.Core.Uint256.mul_eq_of_lt hReserveMulLt
  have hReserveBound' :
      ((mul (scaledOutstandingExpr' preState)
          (preState.storage BorrowLiquiditySafety.reserveRatioBips.slot) : Uint256) : Nat) +
        (HALF_BIP : Nat) <= MAX_UINT256 := by
    rw [hReserveMulVal]
    exact hReserveBound
  simpa [reserveNumeratorExpr', HALF_BIP] using
    (safeAdd_some
      (scaledOutstandingExpr' preState * preState.storage BorrowLiquiditySafety.reserveRatioBips.slot)
      HALF_BIP
      hReserveBound')

private theorem normalizeNumerator_some_expanded
    (preState : ContractState)
    (hPendingLeTotal : scaledPendingWithdrawalsOf preState <= scaledTotalSupplyOf preState)
    (hReserve :
      (scaledOutstandingSupplyOf preState : Nat) * (reserveRatioBipsOf preState : Nat) + (HALF_BIP : Nat)
        <= MAX_UINT256)
    (hNormalize :
      (scaledRequiredReservesOf preState : Nat) * (scaleFactorOf preState : Nat) + (HALF_RAY : Nat)
        <= MAX_UINT256) :
    safeAdd
      (mul
        (add (div (reserveNumeratorExpr' preState) 10000)
          (preState.storage BorrowLiquiditySafety.scaledPendingWithdrawals.slot))
        (preState.storage BorrowLiquiditySafety.scaleFactor.slot))
      500000000000000000000000000 = some (normalizeNumeratorExpr' preState) := by
  have hNormalizeBound :
      ((scaledRequiredExpr' preState : Nat) *
          (preState.storage BorrowLiquiditySafety.scaleFactor.slot : Nat)) +
        (HALF_RAY : Nat) <= MAX_UINT256 := by
    simpa [normalizeNumeratorExpr', scaledRequired_eq preState, scaleFactorOf] using hNormalize
  have hNormalizeMulLt :
      (scaledRequiredExpr' preState : Nat) *
          (preState.storage BorrowLiquiditySafety.scaleFactor.slot : Nat) <
        Verity.Core.Uint256.modulus := by
    have h' :
        (scaledRequiredExpr' preState : Nat) *
            (preState.storage BorrowLiquiditySafety.scaleFactor.slot : Nat) <
          MAX_UINT256 + 1 := by
      omega
    simpa [Verity.Proofs.Stdlib.Automation.modulus_eq_max_uint256_succ] using h'
  have hNormalizeMulVal :
      ((mul (scaledRequiredExpr' preState)
          (preState.storage BorrowLiquiditySafety.scaleFactor.slot) : Uint256) : Nat) =
        (scaledRequiredExpr' preState : Nat) *
          (preState.storage BorrowLiquiditySafety.scaleFactor.slot : Nat) := by
    simpa [mul] using Verity.Core.Uint256.mul_eq_of_lt hNormalizeMulLt
  have hNormalizeBound' :
      ((mul (scaledRequiredExpr' preState)
          (preState.storage BorrowLiquiditySafety.scaleFactor.slot) : Uint256) : Nat) +
        (HALF_RAY : Nat) <= MAX_UINT256 := by
    rw [hNormalizeMulVal]
    exact hNormalizeBound
  have hNormalizeNumeratorRaw :
      safeAdd
        (mul (scaledRequiredExpr' preState)
          (preState.storage BorrowLiquiditySafety.scaleFactor.slot))
        500000000000000000000000000 = some (normalizeNumeratorExpr' preState) := by
    simpa [normalizeNumeratorExpr', HALF_RAY] using
      (safeAdd_some
        (scaledRequiredExpr' preState * preState.storage BorrowLiquiditySafety.scaleFactor.slot)
        HALF_RAY
        hNormalizeBound')
  simpa [scaledRequiredExpr'] using hNormalizeNumeratorRaw

private theorem liquidityWithFees_some_expanded
    (preState : ContractState)
    (hPendingLeTotal : scaledPendingWithdrawalsOf preState <= scaledTotalSupplyOf preState)
    (hReserve :
      (scaledOutstandingSupplyOf preState : Nat) * (reserveRatioBipsOf preState : Nat) + (HALF_BIP : Nat)
        <= MAX_UINT256)
    (hNormalize :
      (scaledRequiredReservesOf preState : Nat) * (scaleFactorOf preState : Nat) + (HALF_RAY : Nat)
        <= MAX_UINT256)
    (hLiquidityWithFees :
      (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat)
        <= MAX_UINT256) :
    safeAdd (div (normalizeNumeratorExpr' preState) 1000000000000000000000000000) (updatedFeesExpr' preState) =
      some (normalizedRequiredExpr' preState + updatedFeesExpr' preState) := by
  have hLiquidityWithFeesBound :
      (normalizedRequiredExpr' preState : Nat) + (updatedFeesExpr' preState : Nat) <= MAX_UINT256 := by
    simpa [normalizedRequired_eq preState, updatedFees_eq preState] using hLiquidityWithFees
  have hLiquidityWithFeesRaw :
      safeAdd (normalizedRequiredExpr' preState) (updatedFeesExpr' preState) =
        some (normalizedRequiredExpr' preState + updatedFeesExpr' preState) := by
    simpa using
      (safeAdd_some (normalizedRequiredExpr' preState) (updatedFeesExpr' preState)
        hLiquidityWithFeesBound)
  simpa [normalizedRequiredExpr'] using hLiquidityWithFeesRaw

private theorem liquidityRequired_some
    (preState : ContractState)
    (hPendingLeTotal : scaledPendingWithdrawalsOf preState <= scaledTotalSupplyOf preState)
    (hReserve :
      (scaledOutstandingSupplyOf preState : Nat) * (reserveRatioBipsOf preState : Nat) + (HALF_BIP : Nat)
        <= MAX_UINT256)
    (hNormalize :
      (scaledRequiredReservesOf preState : Nat) * (scaleFactorOf preState : Nat) + (HALF_RAY : Nat)
        <= MAX_UINT256)
    (hLiquidityWithFees :
      (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat)
        <= MAX_UINT256)
    (hLiquidityRequiredTotal :
      (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat) +
          (normalizedUnclaimedWithdrawalsOf preState : Nat) <= MAX_UINT256) :
    safeAdd
      (normalizedRequiredExpr' preState + updatedFeesExpr' preState)
      (preState.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot) =
      some (liquidityRequiredExpr' preState) := by
  have hUnclaimedVal :
      (preState.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot : Nat) =
        (preState.storage 3 : Nat) := by
    rfl
  have hLiquidityWithFeesBound :
      (normalizedRequiredExpr' preState : Nat) + (updatedFeesExpr' preState : Nat) <= MAX_UINT256 := by
    simpa [normalizedRequired_eq preState, updatedFees_eq preState] using hLiquidityWithFees
  have hLiquidityWithFeesRaw :
      safeAdd (normalizedRequiredExpr' preState) (updatedFeesExpr' preState) =
        some (normalizedRequiredExpr' preState + updatedFeesExpr' preState) := by
    simpa using
      (safeAdd_some (normalizedRequiredExpr' preState) (updatedFeesExpr' preState)
        hLiquidityWithFeesBound)
  have hLiquidityWithFeesLt :
      (normalizedRequiredExpr' preState : Nat) + (updatedFeesExpr' preState : Nat) <
        Verity.Core.Uint256.modulus := by
    have h' :
        (normalizedRequiredExpr' preState : Nat) + (updatedFeesExpr' preState : Nat) <
          MAX_UINT256 + 1 := by
      omega
    simpa [Verity.Proofs.Stdlib.Automation.modulus_eq_max_uint256_succ] using h'
  have hLiquidityWithFeesVal :
      (((normalizedRequiredExpr' preState + updatedFeesExpr' preState : Uint256)) : Nat) =
        (normalizedRequiredExpr' preState : Nat) + (updatedFeesExpr' preState : Nat) := by
    simpa using Verity.Core.Uint256.add_eq_of_lt hLiquidityWithFeesLt
  have hLiquidityRequiredBound :
      ((normalizedRequiredExpr' preState + updatedFeesExpr' preState : Uint256) : Nat) +
        (preState.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot : Nat) <=
          MAX_UINT256 := by
    calc
      ((normalizedRequiredExpr' preState + updatedFeesExpr' preState : Uint256) : Nat) +
          (preState.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot : Nat)
          =
        ((normalizedRequiredExpr' preState : Nat) + (updatedFeesExpr' preState : Nat)) +
          (preState.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot : Nat) := by
            rw [hLiquidityWithFeesVal]
      _ =
        (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat) +
          (preState.storage 3 : Nat) := by
            rw [normalizedRequired_eq preState, updatedFees_eq preState]
            simpa [Nat.add_assoc] using
              congrArg
                (fun n : Nat =>
                  (normalizedRequiredReservesOf preState : Nat) +
                    (updatedAccruedProtocolFeesOf preState : Nat) + n)
                hUnclaimedVal
      _ =
        (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat) +
          (normalizedUnclaimedWithdrawalsOf preState : Nat) := by
            change
              (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat) +
                  (preState.storage 3 : Nat) =
                (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat) +
                  (normalizedUnclaimedWithdrawalsOf preState : Nat)
            rw [show (normalizedUnclaimedWithdrawalsOf preState : Nat) = (preState.storage 3 : Nat) by
              exact hUnclaimedVal.symm]
      _ <= MAX_UINT256 := hLiquidityRequiredTotal
  simpa [liquidityRequiredExpr', Verity.Core.Uint256.add_assoc] using
    (safeAdd_some
      (normalizedRequiredExpr' preState + updatedFeesExpr' preState)
      (preState.storage BorrowLiquiditySafety.normalizedUnclaimedWithdrawals.slot)
      hLiquidityRequiredBound)

private theorem amountGuard
    (amount : Uint256) (preState : ContractState)
    (hAmount : amount <= borrowableAssetsAfterUpdate preState) :
    amount <=
      ite (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot > liquidityRequiredExpr' preState)
        (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot - liquidityRequiredExpr' preState)
        0 := by
  have hAmount' : amount <=
      ite (totalAssetsOf preState > requiredLiquidityAfterUpdate preState)
        (totalAssetsOf preState - requiredLiquidityAfterUpdate preState) 0 := by
    simpa [borrowableAssetsAfterUpdate, borrowableAssetsFromFields,
      requiredLiquidityAfterUpdate, satSub] using hAmount
  simpa [totalAssetsOf, liquidityRequired_eq preState] using hAmount'

private def slot0WrittenValue (amount : Uint256) (preState : ContractState) : Uint256 :=
  if 0 = BorrowLiquiditySafety.pendingProtocolFeeDelta.slot then 0
  else if 0 = BorrowLiquiditySafety.accruedProtocolFees.slot then updatedFeesExpr' preState
  else if 0 = BorrowLiquiditySafety.totalAssetsStored.slot then
    sub (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot) amount
  else
    preState.storage 0

private def borrowTailWithLiquidity (amount : Uint256) (preState : ContractState) : Contract Unit :=
  borrowTailAfterLiquidityRequiredFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (liquidityRequiredExpr' preState)

private def borrowTailAfterLiquidityWithFees (amount : Uint256) (preState : ContractState) : Contract Unit :=
  borrowTailAfterLiquidityWithFeesFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (normalizedRequiredExpr' preState + updatedFeesExpr' preState)

private def borrowTailAfterNormalizedNumerator (amount : Uint256) (preState : ContractState) : Contract Unit :=
  borrowTailAfterNormalizedNumeratorFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (normalizeNumeratorExpr' preState)

private def borrowTailAfterReserve (amount : Uint256) (preState : ContractState) : Contract Unit :=
  borrowTailAfterReserveFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (reserveNumeratorExpr' preState)

private def borrowTailAfterOutstanding (amount : Uint256) (preState : ContractState) : Contract Unit :=
  borrowTailAfterOutstandingFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (scaledOutstandingExpr' preState)

private def borrowTailAfterUpdatedFees (amount : Uint256) (preState : ContractState) : Contract Unit :=
  borrowTailAfterUpdatedFeesFromReads amount (readsOf preState) (updatedFeesExpr' preState)

@[irreducible] private def stateAfterUpdatedFeesFromReads
    (amount : Uint256) (r : BorrowReads) (updatedAccruedProtocolFees_ : Uint256)
    (s : ContractState) : ContractState :=
  (borrowTailAfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_).runState s

@[irreducible] private def stateAfterOutstandingFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256)
    (s : ContractState) : ContractState :=
  (borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
    scaledOutstandingSupply_).runState s

@[irreducible] private def stateAfterReserveFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ reserveNumerator_ : Uint256)
    (s : ContractState) : ContractState :=
  (borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_
    reserveNumerator_).runState s

@[irreducible] private def stateAfterLiquidityRequiredFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityRequired_ : Uint256)
    (s : ContractState) : ContractState :=
  (borrowTailAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
    liquidityRequired_).runState s

@[irreducible] private def stateAfterNormalizedNumeratorFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ : Uint256)
    (s : ContractState) : ContractState :=
  (borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
    normalizedNumerator_).runState s

@[irreducible] private def stateAfterLiquidityWithFeesFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ : Uint256)
    (s : ContractState) : ContractState :=
  (borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
    liquidityWithFees_).runState s

@[irreducible] private def slot0OfState (s : ContractState) : Uint256 :=
  s.storage 0

@[irreducible] private def slot0AfterUpdatedFeesFromReads
    (amount : Uint256) (r : BorrowReads) (updatedAccruedProtocolFees_ : Uint256)
    (s : ContractState) : Uint256 :=
  slot0OfState (stateAfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_ s)

@[irreducible] private def slot0AfterOutstandingFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256)
    (s : ContractState) : Uint256 :=
  slot0OfState (stateAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
    scaledOutstandingSupply_ s)

@[irreducible] private def slot0AfterReserveFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ reserveNumerator_ : Uint256)
    (s : ContractState) : Uint256 :=
  slot0OfState (stateAfterReserveFromReads amount r updatedAccruedProtocolFees_
    reserveNumerator_ s)

@[irreducible] private def slot0AfterLiquidityRequiredFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityRequired_ : Uint256)
    (s : ContractState) : Uint256 :=
  slot0OfState (stateAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
    liquidityRequired_ s)

@[irreducible] private def slot0AfterNormalizedNumeratorFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ : Uint256)
    (s : ContractState) : Uint256 :=
  slot0OfState (stateAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
    normalizedNumerator_ s)

@[irreducible] private def slot0AfterLiquidityWithFeesFromReads
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ : Uint256)
    (s : ContractState) : Uint256 :=
  slot0OfState (stateAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
    liquidityWithFees_ s)

@[irreducible] private def slot0AfterUpdatedFees (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0AfterUpdatedFeesFromReads amount (readsOf preState) (updatedFeesExpr' preState) preState

@[irreducible] private def slot0AfterOutstanding (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0AfterOutstandingFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (scaledOutstandingExpr' preState) preState

@[irreducible] private def slot0AfterReserve (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0AfterReserveFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (reserveNumeratorExpr' preState) preState

@[irreducible] private def slot0AfterLiquidityTail (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0AfterLiquidityRequiredFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (liquidityRequiredExpr' preState) preState

@[irreducible] private def slot0AfterNormalizedNumerator (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0AfterNormalizedNumeratorFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (normalizeNumeratorExpr' preState) preState

@[irreducible] private def slot0AfterLiquidityWithFees (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0AfterLiquidityWithFeesFromReads amount (readsOf preState)
    (updatedFeesExpr' preState)
    (normalizedRequiredExpr' preState + updatedFeesExpr' preState) preState

@[irreducible] private def reserveNumeratorSomeExpr (preState : ContractState) : Prop :=
  safeAdd
    (mul (scaledOutstandingExpr' preState) (readsOf preState).reserveRatioBips)
    5000 = some (reserveNumeratorExpr' preState)

@[irreducible] private def normalizeNumeratorSomeExpr (preState : ContractState) : Prop :=
  safeAdd
    (mul
      (add (div (reserveNumeratorExpr' preState) 10000)
        (readsOf preState).scaledPendingWithdrawals)
      (readsOf preState).scaleFactor)
    500000000000000000000000000 = some (normalizeNumeratorExpr' preState)

@[irreducible] private def liquidityWithFeesSomeExpr (preState : ContractState) : Prop :=
  safeAdd (div (normalizeNumeratorExpr' preState) 1000000000000000000000000000)
    (updatedFeesExpr' preState) =
  some (normalizedRequiredExpr' preState + updatedFeesExpr' preState)

@[irreducible] private def liquidityRequiredSomeExpr (preState : ContractState) : Prop :=
  safeAdd (normalizedRequiredExpr' preState + updatedFeesExpr' preState)
    (readsOf preState).normalizedUnclaimedWithdrawals =
  some (liquidityRequiredExpr' preState)

@[irreducible] private def slot0AfterLiquidityWrites (amount : Uint256) (preState : ContractState) : Uint256 :=
  ((do
      setStorage BorrowLiquiditySafety.totalAssetsStored
        (sub (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot) amount)
      setStorage BorrowLiquiditySafety.accruedProtocolFees (updatedFeesExpr' preState)
      setStorage BorrowLiquiditySafety.pendingProtocolFeeDelta 0).run preState).snd.storage 0

private def slot0WriteChain (amount : Uint256) (preState : ContractState) : Contract Unit :=
  Verity.bind
    (setStorage BorrowLiquiditySafety.totalAssetsStored
      (sub (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot) amount))
    (fun _ =>
      Verity.bind
        (setStorage BorrowLiquiditySafety.accruedProtocolFees (updatedFeesExpr' preState))
        (fun _ => setStorage BorrowLiquiditySafety.pendingProtocolFeeDelta 0))

private def liquidityAmountGuard (amount : Uint256) (preState : ContractState) : Bool :=
  decide
    ((amount : Nat) <=
      ((if (liquidityRequiredExpr' preState : Nat) <
          (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot : Nat) then
        sub (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot)
          (liquidityRequiredExpr' preState)
      else 0 : Uint256) : Nat))

private def liquidityMidContract (amount : Uint256) (preState : ContractState) : Contract Unit :=
  Verity.bind
    (require (liquidityAmountGuard amount preState) "BorrowAmountTooHigh")
    (fun _ => Verity.bind (require true "BorrowHookFailed") (fun _ => slot0WriteChain amount preState))

@[irreducible] private def stateAfterReserveMid (amount : Uint256) (preState : ContractState) : ContractState :=
  (liquidityMidContract amount preState).runState preState

@[irreducible] private def slot0AfterReserveMid (amount : Uint256) (preState : ContractState) : Uint256 :=
  slot0OfState (stateAfterReserveMid amount preState)

@[irreducible] private def stateAfterLiquidityGuardedWrites (amount : Uint256) (preState : ContractState) :
    ContractState :=
  (match
      match
        if liquidityAmountGuard amount preState then
          ContractResult.success () preState
        else
          ContractResult.revert "BorrowAmountTooHigh" preState with
      | ContractResult.success _ s' =>
        slot0WriteChain amount preState s'
      | ContractResult.revert msg s' => ContractResult.revert msg s' with
    | ContractResult.success a s' => ContractResult.success a s'
    | ContractResult.revert msg _ => ContractResult.revert msg preState).snd

@[irreducible] private def slot0AfterLiquidityGuardedWrites (amount : Uint256) (preState : ContractState) :
    Uint256 :=
  slot0OfState (stateAfterLiquidityGuardedWrites amount preState)

private theorem storage0_of_runState_eq
    {α β : Type} {c : Contract α} {d : Contract β} {s : ContractState}
    (h : c.runState s = d.runState s) :
    (c.run s).snd.storage 0 = (d.run s).snd.storage 0 := by
  simpa [Contract.runState_eq_snd_run] using
    congrArg (fun s' : ContractState => s'.storage 0) h

private theorem requireSomeUint_run_of_eq
    {opt : Option Uint256} {value : Uint256} {msg : String} {s : ContractState}
    (h : opt = some value) :
    (requireSomeUint opt msg).run s = ContractResult.success value s := by
  cases h
  rfl

private theorem rollback_snd_eq {α : Type} (r : ContractResult α) (preState : ContractState) :
    (match r with
    | ContractResult.success _ s' => s'
    | ContractResult.revert _ _ => preState) =
      (match r with
      | ContractResult.success a s' => ContractResult.success a s'
      | ContractResult.revert msg _ => ContractResult.revert msg preState).snd := by
  cases r <;> rfl

private theorem borrowTailAfterUpdatedFeesFromReads_runState_of_outstanding
    (amount : Uint256) (r : BorrowReads) (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256)
    (s : ContractState)
    (hOutstanding :
      safeSub r.scaledTotalSupply r.scaledPendingWithdrawals = some scaledOutstandingSupply_) :
    (borrowTailAfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_).runState s =
      (borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
        scaledOutstandingSupply_).runState s := by
  unfold borrowTailAfterUpdatedFeesFromReads
  exact
    bind_runState_of_success_same
      (requireSomeUint (safeSub r.scaledTotalSupply r.scaledPendingWithdrawals)
        "OutstandingSupplyUnderflow")
      (fun scaledOutstandingSupply_ =>
        borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
          scaledOutstandingSupply_)
      s scaledOutstandingSupply_ (requireSomeUint_run_of_eq hOutstanding)

private theorem borrowTailAfterOutstandingFromReads_runState_of_reserveNumerator
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ scaledOutstandingSupply_ reserveNumerator_ : Uint256)
    (s : ContractState)
    (hReserveNumerator :
      safeAdd (mul scaledOutstandingSupply_ r.reserveRatioBips) 5000 = some reserveNumerator_) :
    (borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
      scaledOutstandingSupply_).runState s =
      (borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_
        reserveNumerator_).runState s := by
  unfold borrowTailAfterOutstandingFromReads
  exact
    bind_runState_of_success_same
      (requireSomeUint (safeAdd (mul scaledOutstandingSupply_ r.reserveRatioBips) 5000)
        "ReserveRequirementOverflow")
      (fun reserveNumerator_ =>
        borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_ reserveNumerator_)
      s reserveNumerator_ (requireSomeUint_run_of_eq hReserveNumerator)

private theorem borrowTailAfterReserveFromReads_runState_of_normalizeNumerator
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ reserveNumerator_ normalizedNumerator_ : Uint256)
    (s : ContractState)
    (hNormalizeNumerator :
      safeAdd
        (mul (add (div reserveNumerator_ 10000) r.scaledPendingWithdrawals) r.scaleFactor)
        500000000000000000000000000 = some normalizedNumerator_) :
    (borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_
      reserveNumerator_).runState s =
      (borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
        normalizedNumerator_).runState s := by
  unfold borrowTailAfterReserveFromReads
  exact
    bind_runState_of_success_same
      (requireSomeUint
        (safeAdd
          (mul (add (div reserveNumerator_ 10000) r.scaledPendingWithdrawals) r.scaleFactor)
          500000000000000000000000000)
        "NormalizeAmountOverflow")
      (fun normalizedNumerator_ =>
        borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
          normalizedNumerator_)
      s normalizedNumerator_ (requireSomeUint_run_of_eq hNormalizeNumerator)

private theorem borrowTailAfterNormalizedNumeratorFromReads_runState_of_liquidityWithFees
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ : Uint256)
    (s : ContractState)
    (hLiquidityWithFees :
      safeAdd (div normalizedNumerator_ 1000000000000000000000000000)
        updatedAccruedProtocolFees_ = some liquidityWithFees_) :
    (borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
      normalizedNumerator_).runState s =
      (borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
        liquidityWithFees_).runState s := by
  unfold borrowTailAfterNormalizedNumeratorFromReads
  exact
    bind_runState_of_success_same
      (requireSomeUint
        (safeAdd (div normalizedNumerator_ 1000000000000000000000000000)
          updatedAccruedProtocolFees_)
        "LiquidityRequirementOverflow")
      (fun liquidityWithFees_ =>
        borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
          liquidityWithFees_)
      s liquidityWithFees_ (requireSomeUint_run_of_eq hLiquidityWithFees)

private theorem borrowTailAfterLiquidityWithFeesFromReads_runState_of_liquidityRequired
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ : Uint256)
    (s : ContractState)
    (hLiquidityRequired :
      safeAdd liquidityWithFees_ r.normalizedUnclaimedWithdrawals = some liquidityRequired_) :
    (borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
      liquidityWithFees_).runState s =
      (borrowTailAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
        liquidityRequired_).runState s := by
  unfold borrowTailAfterLiquidityWithFeesFromReads
  exact
    bind_runState_of_success_same
      (requireSomeUint (safeAdd liquidityWithFees_ r.normalizedUnclaimedWithdrawals)
        "LiquidityRequirementOverflow")
      (fun liquidityRequired_ =>
        borrowTailAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
          liquidityRequired_)
      s liquidityRequired_ (requireSomeUint_run_of_eq hLiquidityRequired)

private theorem stateAfterUpdatedFeesFromReads_reduces_to_afterOutstanding
    (amount : Uint256) (r : BorrowReads) (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256)
    (s : ContractState)
    (hOutstanding :
      safeSub r.scaledTotalSupply r.scaledPendingWithdrawals = some scaledOutstandingSupply_) :
    stateAfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_ s =
      stateAfterOutstandingFromReads amount r updatedAccruedProtocolFees_ scaledOutstandingSupply_ s := by
  unfold stateAfterUpdatedFeesFromReads stateAfterOutstandingFromReads
  exact
    borrowTailAfterUpdatedFeesFromReads_runState_of_outstanding amount r
      updatedAccruedProtocolFees_ scaledOutstandingSupply_ s hOutstanding

private theorem stateAfterOutstandingFromReads_reduces_to_afterReserve
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ scaledOutstandingSupply_ reserveNumerator_ : Uint256)
    (s : ContractState)
    (hReserveNumerator :
      safeAdd (mul scaledOutstandingSupply_ r.reserveRatioBips) 5000 = some reserveNumerator_) :
    stateAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
      scaledOutstandingSupply_ s =
      stateAfterReserveFromReads amount r updatedAccruedProtocolFees_
        reserveNumerator_ s := by
  unfold stateAfterOutstandingFromReads stateAfterReserveFromReads
  exact
    borrowTailAfterOutstandingFromReads_runState_of_reserveNumerator amount r
      updatedAccruedProtocolFees_ scaledOutstandingSupply_ reserveNumerator_ s hReserveNumerator

private theorem stateAfterReserveFromReads_reduces_to_afterNormalizedNumerator
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ reserveNumerator_ normalizedNumerator_ : Uint256)
    (s : ContractState)
    (hNormalizeNumerator :
      safeAdd
        (mul (add (div reserveNumerator_ 10000) r.scaledPendingWithdrawals) r.scaleFactor)
        500000000000000000000000000 = some normalizedNumerator_) :
    stateAfterReserveFromReads amount r updatedAccruedProtocolFees_
      reserveNumerator_ s =
      stateAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
        normalizedNumerator_ s := by
  unfold stateAfterReserveFromReads stateAfterNormalizedNumeratorFromReads
  exact
    borrowTailAfterReserveFromReads_runState_of_normalizeNumerator amount r
      updatedAccruedProtocolFees_ reserveNumerator_ normalizedNumerator_ s hNormalizeNumerator

private theorem stateAfterNormalizedNumeratorFromReads_reduces_to_afterLiquidityWithFees
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ : Uint256)
    (s : ContractState)
    (hLiquidityWithFees :
      safeAdd (div normalizedNumerator_ 1000000000000000000000000000)
        updatedAccruedProtocolFees_ = some liquidityWithFees_) :
    stateAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
      normalizedNumerator_ s =
      stateAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
        liquidityWithFees_ s := by
  unfold stateAfterNormalizedNumeratorFromReads stateAfterLiquidityWithFeesFromReads
  exact
    borrowTailAfterNormalizedNumeratorFromReads_runState_of_liquidityWithFees amount r
      updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ s hLiquidityWithFees

private theorem stateAfterLiquidityWithFeesFromReads_reduces_to_afterLiquidityRequired
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ : Uint256)
    (s : ContractState)
    (hLiquidityRequired :
      safeAdd liquidityWithFees_ r.normalizedUnclaimedWithdrawals = some liquidityRequired_) :
    stateAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
      liquidityWithFees_ s =
      stateAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
        liquidityRequired_ s := by
  unfold stateAfterLiquidityWithFeesFromReads stateAfterLiquidityRequiredFromReads
  exact
    borrowTailAfterLiquidityWithFeesFromReads_runState_of_liquidityRequired amount r
      updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ s hLiquidityRequired

private theorem borrowTailAfterUpdatedFeesFromReads_slot0_of_outstanding
    (amount : Uint256) (r : BorrowReads) (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256)
    (s : ContractState)
    (hOutstanding :
      safeSub r.scaledTotalSupply r.scaledPendingWithdrawals = some scaledOutstandingSupply_) :
    ((borrowTailAfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_).run s).snd.storage 0 =
      ((borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
        scaledOutstandingSupply_).run s).snd.storage 0 :=
  storage0_of_runState_eq
    (borrowTailAfterUpdatedFeesFromReads_runState_of_outstanding amount r
      updatedAccruedProtocolFees_ scaledOutstandingSupply_ s hOutstanding)

private theorem borrowTailAfterOutstandingFromReads_slot0_of_reserveNumerator
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ scaledOutstandingSupply_ reserveNumerator_ : Uint256)
    (s : ContractState)
    (hReserveNumerator :
      safeAdd (mul scaledOutstandingSupply_ r.reserveRatioBips) 5000 = some reserveNumerator_) :
    ((borrowTailAfterOutstandingFromReads amount r updatedAccruedProtocolFees_
      scaledOutstandingSupply_).run s).snd.storage 0 =
      ((borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_
        reserveNumerator_).run s).snd.storage 0 :=
  storage0_of_runState_eq
    (borrowTailAfterOutstandingFromReads_runState_of_reserveNumerator amount r
      updatedAccruedProtocolFees_ scaledOutstandingSupply_ reserveNumerator_ s hReserveNumerator)

private theorem borrowTailAfterReserveFromReads_slot0_of_normalizeNumerator
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ reserveNumerator_ normalizedNumerator_ : Uint256)
    (s : ContractState)
    (hNormalizeNumerator :
      safeAdd
        (mul (add (div reserveNumerator_ 10000) r.scaledPendingWithdrawals) r.scaleFactor)
        500000000000000000000000000 = some normalizedNumerator_) :
    ((borrowTailAfterReserveFromReads amount r updatedAccruedProtocolFees_
      reserveNumerator_).run s).snd.storage 0 =
      ((borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
        normalizedNumerator_).run s).snd.storage 0 :=
  storage0_of_runState_eq
    (borrowTailAfterReserveFromReads_runState_of_normalizeNumerator amount r
      updatedAccruedProtocolFees_ reserveNumerator_ normalizedNumerator_ s hNormalizeNumerator)

private theorem borrowTailAfterNormalizedNumeratorFromReads_slot0_of_liquidityWithFees
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ : Uint256)
    (s : ContractState)
    (hLiquidityWithFees :
      safeAdd (div normalizedNumerator_ 1000000000000000000000000000)
        updatedAccruedProtocolFees_ = some liquidityWithFees_) :
    ((borrowTailAfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
      normalizedNumerator_).run s).snd.storage 0 =
      ((borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
        liquidityWithFees_).run s).snd.storage 0 :=
  storage0_of_runState_eq
    (borrowTailAfterNormalizedNumeratorFromReads_runState_of_liquidityWithFees amount r
      updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ s hLiquidityWithFees)

private theorem borrowTailAfterLiquidityWithFeesFromReads_slot0_of_liquidityRequired
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ : Uint256)
    (s : ContractState)
    (hLiquidityRequired :
      safeAdd liquidityWithFees_ r.normalizedUnclaimedWithdrawals = some liquidityRequired_) :
    ((borrowTailAfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
      liquidityWithFees_).run s).snd.storage 0 =
      ((borrowTailAfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
        liquidityRequired_).run s).snd.storage 0 :=
  storage0_of_runState_eq
    (borrowTailAfterLiquidityWithFeesFromReads_runState_of_liquidityRequired amount r
      updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ s hLiquidityRequired)

private theorem slot0AfterUpdatedFeesFromReads_reduces_to_afterOutstanding
    (amount : Uint256) (r : BorrowReads) (updatedAccruedProtocolFees_ scaledOutstandingSupply_ : Uint256)
    (s : ContractState)
    (hOutstanding :
      safeSub r.scaledTotalSupply r.scaledPendingWithdrawals = some scaledOutstandingSupply_) :
    slot0AfterUpdatedFeesFromReads amount r updatedAccruedProtocolFees_ s =
        slot0AfterOutstandingFromReads amount r updatedAccruedProtocolFees_ scaledOutstandingSupply_ s := by
    unfold slot0AfterUpdatedFeesFromReads slot0AfterOutstandingFromReads
    exact
      congrArg slot0OfState
        (stateAfterUpdatedFeesFromReads_reduces_to_afterOutstanding amount r
          updatedAccruedProtocolFees_ scaledOutstandingSupply_ s hOutstanding)

private theorem slot0AfterNormalizedNumeratorFromReads_reduces_to_afterLiquidityWithFees
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ : Uint256)
    (s : ContractState)
    (hLiquidityWithFees :
      safeAdd (div normalizedNumerator_ 1000000000000000000000000000)
        updatedAccruedProtocolFees_ = some liquidityWithFees_) :
      slot0AfterNormalizedNumeratorFromReads amount r updatedAccruedProtocolFees_
        normalizedNumerator_ s =
        slot0AfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
          liquidityWithFees_ s := by
    unfold slot0AfterNormalizedNumeratorFromReads slot0AfterLiquidityWithFeesFromReads
    exact
      congrArg slot0OfState
        (stateAfterNormalizedNumeratorFromReads_reduces_to_afterLiquidityWithFees amount r
          updatedAccruedProtocolFees_ normalizedNumerator_ liquidityWithFees_ s hLiquidityWithFees)

private theorem slot0AfterLiquidityWithFeesFromReads_reduces_to_afterLiquidityRequired
    (amount : Uint256) (r : BorrowReads)
    (updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ : Uint256)
    (s : ContractState)
    (hLiquidityRequired :
      safeAdd liquidityWithFees_ r.normalizedUnclaimedWithdrawals = some liquidityRequired_) :
      slot0AfterLiquidityWithFeesFromReads amount r updatedAccruedProtocolFees_
        liquidityWithFees_ s =
        slot0AfterLiquidityRequiredFromReads amount r updatedAccruedProtocolFees_
          liquidityRequired_ s := by
    unfold slot0AfterLiquidityWithFeesFromReads slot0AfterLiquidityRequiredFromReads
    exact
      congrArg slot0OfState
        (stateAfterLiquidityWithFeesFromReads_reduces_to_afterLiquidityRequired amount r
          updatedAccruedProtocolFees_ liquidityWithFees_ liquidityRequired_ s hLiquidityRequired)

private theorem borrow_slot0_reduces_to_after_updatedFees
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    (runBorrow amount preState).storage 0 = slot0AfterUpdatedFees amount preState := by
  rcases hPre with ⟨hFlaggedSlot, hClosedSlot, _, _, hFees, _, _, _, _, _⟩
  have hClosedRaw := isClosed_raw preState hClosedSlot
  simp only [isClosedSlot] at hClosedRaw
  have hUpdatedFees := updatedFees_some preState hFees
  have hPrefix :
      (runBorrow amount preState).storage 0 =
        ((borrowTailFromReads amount (readsOf preState)).run preState).snd.storage 0 := by
    have hRun := borrow_reduces_to_tailFromReads amount preState hFlaggedSlot
    simpa [runBorrow] using storage0_of_runState_eq hRun
  have hUpdatedFeesRun :
      (requireSomeUint
          (safeAdd (readsOf preState).accruedProtocolFees
            (readsOf preState).pendingProtocolFeeDelta)
          "ProtocolFeeOverflow").run preState =
        ContractResult.success (updatedFeesExpr' preState) preState := by
    exact requireSomeUint_run_of_eq (by simpa [readsOf] using hUpdatedFees)
  have hClosedRun :
      (require ((readsOf preState).isClosed == 0) "BorrowFromClosedMarket").run preState =
        ContractResult.success () preState := by
    simp [readsOf, hClosedRaw]
  have hFeeState :
      (borrowTailFromReads amount (readsOf preState)).runState preState =
        (Verity.bind
          (require ((readsOf preState).isClosed == 0) "BorrowFromClosedMarket")
          (fun _ =>
            borrowTailAfterUpdatedFeesFromReads amount (readsOf preState)
              (updatedFeesExpr' preState))).runState preState := by
    unfold borrowTailFromReads
    exact
      bind_runState_of_success_same
        (requireSomeUint
          (safeAdd (readsOf preState).accruedProtocolFees
            (readsOf preState).pendingProtocolFeeDelta)
          "ProtocolFeeOverflow")
        (fun updatedAccruedProtocolFees_ =>
          Verity.bind
            (require ((readsOf preState).isClosed == 0) "BorrowFromClosedMarket")
            (fun _ =>
              borrowTailAfterUpdatedFeesFromReads amount (readsOf preState)
                updatedAccruedProtocolFees_))
        preState (updatedFeesExpr' preState) hUpdatedFeesRun
  have hClosedState :
      (Verity.bind
          (require ((readsOf preState).isClosed == 0) "BorrowFromClosedMarket")
          (fun _ =>
            borrowTailAfterUpdatedFeesFromReads amount (readsOf preState)
              (updatedFeesExpr' preState))).runState preState =
        (borrowTailAfterUpdatedFeesFromReads amount (readsOf preState)
          (updatedFeesExpr' preState)).runState preState :=
    bind_runState_of_success_same
      (require ((readsOf preState).isClosed == 0) "BorrowFromClosedMarket")
      (fun _ =>
        borrowTailAfterUpdatedFeesFromReads amount (readsOf preState)
          (updatedFeesExpr' preState))
      preState () hClosedRun
  have hTail :
      ((borrowTailFromReads amount (readsOf preState)).run preState).snd.storage 0 =
        slot0AfterUpdatedFees amount preState := by
    have hState := hFeeState.trans hClosedState
    unfold slot0AfterUpdatedFees slot0AfterUpdatedFeesFromReads
    unfold stateAfterUpdatedFeesFromReads slot0OfState
    simpa [Contract.runState_eq_snd_run] using storage0_of_runState_eq hState
  calc
    (runBorrow amount preState).storage 0 =
        ((borrowTailFromReads amount (readsOf preState)).run preState).snd.storage 0 := hPrefix
    _ = slot0AfterUpdatedFees amount preState := hTail

private theorem slot0AfterUpdatedFees_reduces_to_after_outstanding
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    slot0AfterUpdatedFees amount preState = slot0AfterOutstanding amount preState := by
  rcases hPre with ⟨_, _, _, hPendingLeTotal, _, _, _, _, _, _⟩
  have hOutstanding := outstanding_some preState hPendingLeTotal
  unfold slot0AfterUpdatedFees slot0AfterOutstanding
  exact
    slot0AfterUpdatedFeesFromReads_reduces_to_afterOutstanding amount (readsOf preState)
      (updatedFeesExpr' preState) (scaledOutstandingExpr' preState) preState
      (by simpa [readsOf] using hOutstanding)

private theorem stateAfterOutstanding_reduces_to_after_reserve_of_reserveNumerator
    (amount : Uint256) (preState : ContractState)
    (hReserveNumerator : reserveNumeratorSomeExpr preState) :
    stateAfterOutstandingFromReads amount (readsOf preState)
      (updatedFeesExpr' preState) (scaledOutstandingExpr' preState) preState =
      stateAfterReserveFromReads amount (readsOf preState)
        (updatedFeesExpr' preState) (reserveNumeratorExpr' preState) preState := by
  have hReserveNumerator' :
      safeAdd
        (mul (scaledOutstandingExpr' preState)
          (readsOf preState).reserveRatioBips)
        5000 = some (reserveNumeratorExpr' preState) := by
    unfold reserveNumeratorSomeExpr at hReserveNumerator
    exact hReserveNumerator
  exact
    stateAfterOutstandingFromReads_reduces_to_afterReserve amount (readsOf preState)
      (updatedFeesExpr' preState) (scaledOutstandingExpr' preState)
      (reserveNumeratorExpr' preState) preState
      hReserveNumerator'

private theorem slot0AfterOutstanding_reduces_to_after_reserve_of_reserveNumerator
    (amount : Uint256) (preState : ContractState)
    (hReserveNumerator : reserveNumeratorSomeExpr preState) :
    slot0AfterOutstanding amount preState = slot0AfterReserve amount preState := by
  unfold slot0AfterOutstanding slot0AfterReserve
  unfold slot0AfterOutstandingFromReads slot0AfterReserveFromReads
  exact
    congrArg slot0OfState
      (stateAfterOutstanding_reduces_to_after_reserve_of_reserveNumerator amount preState
        hReserveNumerator)

private theorem slot0AfterOutstanding_reduces_to_after_reserve
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    slot0AfterOutstanding amount preState = slot0AfterReserve amount preState := by
  rcases hPre with ⟨_, _, _, hPendingLeTotal, _, hReserve, _, _, _, _⟩
  have hReserveNumerator' : reserveNumeratorSomeExpr preState := by
    unfold reserveNumeratorSomeExpr
    simpa [readsOf] using reserveNumerator_some preState hPendingLeTotal hReserve
  exact
    slot0AfterOutstanding_reduces_to_after_reserve_of_reserveNumerator amount preState
      hReserveNumerator'

private theorem stateAfterReserve_reduces_to_after_normalizedNumerator_of_normalizeNumerator
    (amount : Uint256) (preState : ContractState)
    (hNormalizeNumerator : normalizeNumeratorSomeExpr preState) :
    stateAfterReserveFromReads amount (readsOf preState)
      (updatedFeesExpr' preState) (reserveNumeratorExpr' preState) preState =
      stateAfterNormalizedNumeratorFromReads amount (readsOf preState)
        (updatedFeesExpr' preState) (normalizeNumeratorExpr' preState) preState := by
  have hNormalizeNumerator' :
      safeAdd
        (mul
          (add (div (reserveNumeratorExpr' preState) 10000)
            (readsOf preState).scaledPendingWithdrawals)
          (readsOf preState).scaleFactor)
        500000000000000000000000000 = some (normalizeNumeratorExpr' preState) := by
    unfold normalizeNumeratorSomeExpr at hNormalizeNumerator
    exact hNormalizeNumerator
  exact
    stateAfterReserveFromReads_reduces_to_afterNormalizedNumerator amount (readsOf preState)
      (updatedFeesExpr' preState) (reserveNumeratorExpr' preState)
      (normalizeNumeratorExpr' preState) preState
      hNormalizeNumerator'

private theorem slot0AfterReserve_reduces_to_after_normalizedNumerator_of_normalizeNumerator
    (amount : Uint256) (preState : ContractState)
    (hNormalizeNumerator : normalizeNumeratorSomeExpr preState) :
    slot0AfterReserve amount preState = slot0AfterNormalizedNumerator amount preState := by
  unfold slot0AfterReserve slot0AfterNormalizedNumerator
  unfold slot0AfterReserveFromReads slot0AfterNormalizedNumeratorFromReads
  exact
    congrArg slot0OfState
      (stateAfterReserve_reduces_to_after_normalizedNumerator_of_normalizeNumerator amount preState
        hNormalizeNumerator)

private theorem slot0AfterReserve_reduces_to_after_normalizedNumerator
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    slot0AfterReserve amount preState = slot0AfterNormalizedNumerator amount preState := by
  rcases hPre with ⟨_, _, _, hPendingLeTotal, _, hReserve, hNormalize, _, _, _⟩
  have hNormalizeNumerator' : normalizeNumeratorSomeExpr preState := by
    unfold normalizeNumeratorSomeExpr
    simpa [readsOf] using
      normalizeNumerator_some_expanded preState hPendingLeTotal hReserve hNormalize
  exact
    slot0AfterReserve_reduces_to_after_normalizedNumerator_of_normalizeNumerator amount preState
      hNormalizeNumerator'

private theorem slot0AfterNormalizedNumerator_reduces_to_after_liquidityWithFees_of_liquidityWithFees
    (amount : Uint256) (preState : ContractState)
    (hLiquidityWithFeesRaw : liquidityWithFeesSomeExpr preState) :
    slot0AfterNormalizedNumerator amount preState = slot0AfterLiquidityWithFees amount preState := by
  have hLiquidityWithFeesRaw' :
      safeAdd (div (normalizeNumeratorExpr' preState) 1000000000000000000000000000)
        (updatedFeesExpr' preState) =
      some (normalizedRequiredExpr' preState + updatedFeesExpr' preState) := by
    unfold liquidityWithFeesSomeExpr at hLiquidityWithFeesRaw
    exact hLiquidityWithFeesRaw
  unfold slot0AfterNormalizedNumerator slot0AfterLiquidityWithFees
  exact
    slot0AfterNormalizedNumeratorFromReads_reduces_to_afterLiquidityWithFees amount
      (readsOf preState) (updatedFeesExpr' preState) (normalizeNumeratorExpr' preState)
      (normalizedRequiredExpr' preState + updatedFeesExpr' preState) preState
      hLiquidityWithFeesRaw'

private theorem slot0AfterNormalizedNumerator_reduces_to_after_liquidityWithFees
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    slot0AfterNormalizedNumerator amount preState = slot0AfterLiquidityWithFees amount preState := by
  rcases hPre with ⟨_, _, _, hPendingLeTotal, _, hReserve, hNormalize,
    hLiquidityWithFees, _, _⟩
  have hLiquidityWithFeesRaw : liquidityWithFeesSomeExpr preState := by
    unfold liquidityWithFeesSomeExpr
    exact
      liquidityWithFees_some_expanded preState hPendingLeTotal hReserve hNormalize
        hLiquidityWithFees
  exact
    slot0AfterNormalizedNumerator_reduces_to_after_liquidityWithFees_of_liquidityWithFees
      amount preState
      hLiquidityWithFeesRaw

private theorem slot0AfterLiquidityWithFees_reduces_to_after_liquidityTail_of_liquidityRequired
    (amount : Uint256) (preState : ContractState)
    (hLiquidityRequired : liquidityRequiredSomeExpr preState) :
    slot0AfterLiquidityWithFees amount preState = slot0AfterLiquidityTail amount preState := by
  have hLiquidityRequired' :
      safeAdd (normalizedRequiredExpr' preState + updatedFeesExpr' preState)
        (readsOf preState).normalizedUnclaimedWithdrawals =
      some (liquidityRequiredExpr' preState) := by
    unfold liquidityRequiredSomeExpr at hLiquidityRequired
    exact hLiquidityRequired
  unfold slot0AfterLiquidityWithFees slot0AfterLiquidityTail
  exact
    slot0AfterLiquidityWithFeesFromReads_reduces_to_afterLiquidityRequired amount
      (readsOf preState) (updatedFeesExpr' preState)
      (normalizedRequiredExpr' preState + updatedFeesExpr' preState)
      (liquidityRequiredExpr' preState) preState
      hLiquidityRequired'

private theorem slot0AfterLiquidityWithFees_reduces_to_after_liquidityTail
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    slot0AfterLiquidityWithFees amount preState = slot0AfterLiquidityTail amount preState := by
  rcases hPre with ⟨_, _, _, hPendingLeTotal, _, hReserve, hNormalize,
    hLiquidityWithFees, hLiquidityRequiredTotal, _⟩
  have hLiquidityRequired' : liquidityRequiredSomeExpr preState := by
    unfold liquidityRequiredSomeExpr
    simpa [readsOf] using
      liquidityRequired_some preState hPendingLeTotal hReserve hNormalize hLiquidityWithFees
        hLiquidityRequiredTotal
  exact
    slot0AfterLiquidityWithFees_reduces_to_after_liquidityTail_of_liquidityRequired
      amount preState
      hLiquidityRequired'

private theorem slot0AfterReserve_reduces_to_after_liquidityTail
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    slot0AfterReserve amount preState = slot0AfterLiquidityTail amount preState := by
  calc
    slot0AfterReserve amount preState = slot0AfterNormalizedNumerator amount preState := by
      exact slot0AfterReserve_reduces_to_after_normalizedNumerator amount preState hPre
    _ = slot0AfterLiquidityWithFees amount preState := by
      exact slot0AfterNormalizedNumerator_reduces_to_after_liquidityWithFees amount preState hPre
    _ = slot0AfterLiquidityTail amount preState := by
      exact slot0AfterLiquidityWithFees_reduces_to_after_liquidityTail amount preState hPre

@[irreducible] private def liquidityTailMidStateEq
    (amount : Uint256) (preState : ContractState) : Prop :=
  stateAfterLiquidityRequiredFromReads amount (readsOf preState)
    (updatedFeesExpr' preState) (liquidityRequiredExpr' preState) preState =
    stateAfterReserveMid amount preState

private theorem liquidityTailMidStateEq_of_hook
    (amount : Uint256) (preState : ContractState)
    (hHookSlot : hookAllowsBorrowOf preState != 0) :
    liquidityTailMidStateEq amount preState := by
  have hHookRaw := hookAllowsBorrow_raw preState hHookSlot
  unfold liquidityTailMidStateEq
  unfold stateAfterLiquidityRequiredFromReads stateAfterReserveMid
  unfold borrowTailAfterLiquidityRequiredFromReads liquidityMidContract liquidityAmountGuard slot0WriteChain
  simp only [readsOf, Verity.Core.Uint256.le_def, Verity.Core.Uint256.lt_def,
    HSub.hSub, Verity.EVM.Uint256.sub]
  rw [show (preState.storage BorrowLiquiditySafety.hookAllowsBorrow.slot != 0) = true by
    simpa using hHookRaw]
  rfl

private theorem slot0AfterLiquidityTail_reduces_to_mid
    (amount : Uint256) (preState : ContractState)
    (hHookSlot : hookAllowsBorrowOf preState != 0) :
    slot0AfterLiquidityTail amount preState = slot0AfterReserveMid amount preState := by
  unfold slot0AfterLiquidityTail slot0AfterLiquidityRequiredFromReads slot0AfterReserveMid
  have hState := liquidityTailMidStateEq_of_hook amount preState hHookSlot
  unfold liquidityTailMidStateEq at hState
  exact
    congrArg slot0OfState
      hState

private theorem stateAfterReserveMid_reduces_to_guardedWrites
    (amount : Uint256) (preState : ContractState)
    :
    stateAfterReserveMid amount preState = stateAfterLiquidityGuardedWrites amount preState := by
  unfold stateAfterReserveMid stateAfterLiquidityGuardedWrites liquidityMidContract
  by_cases hGuard : liquidityAmountGuard amount preState = true
  · unfold slot0WriteChain
    simp [Contract.runState, Contract.run, Verity.bind, Bind.bind, require, setStorage,
      hGuard, Verity.EVM.Uint256.sub]
  · simp [Contract.runState, Contract.run, Verity.bind, Bind.bind, require, hGuard]

private theorem slot0AfterReserveMid_reduces_to_guardedWrites
    (amount : Uint256) (preState : ContractState)
    :
    slot0AfterReserveMid amount preState = slot0AfterLiquidityGuardedWrites amount preState := by
  unfold slot0AfterReserveMid slot0AfterLiquidityGuardedWrites
  exact
    congrArg slot0OfState
      (stateAfterReserveMid_reduces_to_guardedWrites amount preState)

private theorem slot0AfterLiquidityTail_reduces_to_guardedWrites
    (amount : Uint256) (preState : ContractState)
    (hHookSlot : hookAllowsBorrowOf preState != 0) :
    slot0AfterLiquidityTail amount preState = slot0AfterLiquidityGuardedWrites amount preState := by
  calc
    slot0AfterLiquidityTail amount preState = slot0AfterReserveMid amount preState := by
      exact slot0AfterLiquidityTail_reduces_to_mid amount preState hHookSlot
    _ = slot0AfterLiquidityGuardedWrites amount preState := by
      exact slot0AfterReserveMid_reduces_to_guardedWrites amount preState

private theorem slot0AfterLiquidityGuardedWrites_reduces_to_writes
    (amount : Uint256) (preState : ContractState)
    (hAmount : amount <= borrowableAssetsAfterUpdate preState) :
    slot0AfterLiquidityGuardedWrites amount preState = slot0AfterLiquidityWrites amount preState := by
  have hAmountGuard := amountGuard amount preState hAmount
  have hAmountGuardRaw :
      (amount : Nat) <=
        if (liquidityRequiredExpr' preState : Nat) <
            (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot : Nat) then
          ((preState.storage BorrowLiquiditySafety.totalAssetsStored.slot - liquidityRequiredExpr' preState :
              Uint256) : Nat)
        else 0 := by
    simpa [Verity.Core.Uint256.le_def, Verity.Core.Uint256.lt_def] using hAmountGuard
  have hAmountGuardBool : liquidityAmountGuard amount preState = true := by
    unfold liquidityAmountGuard
    rw [decide_eq_true_iff]
    by_cases hLt :
        (liquidityRequiredExpr' preState : Nat) <
          (preState.storage BorrowLiquiditySafety.totalAssetsStored.slot : Nat)
    · simpa [hLt, HSub.hSub, Verity.EVM.Uint256.sub] using hAmountGuardRaw
    · simpa [hLt] using hAmountGuardRaw
  unfold slot0AfterLiquidityGuardedWrites stateAfterLiquidityGuardedWrites slot0OfState
    slot0AfterLiquidityWrites slot0WriteChain
  rw [hAmountGuardBool]
  simp [Contract.run, Verity.bind, Bind.bind, setStorage, Verity.EVM.Uint256.sub]

private theorem slot0AfterLiquidityWrites_write
    (amount : Uint256) (preState : ContractState) :
    slot0AfterLiquidityWrites amount preState = slot0WrittenValue amount preState := by
  unfold slot0AfterLiquidityWrites slot0WrittenValue
  simp [Verity.bind, Verity.pure, Pure.pure, Bind.bind, Contract.run, setStorage,
    BorrowLiquiditySafety.pendingProtocolFeeDelta,
    BorrowLiquiditySafety.accruedProtocolFees, BorrowLiquiditySafety.totalAssetsStored]

private theorem slot0AfterLiquidityTail_write
    (amount : Uint256) (preState : ContractState)
    (hHookSlot : hookAllowsBorrowOf preState != 0)
    (hAmount : amount <= borrowableAssetsAfterUpdate preState) :
    slot0AfterLiquidityTail amount preState = slot0WrittenValue amount preState := by
  calc
    slot0AfterLiquidityTail amount preState = slot0AfterLiquidityGuardedWrites amount preState := by
      exact slot0AfterLiquidityTail_reduces_to_guardedWrites amount preState hHookSlot
    _ = slot0AfterLiquidityWrites amount preState := by
      exact slot0AfterLiquidityGuardedWrites_reduces_to_writes amount preState hAmount
    _ = slot0WrittenValue amount preState := by
      exact slot0AfterLiquidityWrites_write amount preState

private theorem borrow_slot0_write
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    (runBorrow amount preState).storage 0 = slot0WrittenValue amount preState := by
  have hPre' := hPre
  rcases hPre with ⟨_, _, hHookSlot, _, _, _, _, _, _, hAmount⟩
  calc
    (runBorrow amount preState).storage 0 = slot0AfterUpdatedFees amount preState := by
      exact borrow_slot0_reduces_to_after_updatedFees amount preState hPre'
    _ = slot0AfterOutstanding amount preState := by
      exact slot0AfterUpdatedFees_reduces_to_after_outstanding amount preState hPre'
    _ = slot0AfterReserve amount preState := by
      exact slot0AfterOutstanding_reduces_to_after_reserve amount preState hPre'
    _ = slot0AfterLiquidityTail amount preState := by
      exact slot0AfterReserve_reduces_to_after_liquidityTail amount preState hPre'
    _ = slot0WrittenValue amount preState := by
      exact slot0AfterLiquidityTail_write amount preState hHookSlot hAmount

theorem borrow_total_assets_write
    (amount : Uint256) (preState : ContractState)
    (hPre : borrow_succeeds_preconditions amount preState) :
    totalAssetsOf (runBorrow amount preState) = totalAssetsOf preState - amount := by
  simpa [totalAssetsOf, slot0WrittenValue, BorrowLiquiditySafety.pendingProtocolFeeDelta,
    BorrowLiquiditySafety.accruedProtocolFees, BorrowLiquiditySafety.totalAssetsStored] using
    borrow_slot0_write amount preState hPre

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
