import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Verity.Proofs.Stdlib.Automation

/-!
Reference proofs for all public theorem interfaces in `Specs.lean`.
Generated task files remain agent-facing placeholders; executable reference
solutions live only in this module.
-/

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- A full-precision ceiling quotient cannot exceed its left factor when the
right factor is strictly smaller than the divisor.  The failure sentinel is
zero, so the statement covers both helper outcomes. -/
private theorem mulDiv512Up_le_left_of_right_lt
    (a b c : Uint256) (hbc : (b : Nat) < (c : Nat)) :
    (mulDiv512Up a b c : Nat) ≤ (a : Nat) := by
  have hc : (c : Nat) ≠ 0 := by omega
  have hcPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hc
  have hBLe : (b : Nat) ≤ (c : Nat) - 1 := Nat.le_pred_of_lt hbc
  have hSubLt : (c : Nat) - 1 < (c : Nat) := Nat.sub_lt hcPos (by decide)
  have hNumeratorLt :
      (a : Nat) * (b : Nat) + ((c : Nat) - 1) < ((a : Nat) + 1) * (c : Nat) := by
    calc
      (a : Nat) * (b : Nat) + ((c : Nat) - 1)
          ≤ (a : Nat) * ((c : Nat) - 1) + ((c : Nat) - 1) := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hBLe) _
      _ = ((a : Nat) + 1) * ((c : Nat) - 1) := by
              rw [Nat.add_mul]
              simp
      _ < ((a : Nat) + 1) * (c : Nat) := by
              exact Nat.mul_lt_mul_of_pos_left hSubLt (by omega)
  unfold mulDiv512Up
  cases hResult : mulDiv512Up? a b c with
  | none => simp [hResult]
  | some result =>
      have hFit :
          (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) ≤ MAX_UINT256 := by
        simpa [mulDiv512Up?, hc] using congrArg Option.isSome hResult
      have hDivLt :
          (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) < (a : Nat) + 1 := by
        exact (Nat.div_lt_iff_lt_mul hcPos).2 hNumeratorLt
      have hResultVal :
          (result : Nat) = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := by
        simp [mulDiv512Up?, hc] at hResult
        rw [← hResult.2]
        simp [Nat.mod_eq_of_lt
          (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hFit)]
      simp [hResult, hResultVal]
      omega

/-- The current fee-on-total quotient is at most the gross amount whenever
the source's checked fee-divisor addition fits. -/
private theorem feeAmountOf_le_gross
    (s : ContractState) (grossAssets : Uint256) (hFeeDivisor : feeDivisorFits s) :
    (feeAmountOf s grossAssets : Nat) ≤ (grossAssets : Nat) := by
  have hFits : (feeOnWithdrawOf s : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, checkedAddFits] using hFeeDivisor
  have hAddVal :
      (add (feeOnWithdrawOf s) feeDenominator : Nat) =
        (feeOnWithdrawOf s : Nat) + (feeDenominator : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hFits)
  have hDenominatorPos : 0 < (feeDenominator : Nat) := by
    native_decide
  have hFeeLtDivisor :
      (feeOnWithdrawOf s : Nat) < (add (feeOnWithdrawOf s) feeDenominator : Nat) := by
    rw [hAddVal]
    omega
  unfold feeAmountOf feeAmountWith
  exact mulDiv512Up_le_left_of_right_lt _ _ _ hFeeLtDivisor

/-- The concrete map write performed by `setMapping`.  Keeping the verifier's
bookkeeping update here lets the execution lemmas below name compact
post-states instead of asking `simp` to repeatedly expand nested records. -/
private def mapWriteState
    (s : ContractState) (sl : Nat) (key : Address) (value : Uint256) : ContractState :=
  { s.writeMap sl key value with
    knownAddresses := fun sl' =>
      if sl' == sl then (s.knownAddresses sl').insert key else s.knownAddresses sl' }

/-- Reduce one successful monadic bind before the outer call applies its
rollback wrapper. -/
private theorem bind_apply_of_success
    {α β : Type} (m : Contract α) (k : α → Contract β) (s s' : ContractState) (a : α)
    (h : m s = ContractResult.success a s') :
    (m >>= k) s = k a s' := by
  simp [Bind.bind, Verity.bind, h]

private theorem bind_apply_of_revert
    {α β : Type} (m : Contract α) (k : α → Contract β) (s s' : ContractState)
    (msg : String) (h : m s = ContractResult.revert msg s') :
    (m >>= k) s = ContractResult.revert msg s' := by
  simp [Bind.bind, Verity.bind, h]

/-- The contract surface uses the named EVM operations directly, whereas the
core algebraic identities are stated with notation.  These bridge lemmas keep
zero-component state equalities compact. -/
private theorem uint_sub_zero (a : Uint256) : sub a 0 = a := by
  exact Verity.Core.Uint256.sub_zero a

private theorem uint_sub_self (a : Uint256) : sub a a = 0 := by
  exact Verity.Core.Uint256.sub_self a

private theorem uint_add_zero (a : Uint256) : add a 0 = a := by
  exact Verity.Core.Uint256.add_zero a

/-- The successful queued-request state, including the concrete bookkeeping
updates induced by each mapping write. -/
private def queuedPostState
    (s : ContractState) (shares grossAssets : Uint256) (receiver owner : Address) : ContractState :=
  let afterTransfer :=
    mapWriteState
      (mapWriteState s 5 owner (sub (s.storageMap 5 owner) shares))
      5 s.thisAddress (add (s.storageMap 5 s.thisAddress) shares)
  let afterTotal := afterTransfer.writeSlot 0 (add (s.storage 0) grossAssets)
  let afterShares := mapWriteState afterTotal 6 receiver (add (s.storageMap 6 receiver) shares)
  mapWriteState afterShares 7 receiver (add (s.storageMap 7 receiver) grossAssets)

/-- Execute a queued request once, with a named post-state.  The proof reduces
one branch at a time; it deliberately does not rely on a global recursion
limit to normalize the full contract-state record. -/
private theorem requestRedeem_queued_run
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (s : ContractState)
    (hVault : s.thisAddress ≠ 0)
    (hOwner : owner ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hOwnerNotVault : owner ≠ s.thisAddress)
    (hOwnerIsSender : owner = s.sender)
    (hUnpaused : s.storage 3 = 0)
    (hSharesPositive : shares > 0)
    (hOwnerShares : s.storageMap 5 owner >= shares)
    (hQueued :
      (if externalUnderlyingBalance > s.storage 0 then
        sub externalUnderlyingBalance (s.storage 0)
      else 0) < grossAssets)
    (hTotalAdd : (s.storage 0 : Nat) + (grossAssets : Nat) <= MAX_UINT256)
    (hSharesAdd : (s.storageMap 6 receiver : Nat) + (shares : Nat) <= MAX_UINT256)
    (hAssetsAdd : (s.storageMap 7 receiver : Nat) + (grossAssets : Nat) <= MAX_UINT256) :
    (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets externalUnderlyingBalance
      true true true true).run s =
      ContractResult.success 0 (queuedPostState s shares grossAssets receiver owner) := by
  have hTotalSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hTotalAdd
  have hSharesSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hSharesAdd
  have hAssetsSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hAssetsAdd
  have hNotInstant : ¬ grossAssets <=
      (if externalUnderlyingBalance > s.storage 0 then sub externalUnderlyingBalance (s.storage 0) else 0) :=
    Nat.not_le_of_gt hQueued
  have hNotInstantVal : ¬grossAssets.val <=
      (if externalUnderlyingBalance > s.storage 0 then sub externalUnderlyingBalance (s.storage 0) else 0).val :=
    Nat.not_le_of_gt hQueued
  subst owner
  have hSenderVault : s.sender ≠ s.thisAddress := by simpa using hOwnerNotVault
  have hVaultZero : s.thisAddress ≠ 0 := hVault
  have hSenderZero : s.sender ≠ 0 := hOwner
  rw [YoAsyncRedemptionEscrow.requestRedeem]
  by_cases hExternal : externalUnderlyingBalance > s.storage 0
  · have hBranch : ¬grossAssets.val <= (sub externalUnderlyingBalance (s.storage 0)).val := by
      simpa [hExternal] using hNotInstantVal
    simp [Contract.run, Bind.bind, Verity.bind, getStorage, getMapping, msgSender, Verity.require,
      YoAsyncRedemptionEscrow._getAvailableBalance, YoAsyncRedemptionEscrow._transfer,
      YoAsyncRedemptionEscrow._update, setStorage, setMapping, requireSomeUint,
      Verity.contractAddress, Verity.pure, Pure.pure, YoAsyncRedemptionEscrow.paused,
      YoAsyncRedemptionEscrow.shareBalances, YoAsyncRedemptionEscrow.pendingShares,
      YoAsyncRedemptionEscrow.pendingAssets, YoAsyncRedemptionEscrow.totalPendingAssets,
      zeroAddress, hVault, hOwner, hReceiver, hSenderVault, hVaultZero, hSenderZero,
      hUnpaused, hSharesPositive, hOwnerShares, hNotInstant, hNotInstantVal, hTotalSafe,
      hSharesSafe, hAssetsSafe, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, hExternal, hBranch]
    constructor
    · funext sl
      by_cases hsl : sl = 0
      · subst sl
        exact Verity.Core.Uint256.add_comm _ _
      · simp [hsl]
    · funext sl key
      by_cases h7 : sl = 7 ∧ key = receiver
      · simp [h7]
        change grossAssets + s.storageMap 7 receiver = s.storageMap 7 receiver + grossAssets
        exact Verity.Core.Uint256.add_comm _ _
      · by_cases h6 : sl = 6 ∧ key = receiver
        · simp [h7, h6]
          change shares + s.storageMap 6 receiver = s.storageMap 6 receiver + shares
          exact Verity.Core.Uint256.add_comm _ _
        · simp [h7, h6]
  · have hGrossNonzero : grossAssets.val ≠ 0 := by
      have hGrossPos : 0 < grossAssets.val := by simpa [hExternal] using hQueued
      omega
    simp [Contract.run, Bind.bind, Verity.bind, getStorage, getMapping, msgSender, Verity.require,
      YoAsyncRedemptionEscrow._getAvailableBalance, YoAsyncRedemptionEscrow._transfer,
      YoAsyncRedemptionEscrow._update, setStorage, setMapping, requireSomeUint,
      Verity.contractAddress, Verity.pure, Pure.pure, YoAsyncRedemptionEscrow.paused,
      YoAsyncRedemptionEscrow.shareBalances, YoAsyncRedemptionEscrow.pendingShares,
      YoAsyncRedemptionEscrow.pendingAssets, YoAsyncRedemptionEscrow.totalPendingAssets,
      zeroAddress, hVault, hOwner, hReceiver, hSenderVault, hVaultZero, hSenderZero,
      hUnpaused, hSharesPositive, hOwnerShares, hNotInstant, hNotInstantVal, hTotalSafe,
      hSharesSafe, hAssetsSafe, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, hExternal, hGrossNonzero]
    constructor
    · funext sl
      by_cases hsl : sl = 0
      · subst sl
        exact Verity.Core.Uint256.add_comm _ _
      · simp [hsl]
    · funext sl key
      by_cases h7 : sl = 7 ∧ key = receiver
      · simp [h7]
        change grossAssets + s.storageMap 7 receiver = s.storageMap 7 receiver + grossAssets
        exact Verity.Core.Uint256.add_comm _ _
      · by_cases h6 : sl = 6 ∧ key = receiver
        · simp [h7, h6]
          change shares + s.storageMap 6 receiver = s.storageMap 6 receiver + shares
          exact Verity.Core.Uint256.add_comm _ _
        · simp [h7, h6]

/-- Post-state of the three pending-accounting writes in `fulfillRedeem`. -/
private def pendingFulfillPostState
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256) : ContractState :=
  let afterShares := mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)
  let afterAssets := mapWriteState afterShares 7 receiver (sub (s.storageMap 7 receiver) grossAssets)
  afterAssets.writeSlot 0 (sub (s.storage 0) grossAssets)

/-- Post-state of the burn performed by `_withdraw`. -/
private def burnPostState (s : ContractState) (shares : Uint256) : ContractState :=
  (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) shares)).writeSlot 4
    (sub (s.storage 4) shares)

/-- The same burn post-state when `_withdraw` burns an arbitrary owner.  Instant
requests use this form, while fulfillment burns the vault-owned pool above. -/
private def burnFromPostState
    (s : ContractState) (owner : Address) (shares : Uint256) : ContractState :=
  (mapWriteState s 5 owner (sub (s.storageMap 5 owner) shares)).writeSlot 4
    (sub (s.storage 4) shares)

/-- The transfer state for a zero-share cancellation.  It records the map-key
bookkeeping of the non-self path while preserving all EVM-visible values. -/
private def transferZeroPostState (s : ContractState) (receiver : Address) : ContractState :=
  if s.thisAddress = receiver then s else
    mapWriteState
      (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) 0))
      5 receiver (add (s.storageMap 5 receiver) 0)

/-- The general ERC-20 transfer post-state, including the self-transfer path. -/
private def transferPostState
    (s : ContractState) (fromAddr toAddr : Address) (shares : Uint256) : ContractState :=
  if fromAddr = toAddr then s else
    mapWriteState
      (mapWriteState s 5 fromAddr (sub (s.storageMap 5 fromAddr) shares))
      5 toAddr (add (s.storageMap 5 toAddr) shares)

/-- Successful cancellation first updates the independent pending components,
then transfers the selected pooled shares. -/
private def cancelledPostState
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256) : ContractState :=
  transferPostState (pendingFulfillPostState s receiver shares grossAssets)
    s.thisAddress receiver shares

private def cancelZeroPostState (s : ContractState) (receiver : Address) : ContractState :=
  transferZeroPostState (pendingFulfillPostState s receiver 0 0) receiver

/-- `setMapping` expressed through the compact state name used below. -/
private theorem setMapping_apply_mapWriteState
    (s : ContractState) (sl : Nat) (key : Address) (value : Uint256) :
    (setMapping (⟨sl⟩ : StorageSlot (Address → Uint256)) key value) s =
      ContractResult.success () (mapWriteState s sl key value) := by
  rfl

/-- Current `isAuthorized` takes the explicit successful authority branch. -/
private theorem isAuthorized_true_true_apply (s : ContractState) (hAuthority : s.storageAddr 9 ≠ 0) :
    YoAsyncRedemptionEscrow.isAuthorized true true s = ContractResult.success true s := by
  rw [YoAsyncRedemptionEscrow.isAuthorized]
  simp [Bind.bind, Verity.bind, getStorageAddr, msgSender, Verity.require,
    YoAsyncRedemptionEscrow.authority, zeroAddress, hAuthority, Verity.pure, Pure.pure]

/-- A nonzero authority returning `false` falls through to the stored owner. -/
private theorem isAuthorized_true_false_owner_apply
    (s : ContractState) (hAuthority : s.storageAddr 9 ≠ 0)
    (hOwnerSender : s.sender = s.storageAddr 8) :
    YoAsyncRedemptionEscrow.isAuthorized true false s = ContractResult.success true s := by
  rw [YoAsyncRedemptionEscrow.isAuthorized]
  simp [Bind.bind, Verity.bind, getStorageAddr, msgSender, Verity.require,
    YoAsyncRedemptionEscrow.authority, YoAsyncRedemptionEscrow.owner, zeroAddress,
    hAuthority, hOwnerSender, Verity.pure, Pure.pure]

private theorem isAuthorized_false_apply (s : ContractState) (hAuthority : s.storageAddr 9 ≠ 0) :
    YoAsyncRedemptionEscrow.isAuthorized false false s =
      ContractResult.revert "AuthorityCanCallReverted" s := by
  rw [YoAsyncRedemptionEscrow.isAuthorized]
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.authority) _ s s
    (s.storageAddr 9) (by rfl)]
  rw [bind_apply_of_success Verity.msgSender _ s s s.sender (by rfl)]
  have hAuthNonzero : (s.storageAddr 9 != zeroAddress) = true := by
    simpa [zeroAddress] using hAuthority
  simp only [hAuthNonzero, ↓reduceIte]
  exact bind_apply_of_revert (Verity.require false "AuthorityCanCallReverted") _ s s
    "AuthorityCanCallReverted" (by rfl)

/-- Isolate the zero-share `_transfer` used by source-permitted `(0,0)`
cancellation without expanding its resulting records at call sites. -/
private theorem transfer_zero_apply
    (s : ContractState) (receiver : Address)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hUnpaused : s.storage 3 = 0) :
    YoAsyncRedemptionEscrow._transfer s.thisAddress receiver 0 s =
      ContractResult.success () (transferZeroPostState s receiver) := by
  rw [YoAsyncRedemptionEscrow._transfer]
  rw [bind_apply_of_success
    (Verity.require (s.thisAddress != zeroAddress) "ERC20InvalidSender") _ s s ()
    (by simp [Verity.require, zeroAddress, hVault])]
  rw [bind_apply_of_success
    (Verity.require (receiver != zeroAddress) "ERC20InvalidReceiver") _ s s ()
    (by simp [Verity.require, zeroAddress, hReceiver])]
  by_cases hSelf : s.thisAddress = receiver
  · subst receiver
    rw [YoAsyncRedemptionEscrow._updateSelf]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
      (by rfl)]
    rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
      (by simp [Verity.require, hUnpaused])]
    rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances s.thisAddress) _
      s s (s.storageMap 5 s.thisAddress) (by rfl)]
    rw [bind_apply_of_success
      (Verity.require (s.storageMap 5 s.thisAddress >= 0) "ERC20InsufficientBalance") _ s s ()
      (by simp [Verity.require])]
    simpa [transferZeroPostState, Verity.pure, Pure.pure]
  · have hSelfBool : (s.thisAddress == receiver) = false := by
      simp [hSelf]
    have hReceiverZero : (receiver == zeroAddress) = false := by
      simp [zeroAddress, hReceiver]
    rw [hSelfBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [YoAsyncRedemptionEscrow._update]
    rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
      (by rfl)]
    rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
      (by simp [Verity.require, hUnpaused])]
    rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances s.thisAddress) _
      s s (s.storageMap 5 s.thisAddress) (by rfl)]
    rw [bind_apply_of_success
      (Verity.require (s.storageMap 5 s.thisAddress >= 0) "ERC20InsufficientBalance") _ s s ()
      (by simp [Verity.require])]
    rw [hReceiverZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances receiver) _
      s s (s.storageMap 5 receiver) (by rfl)]
    rw [bind_apply_of_success
      (setMapping YoAsyncRedemptionEscrow.shareBalances s.thisAddress
        (sub (s.storageMap 5 s.thisAddress) 0)) _ s
      (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) 0)) ()
      (setMapping_apply_mapWriteState s 5 s.thisAddress
        (sub (s.storageMap 5 s.thisAddress) 0))]
    change setMapping YoAsyncRedemptionEscrow.shareBalances receiver
      (add (s.storageMap 5 receiver) 0)
      (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) 0)) = _
    simpa [transferZeroPostState, hSelf] using
      setMapping_apply_mapWriteState
        (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) 0)) 5 receiver
        (add (s.storageMap 5 receiver) 0)

/-- Execute `_transfer` with a named post-state for both the self and
non-self branches. -/
private theorem transfer_apply
    (s : ContractState) (fromAddr toAddr : Address) (shares : Uint256)
    (hFrom : fromAddr ≠ 0) (hTo : toAddr ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hFromShares : shares.val ≤ (s.storageMap 5 fromAddr).val) :
    YoAsyncRedemptionEscrow._transfer fromAddr toAddr shares s =
      ContractResult.success () (transferPostState s fromAddr toAddr shares) := by
  have hBalance : s.storageMap 5 fromAddr >= shares := by
    simpa using hFromShares
  rw [YoAsyncRedemptionEscrow._transfer]
  rw [bind_apply_of_success
    (Verity.require (fromAddr != zeroAddress) "ERC20InvalidSender") _ s s ()
    (by simp [Verity.require, zeroAddress, hFrom])]
  rw [bind_apply_of_success
    (Verity.require (toAddr != zeroAddress) "ERC20InvalidReceiver") _ s s ()
    (by simp [Verity.require, zeroAddress, hTo])]
  by_cases hSelf : fromAddr = toAddr
  · subst toAddr
    rw [YoAsyncRedemptionEscrow._updateSelf]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
      (by rfl)]
    rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
      (by simp [Verity.require, hUnpaused])]
    rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances fromAddr) _ s s
      (s.storageMap 5 fromAddr) (by rfl)]
    rw [bind_apply_of_success
      (Verity.require (s.storageMap 5 fromAddr >= shares) "ERC20InsufficientBalance") _ s s ()
      (by simp [Verity.require, hBalance])]
    simp [transferPostState, Verity.pure, Pure.pure]
  · have hSelfBool : (fromAddr == toAddr) = false := by simp [hSelf]
    rw [hSelfBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [YoAsyncRedemptionEscrow._update]
    rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
      (by rfl)]
    rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
      (by simp [Verity.require, hUnpaused])]
    rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances fromAddr) _ s s
      (s.storageMap 5 fromAddr) (by rfl)]
    rw [bind_apply_of_success
      (Verity.require (s.storageMap 5 fromAddr >= shares) "ERC20InsufficientBalance") _ s s ()
      (by simp [Verity.require, hBalance])]
    have hToZero : (toAddr == zeroAddress) = false := by simp [zeroAddress, hTo]
    rw [hToZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances toAddr) _ s s
      (s.storageMap 5 toAddr) (by rfl)]
    rw [bind_apply_of_success
      (setMapping YoAsyncRedemptionEscrow.shareBalances fromAddr
        (sub (s.storageMap 5 fromAddr) shares)) _ s
      (mapWriteState s 5 fromAddr (sub (s.storageMap 5 fromAddr) shares)) ()
      (setMapping_apply_mapWriteState s 5 fromAddr
        (sub (s.storageMap 5 fromAddr) shares))]
    change setMapping YoAsyncRedemptionEscrow.shareBalances toAddr
      (add (s.storageMap 5 toAddr) shares)
      (mapWriteState s 5 fromAddr (sub (s.storageMap 5 fromAddr) shares)) = _
    simpa [transferPostState, hSelf] using
      setMapping_apply_mapWriteState
        (mapWriteState s 5 fromAddr (sub (s.storageMap 5 fromAddr) shares)) 5 toAddr
        (add (s.storageMap 5 toAddr) shares)

/-- Evaluate the external-balance-derived availability helper without exposing
the surrounding request control flow. -/
private theorem getAvailableBalance_apply
    (externalUnderlyingBalance : Uint256) (s : ContractState) :
    YoAsyncRedemptionEscrow._getAvailableBalance externalUnderlyingBalance s =
      ContractResult.success
        (if externalUnderlyingBalance > s.storage 0 then
          sub externalUnderlyingBalance (s.storage 0)
        else 0) s := by
  rw [YoAsyncRedemptionEscrow._getAvailableBalance]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  by_cases hExternal : externalUnderlyingBalance > s.storage 0 <;>
    simp [hExternal, Verity.pure, Pure.pure]

/-- The queued request helper above deliberately names the non-self transfer
state.  This companion handles the allowed owner-equals-vault self-transfer. -/
private theorem requestRedeem_queued_run_self
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver : Address)
    (s : ContractState)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hSender : s.sender = s.thisAddress)
    (hUnpaused : s.storage 3 = 0)
    (hSharesPositive : shares > 0)
    (hOwnerShares : s.storageMap 5 s.thisAddress >= shares)
    (hQueued :
      (if externalUnderlyingBalance > s.storage 0 then
        sub externalUnderlyingBalance (s.storage 0)
      else 0) < grossAssets)
    (hTotalAdd : (s.storage 0 : Nat) + (grossAssets : Nat) <= MAX_UINT256)
    (hSharesAdd : (s.storageMap 6 receiver : Nat) + (shares : Nat) <= MAX_UINT256)
    (hAssetsAdd : (s.storageMap 7 receiver : Nat) + (grossAssets : Nat) <= MAX_UINT256) :
    (YoAsyncRedemptionEscrow.requestRedeem shares receiver s.thisAddress grossAssets
      externalUnderlyingBalance true true true true).run s =
      ContractResult.success 0
        (let afterTotal := s.writeSlot 0 (add (s.storage 0) grossAssets)
         let afterShares := mapWriteState afterTotal 6 receiver
           (add (s.storageMap 6 receiver) shares)
         mapWriteState afterShares 7 receiver (add (s.storageMap 7 receiver) grossAssets)) := by
  have hTotalSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hTotalAdd
  have hSharesSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hSharesAdd
  have hAssetsSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hAssetsAdd
  have hSharesNonzero : shares.val ≠ 0 := by
    exact Nat.ne_of_gt (by simpa using hSharesPositive)
  have hNotInstant : ¬ grossAssets <=
      (if externalUnderlyingBalance > s.storage 0 then
        sub externalUnderlyingBalance (s.storage 0)
      else 0) :=
    Nat.not_le_of_gt hQueued
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.requestRedeem]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
    (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
    (by simp [Verity.require, hUnpaused])]
  rw [bind_apply_of_success Verity.msgSender _ s s s.sender (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances s.thisAddress) _ s s
    (s.storageMap 5 s.thisAddress) (by rfl)]
  rw [bind_apply_of_success (Verity.require (receiver != zeroAddress) "ZeroReceiver") _ s s ()
    (by simp [Verity.require, zeroAddress, hReceiver])]
  rw [bind_apply_of_success (Verity.require (shares > 0) "SharesAmountZero") _ s s ()
    (by simp [Verity.require, hSharesNonzero])]
  rw [bind_apply_of_success (Verity.require (s.thisAddress == s.sender) "NotSharesOwner") _ s s ()
    (by simp [Verity.require, hSender])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 5 s.thisAddress >= shares) "InsufficientShares") _ s s ()
    (by simp [Verity.require, hOwnerShares])]
  rw [bind_apply_of_success (Verity.require true "PreviewRedeemFailed") _ s s () (by rfl)]
  rw [bind_apply_of_success (Verity.require true "UnderlyingBalanceReadFailed") _ s s () (by rfl)]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow._getAvailableBalance externalUnderlyingBalance) _
    s s _ (getAvailableBalance_apply externalUnderlyingBalance s)]
  simp only [hNotInstant, ↓reduceIte]
  rw [bind_apply_of_success Verity.contractAddress _ s s s.thisAddress (by rfl)]
  have hSelfTransfer :
      YoAsyncRedemptionEscrow._transfer s.thisAddress s.thisAddress shares s =
        ContractResult.success () s := by
    simpa [transferPostState] using
      transfer_apply s s.thisAddress s.thisAddress shares hVault hVault hUnpaused
        (by simpa using hOwnerShares)
  rw [bind_apply_of_success
    (YoAsyncRedemptionEscrow._transfer s.thisAddress s.thisAddress shares) _ s s ()
    hSelfTransfer]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (requireSomeUint (safeAdd (s.storage 0) grossAssets) "Panic(0x11): arithmetic overflow") _
    s s (s.storage 0 + grossAssets) (by rw [hTotalSafe]; rfl)]
  rw [bind_apply_of_success
    (requireSomeUint (safeAdd (s.storageMap 6 receiver) shares) "Panic(0x11): arithmetic overflow") _
    s s (s.storageMap 6 receiver + shares) (by rw [hSharesSafe]; rfl)]
  rw [bind_apply_of_success
    (requireSomeUint (safeAdd (s.storageMap 7 receiver) grossAssets)
      "Panic(0x11): arithmetic overflow") _
    s s (s.storageMap 7 receiver + grossAssets) (by rw [hAssetsSafe]; rfl)]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (s.storage 0 + grossAssets)) _ s
    (s.writeSlot 0 (s.storage 0 + grossAssets)) () (by rfl)]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver
      (s.storageMap 6 receiver + shares)) _
    (s.writeSlot 0 (s.storage 0 + grossAssets))
    (mapWriteState (s.writeSlot 0 (s.storage 0 + grossAssets)) 6 receiver
      (s.storageMap 6 receiver + shares)) () (by rfl)]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver
      (s.storageMap 7 receiver + grossAssets)) _
    (mapWriteState (s.writeSlot 0 (s.storage 0 + grossAssets)) 6 receiver
      (s.storageMap 6 receiver + shares))
    (mapWriteState
      (mapWriteState (s.writeSlot 0 (s.storage 0 + grossAssets)) 6 receiver
        (s.storageMap 6 receiver + shares)) 7 receiver
      (s.storageMap 7 receiver + grossAssets)) () (by rfl)]
  rfl

private theorem cancelRedeem_apply_zero
    (receiver : Address) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hUnpaused : s.storage 3 = 0) :
    YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true s =
      ContractResult.success () (cancelZeroPostState s receiver) := by
  rw [YoAsyncRedemptionEscrow.cancelRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && 0 <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by
        simp [Verity.require, hPendingShares])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 7 receiver != 0 && 0 <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s () (by
        simp [Verity.require, hPendingAssets])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storage 0 >= 0) "Panic(0x11): arithmetic underflow") _ s s () (by
      simp [Verity.require])]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver (sub (s.storageMap 6 receiver) 0)) _ s
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) 0)) ()
    (setMapping_apply_mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) 0))]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver (sub (s.storageMap 7 receiver) 0)) _
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) 0))
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) 0)) 7 receiver
      (sub (s.storageMap 7 receiver) 0)) ()
    (setMapping_apply_mapWriteState
      (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) 0)) 7 receiver
      (sub (s.storageMap 7 receiver) 0))]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (sub (s.storage 0) 0)) _
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) 0)) 7 receiver
      (sub (s.storageMap 7 receiver) 0))
    (pendingFulfillPostState s receiver 0 0) () (by rfl)]
  rw [bind_apply_of_success Verity.contractAddress _ (pendingFulfillPostState s receiver 0 0)
    (pendingFulfillPostState s receiver 0 0)
    (pendingFulfillPostState s receiver 0 0).thisAddress (by rfl)]
  have hPendingVault : (pendingFulfillPostState s receiver 0 0).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hVault
  have hPendingReceiver : receiver ≠ 0 := hReceiver
  have hPendingUnpaused : (pendingFulfillPostState s receiver 0 0).storage 3 = 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hUnpaused
  simpa [cancelZeroPostState] using
    transfer_zero_apply (pendingFulfillPostState s receiver 0 0) receiver
      hPendingVault hPendingReceiver hPendingUnpaused

private theorem cancelRedeem_run_zero
    (receiver : Address) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hUnpaused : s.storage 3 = 0) :
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run s =
      ContractResult.success () (cancelZeroPostState s receiver) := by
  unfold Contract.run
  rw [cancelRedeem_apply_zero receiver s hAuthority hVault hReceiver hPendingShares hPendingAssets hUnpaused]

/-- The successful nonzero cancellation path, expressed through its pending
writes and named ERC-20 transfer post-state. -/
private theorem cancelRedeem_apply_authorized
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0) :
    YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets true true s =
      ContractResult.success () (cancelledPostState s receiver shares grossAssets) := by
  have hGlobalGuard : s.storage 0 >= grossAssets := by
    simpa using hGlobalBound
  rw [YoAsyncRedemptionEscrow.cancelRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by simp [Verity.require, hPendingShares, hShareBound])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s () (by simp [Verity.require, hPendingAssets, hAssetBound])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 0 >= grossAssets)
    "Panic(0x11): arithmetic underflow") _ s s () (by
      simp [Verity.require, hGlobalGuard])]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver
      (sub (s.storageMap 6 receiver) shares)) _ s
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) ()
    (setMapping_apply_mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver
      (sub (s.storageMap 7 receiver) grossAssets)) _
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets)) ()
    (setMapping_apply_mapWriteState
      (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (sub (s.storage 0) grossAssets)) _
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))
    (pendingFulfillPostState s receiver shares grossAssets) () (by rfl)]
  rw [bind_apply_of_success Verity.contractAddress _
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets).thisAddress (by rfl)]
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVault
  have hPendingReceiver : receiver ≠ 0 := hReceiver
  have hPendingUnpaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hUnpaused
  have hPendingVaultShares : shares.val ≤
      ((pendingFulfillPostState s receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState s receiver shares grossAssets).thisAddress).val := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultShares
  simpa [cancelledPostState] using
    transfer_apply (pendingFulfillPostState s receiver shares grossAssets)
      (pendingFulfillPostState s receiver shares grossAssets).thisAddress receiver shares
      hPendingVault hPendingReceiver hPendingUnpaused hPendingVaultShares

private theorem cancelRedeem_run_true
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0) :
    (YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets true true).run s =
      ContractResult.success () (cancelledPostState s receiver shares grossAssets) := by
  unfold Contract.run
  rw [cancelRedeem_apply_authorized receiver shares grossAssets s hAuthority hVault hReceiver
    hPendingShares hPendingAssets hShareBound hAssetBound hGlobalBound hVaultShares hUnpaused]

/-- `_transfer` reaches its pause check before either balance read, on both
self and non-self paths. -/
private theorem transfer_apply_paused
    (s : ContractState) (fromAddr toAddr : Address) (shares : Uint256)
    (hFrom : fromAddr ≠ 0) (hTo : toAddr ≠ 0) (hPaused : s.storage 3 = 1) :
    YoAsyncRedemptionEscrow._transfer fromAddr toAddr shares s =
      ContractResult.revert "EnforcedPause" s := by
  rw [YoAsyncRedemptionEscrow._transfer]
  rw [bind_apply_of_success
    (Verity.require (fromAddr != zeroAddress) "ERC20InvalidSender") _ s s ()
    (by simp [Verity.require, zeroAddress, hFrom])]
  rw [bind_apply_of_success
    (Verity.require (toAddr != zeroAddress) "ERC20InvalidReceiver") _ s s ()
    (by simp [Verity.require, zeroAddress, hTo])]
  have hPauseGuard : (s.storage 3 == 0) = false := by
    simpa [hPaused] using (show ((1 : Uint256) == 0) = false by native_decide)
  by_cases hSelf : fromAddr = toAddr
  · subst toAddr
    rw [YoAsyncRedemptionEscrow._updateSelf]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
      (by rfl)]
    simp [Bind.bind, Verity.bind, Verity.require, hPauseGuard]
  · have hSelfBool : (fromAddr == toAddr) = false := by simp [hSelf]
    rw [hSelfBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [YoAsyncRedemptionEscrow._update]
    rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
      (by rfl)]
    simp [Bind.bind, Verity.bind, Verity.require, hPauseGuard]

private theorem cancelRedeem_apply_paused
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hPaused : s.storage 3 = 1) :
    YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets true true s =
      ContractResult.revert "EnforcedPause"
        (pendingFulfillPostState s receiver shares grossAssets) := by
  rw [YoAsyncRedemptionEscrow.cancelRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by
        simp [Verity.require, hPendingShares, hShareBound])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s () (by
        simp [Verity.require, hPendingAssets, hAssetBound])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storage 0 >= grossAssets) "Panic(0x11): arithmetic underflow") _ s s () (by
      simp [Verity.require, hGlobalBound])]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver (sub (s.storageMap 6 receiver) shares)) _ s
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) ()
    (setMapping_apply_mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver
      (sub (s.storageMap 7 receiver) grossAssets)) _
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets)) ()
    (setMapping_apply_mapWriteState
      (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (sub (s.storage 0) grossAssets)) _
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))
    (pendingFulfillPostState s receiver shares grossAssets) () (by rfl)]
  rw [bind_apply_of_success Verity.contractAddress _
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets).thisAddress (by rfl)]
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hVault
  have hPendingPaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 1 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hPaused
  simpa using transfer_apply_paused (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets).thisAddress receiver shares
    hPendingVault hReceiver hPendingPaused

private theorem cancelRedeem_run_paused
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val) :
    (YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets true true).run (pausedStateOf s) =
      ContractResult.revert "EnforcedPause" (pausedStateOf s) := by
  have hPausedAuthority : (pausedStateOf s).storageAddr 9 ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hAuthority
  have hPausedVault : (pausedStateOf s).thisAddress ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hVault
  have hPausedShares : (pausedStateOf s).storageMap 6 receiver ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hPendingShares
  have hPausedAssets : (pausedStateOf s).storageMap 7 receiver ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hPendingAssets
  have hPausedShareBound : shares.val ≤ ((pausedStateOf s).storageMap 6 receiver).val := by
    simpa [pausedStateOf, ContractState.writeSlot] using hShareBound
  have hPausedAssetBound : grossAssets.val ≤ ((pausedStateOf s).storageMap 7 receiver).val := by
    simpa [pausedStateOf, ContractState.writeSlot] using hAssetBound
  have hPausedGlobalBound : grossAssets.val ≤ ((pausedStateOf s).storage 0).val := by
    simpa [pausedStateOf, ContractState.writeSlot] using hGlobalBound
  have hPaused : (pausedStateOf s).storage 3 = 1 := by
    simp [pausedStateOf, ContractState.writeSlot]
  unfold Contract.run
  rw [cancelRedeem_apply_paused receiver shares grossAssets (pausedStateOf s)
    hPausedAuthority hPausedVault hReceiver hPausedShares hPausedAssets hPausedShareBound
    hPausedAssetBound hPausedGlobalBound hPaused]

/-- The source burn path has two named writes and no implicit reduction of a
large post-state. -/
private theorem burn_apply
    (s : ContractState) (shares : Uint256)
    (hVault : s.thisAddress ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val) :
    YoAsyncRedemptionEscrow._burn s.thisAddress shares s =
      ContractResult.success () (burnPostState s shares) := by
  have hBalance : s.storageMap 5 s.thisAddress >= shares := by
    simpa using hVaultShares
  rw [YoAsyncRedemptionEscrow._burn, YoAsyncRedemptionEscrow._update]
  rw [bind_apply_of_success
    (Verity.require (s.thisAddress != zeroAddress) "ERC20InvalidSender") _ s s ()
    (by simp [Verity.require, zeroAddress, hVault])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3) (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
    (by simp [Verity.require, hUnpaused])]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances s.thisAddress) _
    s s (s.storageMap 5 s.thisAddress) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 5 s.thisAddress >= shares) "ERC20InsufficientBalance") _ s s ()
    (by simp [Verity.require, hBalance])]
  simp only [zeroAddress, beq_self_eq_true, ↓reduceIte]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalSupply) _ s s (s.storage 4) (by rfl)]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.shareBalances s.thisAddress
      (sub (s.storageMap 5 s.thisAddress) shares)) _ s
    (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) shares)) ()
    (setMapping_apply_mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) shares))]
  change (setStorage YoAsyncRedemptionEscrow.totalSupply (sub (s.storage 4) shares))
      (mapWriteState s 5 s.thisAddress (sub (s.storageMap 5 s.thisAddress) shares)) = _
  rfl

/-- The corresponding burn calculation for an instant request's owner. -/
private theorem burn_apply_from
    (s : ContractState) (owner : Address) (shares : Uint256)
    (hOwner : owner ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hOwnerShares : shares.val ≤ (s.storageMap 5 owner).val) :
    YoAsyncRedemptionEscrow._burn owner shares s =
      ContractResult.success () (burnFromPostState s owner shares) := by
  have hBalance : s.storageMap 5 owner >= shares := by
    simpa using hOwnerShares
  rw [YoAsyncRedemptionEscrow._burn, YoAsyncRedemptionEscrow._update]
  rw [bind_apply_of_success
    (Verity.require (owner != zeroAddress) "ERC20InvalidSender") _ s s ()
    (by simp [Verity.require, zeroAddress, hOwner])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
    (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
    (by simp [Verity.require, hUnpaused])]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances owner) _ s s
    (s.storageMap 5 owner) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 5 owner >= shares) "ERC20InsufficientBalance") _ s s ()
    (by simp [Verity.require, hBalance])]
  simp only [zeroAddress, beq_self_eq_true, ↓reduceIte]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalSupply) _ s s (s.storage 4)
    (by rfl)]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.shareBalances owner
      (sub (s.storageMap 5 owner) shares)) _ s
    (mapWriteState s 5 owner (sub (s.storageMap 5 owner) shares)) ()
    (setMapping_apply_mapWriteState s 5 owner (sub (s.storageMap 5 owner) shares))]
  change (setStorage YoAsyncRedemptionEscrow.totalSupply (sub (s.storage 4) shares))
      (mapWriteState s 5 owner (sub (s.storageMap 5 owner) shares)) = _
  rfl

private theorem burn_run
    (s : ContractState) (shares : Uint256)
    (hVault : s.thisAddress ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val) :
    (YoAsyncRedemptionEscrow._burn s.thisAddress shares).run s =
      ContractResult.success () (burnPostState s shares) := by
  unfold Contract.run
  rw [burn_apply s shares hVault hUnpaused hVaultShares]

/-- A burn reaches the inherited pause guard before inspecting its balance. -/
private theorem burn_apply_paused
    (s : ContractState) (shares : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1) :
    YoAsyncRedemptionEscrow._burn s.thisAddress shares s =
      ContractResult.revert "EnforcedPause" s := by
  rw [YoAsyncRedemptionEscrow._burn, YoAsyncRedemptionEscrow._update]
  rw [bind_apply_of_success
    (Verity.require (s.thisAddress != zeroAddress) "ERC20InvalidSender") _ s s ()
    (by simp [Verity.require, zeroAddress, hVault])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
    (by rfl)]
  have hPauseGuard : (s.storage 3 == 0) = false := by
    simpa [hPaused] using (show ((1 : Uint256) == 0) = false by native_decide)
  simp [Bind.bind, Verity.bind, Verity.require, hPauseGuard]

/-- The post-read withdrawal suffix.  Keeping it as a separate contract avoids
asking the kernel to normalize the generated `_withdraw` body together with
its record-changing burn. -/
private def withdrawSuffix (owner receiver : Address) (shares feeAmount netAssets : Uint256)
    (recipient asset : Address) (receiverTransferSucceeds feeTransferSucceeds : Bool) : Contract Unit := do
  YoAsyncRedemptionEscrow._burn owner shares
  require receiverTransferSucceeds "SafeERC20FailedOperation"
  Contracts.safeTransfer asset receiver netAssets
  if feeAmount > 0 && recipient != zeroAddress then
    require feeTransferSucceeds "SafeERC20FailedOperation"
    Contracts.safeTransfer asset recipient feeAmount
  else
    Verity.pure ()

private def withdrawAfterAsset (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (recipient : Address) (receiverTransferSucceeds feeTransferSucceeds : Bool) : Contract Unit := do
  let asset ← getStorageAddr YoAsyncRedemptionEscrow.underlyingToken
  withdrawSuffix owner receiver shares feeAmount netAssets recipient asset
    receiverTransferSucceeds feeTransferSucceeds

private def withdrawAfterRecipient (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) : Contract Unit := do
  let recipient ← getStorageAddr YoAsyncRedemptionEscrow.feeRecipient
  withdrawAfterAsset s receiver owner grossAssets shares withdrawFee feeDivisor feeAmount netAssets recipient
    receiverTransferSucceeds feeTransferSucceeds

private def withdrawAfterNet (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee feeDivisor : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) : Contract Unit := do
  let feeAmount := mulDiv512Up grossAssets withdrawFee feeDivisor
  let netAssets ← requireSomeUint (safeSub grossAssets feeAmount)
    "Panic(0x11): arithmetic underflow"
  withdrawAfterRecipient s receiver owner grossAssets shares withdrawFee feeDivisor feeAmount netAssets
    receiverTransferSucceeds feeTransferSucceeds

private def withdrawAfterDivisor (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) : Contract Unit := do
  let feeDivisor ← requireSomeUint (safeAdd withdrawFee 1000000000000000000)
    "Panic(0x11): arithmetic overflow"
  withdrawAfterNet s receiver owner grossAssets shares withdrawFee feeDivisor
    receiverTransferSucceeds feeTransferSucceeds

private def withdrawPrefix (s : ContractState) (receiver owner : Address) (grossAssets shares : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) : Contract Unit := do
  let withdrawFee ← getStorage YoAsyncRedemptionEscrow.feeOnWithdraw
  withdrawAfterDivisor s receiver owner grossAssets shares withdrawFee
    receiverTransferSucceeds feeTransferSucceeds

private theorem withdraw_suffix_apply
    (s : ContractState) (receiver : Address) (shares feeAmount netAssets : Uint256)
    (recipient asset : Address)
    (hVault : s.thisAddress ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val) :
    withdrawSuffix s.thisAddress receiver shares feeAmount netAssets recipient asset true true s =
      ContractResult.success () (burnPostState s shares) := by
  unfold withdrawSuffix
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow._burn s.thisAddress shares) _ s
    (burnPostState s shares) () (burn_apply s shares hVault hUnpaused hVaultShares)]
  rw [bind_apply_of_success (Verity.require true "SafeERC20FailedOperation") _
    (burnPostState s shares) (burnPostState s shares) () (by rfl)]
  rw [bind_apply_of_success (Contracts.safeTransfer asset receiver netAssets) _
    (burnPostState s shares) (burnPostState s shares) () (by rfl)]
  by_cases hFeePositive : 0 < (feeAmount : Nat)
  · by_cases hRecipient : recipient ≠ zeroAddress
    · have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        have hRecipientBool : (recipient != zeroAddress) = true := by
          unfold bne
          rw [beq_eq_false_iff_ne.mpr hRecipient]
          rfl
        exact ⟨hFeePositive, hRecipientBool⟩
      rw [hFeeFlag]
      simp only [eq_self, ↓reduceIte]
      rw [bind_apply_of_success (Verity.require true "SafeERC20FailedOperation") _
        (burnPostState s shares) (burnPostState s shares) () (by rfl)]
      rfl
    · have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro h
        have hBoth : 0 < (feeAmount : Nat) ∧ recipient ≠ zeroAddress := by
          simpa using h
        exact hRecipient hBoth.2
      rw [hFeeFlag]
      rfl
  · have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro h
      have hBoth : 0 < (feeAmount : Nat) ∧ recipient ≠ zeroAddress := by
        simpa using h
      exact hFeePositive hBoth.1
    rw [hFeeFlag]
    rfl

private theorem withdraw_suffix_apply_paused
    (s : ContractState) (receiver : Address) (shares feeAmount netAssets : Uint256)
    (recipient asset : Address) (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1) :
    withdrawSuffix s.thisAddress receiver shares feeAmount netAssets recipient asset true true s =
      ContractResult.revert "EnforcedPause" s := by
  unfold withdrawSuffix
  exact bind_apply_of_revert (YoAsyncRedemptionEscrow._burn s.thisAddress shares) _ s s
    "EnforcedPause" (burn_apply_paused s shares hVault hPaused)

private theorem withdraw_after_asset_apply
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (recipient : Address)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val) :
    withdrawAfterAsset s receiver s.thisAddress grossAssets shares withdrawFee feeDivisor feeAmount netAssets
      recipient true true s = ContractResult.success () (burnPostState s shares) := by
  unfold withdrawAfterAsset
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.underlyingToken) _ s s
    (s.storageAddr 10) (by rfl)]
  exact withdraw_suffix_apply s receiver shares feeAmount netAssets recipient (s.storageAddr 10)
    hVault hUnpaused hVaultShares

private theorem withdraw_after_asset_apply_paused
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (recipient : Address) (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1) :
    withdrawAfterAsset s receiver s.thisAddress grossAssets shares withdrawFee feeDivisor feeAmount netAssets
      recipient true true s = ContractResult.revert "EnforcedPause" s := by
  unfold withdrawAfterAsset
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.underlyingToken) _ s s
    (s.storageAddr 10) (by rfl)]
  exact withdraw_suffix_apply_paused s receiver shares feeAmount netAssets recipient (s.storageAddr 10)
    hVault hPaused

private theorem withdraw_after_recipient_apply
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val) :
    withdrawAfterRecipient s receiver s.thisAddress grossAssets shares withdrawFee feeDivisor feeAmount netAssets
      true true s = ContractResult.success () (burnPostState s shares) := by
  unfold withdrawAfterRecipient
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.feeRecipient) _ s s
    (s.storageAddr 2) (by rfl)]
  exact withdraw_after_asset_apply s receiver shares grossAssets withdrawFee feeDivisor feeAmount netAssets
    (s.storageAddr 2) hVault hUnpaused hVaultShares

private theorem withdraw_after_recipient_apply_paused
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1) :
    withdrawAfterRecipient s receiver s.thisAddress grossAssets shares withdrawFee feeDivisor feeAmount netAssets
      true true s = ContractResult.revert "EnforcedPause" s := by
  unfold withdrawAfterRecipient
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.feeRecipient) _ s s
    (s.storageAddr 2) (by rfl)]
  exact withdraw_after_asset_apply_paused s receiver shares grossAssets withdrawFee feeDivisor feeAmount netAssets
    (s.storageAddr 2) hVault hPaused

private theorem withdraw_after_net_apply
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee feeDivisor : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hSub : requireSomeUint (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee feeDivisor))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) s) :
    withdrawAfterNet s receiver s.thisAddress grossAssets shares withdrawFee feeDivisor true true s =
      ContractResult.success () (burnPostState s shares) := by
  unfold withdrawAfterNet
  rw [bind_apply_of_success
    (requireSomeUint (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee feeDivisor))
      "Panic(0x11): arithmetic underflow") _ s s
    (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) hSub]
  exact withdraw_after_recipient_apply s receiver shares grossAssets withdrawFee feeDivisor
    (mulDiv512Up grossAssets withdrawFee feeDivisor)
    (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) hVault hUnpaused hVaultShares

private theorem withdraw_after_net_apply_paused
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee feeDivisor : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1)
    (hSub : requireSomeUint (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee feeDivisor))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) s) :
    withdrawAfterNet s receiver s.thisAddress grossAssets shares withdrawFee feeDivisor true true s =
      ContractResult.revert "EnforcedPause" s := by
  unfold withdrawAfterNet
  rw [bind_apply_of_success
    (requireSomeUint (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee feeDivisor))
      "Panic(0x11): arithmetic underflow") _ s s
    (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) hSub]
  exact withdraw_after_recipient_apply_paused s receiver shares grossAssets withdrawFee feeDivisor
    (mulDiv512Up grossAssets withdrawFee feeDivisor)
    (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) hVault hPaused

private theorem withdraw_after_divisor_apply
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hAdd : requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
        ContractResult.success (withdrawFee + 1000000000000000000) s)
    (hSub : requireSomeUint
      (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success
          (grossAssets - mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000)) s) :
    withdrawAfterDivisor s receiver s.thisAddress grossAssets shares withdrawFee true true s =
      ContractResult.success () (burnPostState s shares) := by
  unfold withdrawAfterDivisor
  rw [bind_apply_of_success
    (requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow") _ s s
    (withdrawFee + 1000000000000000000) hAdd]
  exact withdraw_after_net_apply s receiver shares grossAssets withdrawFee
    (withdrawFee + 1000000000000000000) hVault hUnpaused hVaultShares hSub

private theorem withdraw_after_divisor_apply_paused
    (s : ContractState) (receiver : Address) (shares grossAssets withdrawFee : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1)
    (hAdd : requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
        ContractResult.success (withdrawFee + 1000000000000000000) s)
    (hSub : requireSomeUint
      (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success
          (grossAssets - mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000)) s) :
    withdrawAfterDivisor s receiver s.thisAddress grossAssets shares withdrawFee true true s =
      ContractResult.revert "EnforcedPause" s := by
  unfold withdrawAfterDivisor
  rw [bind_apply_of_success
    (requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow") _ s s
    (withdrawFee + 1000000000000000000) hAdd]
  exact withdraw_after_net_apply_paused s receiver shares grossAssets withdrawFee
    (withdrawFee + 1000000000000000000) hVault hPaused hSub

private theorem withdraw_prefix_apply
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hAdd : requireSomeUint (safeAdd (s.storage 1) 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
        ContractResult.success (s.storage 1 + 1000000000000000000) s)
    (hSub : requireSomeUint
      (safeSub grossAssets
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success
          (grossAssets - mulDiv512Up grossAssets (s.storage 1)
            (s.storage 1 + 1000000000000000000)) s) :
    withdrawPrefix s receiver s.thisAddress grossAssets shares true true s =
      ContractResult.success () (burnPostState s shares) := by
  unfold withdrawPrefix
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.feeOnWithdraw) _ s s
    (s.storage 1) (by rfl)]
  exact withdraw_after_divisor_apply s receiver shares grossAssets (s.storage 1)
    hVault hUnpaused hVaultShares hAdd hSub

private theorem withdraw_prefix_apply_paused
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1)
    (hAdd : requireSomeUint (safeAdd (s.storage 1) 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
        ContractResult.success (s.storage 1 + 1000000000000000000) s)
    (hSub : requireSomeUint
      (safeSub grossAssets
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success
          (grossAssets - mulDiv512Up grossAssets (s.storage 1)
            (s.storage 1 + 1000000000000000000)) s) :
    withdrawPrefix s receiver s.thisAddress grossAssets shares true true s =
      ContractResult.revert "EnforcedPause" s := by
  unfold withdrawPrefix
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.feeOnWithdraw) _ s s
    (s.storage 1) (by rfl)]
  exact withdraw_after_divisor_apply_paused s receiver shares grossAssets (s.storage 1)
    hVault hPaused hAdd hSub

/-- A continuation form of the staged evaluator, used for the two modeled
SafeERC20 failure boundaries. -/
private theorem withdraw_after_asset_of_suffix
    (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (recipient : Address) (receiverTransferSucceeds feeTransferSucceeds : Bool)
    (result : ContractResult Unit)
    (hSuffix : withdrawSuffix owner receiver shares feeAmount netAssets recipient (s.storageAddr 10)
      receiverTransferSucceeds feeTransferSucceeds s = result) :
    withdrawAfterAsset s receiver owner grossAssets shares withdrawFee feeDivisor feeAmount netAssets recipient
      receiverTransferSucceeds feeTransferSucceeds s = result := by
  unfold withdrawAfterAsset
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.underlyingToken) _ s s
    (s.storageAddr 10) (by rfl)]
  exact hSuffix

private theorem withdraw_after_recipient_of_suffix
    (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee feeDivisor feeAmount netAssets : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) (result : ContractResult Unit)
    (hSuffix : withdrawSuffix owner receiver shares feeAmount netAssets (s.storageAddr 2) (s.storageAddr 10)
      receiverTransferSucceeds feeTransferSucceeds s = result) :
    withdrawAfterRecipient s receiver owner grossAssets shares withdrawFee feeDivisor feeAmount netAssets
      receiverTransferSucceeds feeTransferSucceeds s = result := by
  unfold withdrawAfterRecipient
  rw [bind_apply_of_success (getStorageAddr YoAsyncRedemptionEscrow.feeRecipient) _ s s
    (s.storageAddr 2) (by rfl)]
  exact withdraw_after_asset_of_suffix s receiver owner grossAssets shares withdrawFee feeDivisor feeAmount netAssets
    (s.storageAddr 2) receiverTransferSucceeds feeTransferSucceeds result hSuffix

private theorem withdraw_after_net_of_suffix
    (s : ContractState) (receiver owner : Address)
    (grossAssets shares withdrawFee feeDivisor : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) (result : ContractResult Unit)
    (hSub : requireSomeUint (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee feeDivisor))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) s)
    (hSuffix : withdrawSuffix owner receiver shares
      (mulDiv512Up grossAssets withdrawFee feeDivisor)
      (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor)
      (s.storageAddr 2) (s.storageAddr 10) receiverTransferSucceeds feeTransferSucceeds s = result) :
    withdrawAfterNet s receiver owner grossAssets shares withdrawFee feeDivisor
      receiverTransferSucceeds feeTransferSucceeds s = result := by
  unfold withdrawAfterNet
  rw [bind_apply_of_success
    (requireSomeUint (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee feeDivisor))
      "Panic(0x11): arithmetic underflow") _ s s
    (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor) hSub]
  exact withdraw_after_recipient_of_suffix s receiver owner grossAssets shares withdrawFee feeDivisor
    (mulDiv512Up grossAssets withdrawFee feeDivisor)
    (grossAssets - mulDiv512Up grossAssets withdrawFee feeDivisor)
    receiverTransferSucceeds feeTransferSucceeds result hSuffix

private theorem withdraw_after_divisor_of_suffix
    (s : ContractState) (receiver owner : Address) (grossAssets shares withdrawFee : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) (result : ContractResult Unit)
    (hAdd : requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
        ContractResult.success (withdrawFee + 1000000000000000000) s)
    (hSub : requireSomeUint
      (safeSub grossAssets (mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success
          (grossAssets - mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000)) s)
    (hSuffix : withdrawSuffix owner receiver shares
      (mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000))
      (grossAssets - mulDiv512Up grossAssets withdrawFee (withdrawFee + 1000000000000000000))
      (s.storageAddr 2) (s.storageAddr 10) receiverTransferSucceeds feeTransferSucceeds s = result) :
    withdrawAfterDivisor s receiver owner grossAssets shares withdrawFee
      receiverTransferSucceeds feeTransferSucceeds s = result := by
  unfold withdrawAfterDivisor
  rw [bind_apply_of_success
    (requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow") _ s s
    (withdrawFee + 1000000000000000000) hAdd]
  exact withdraw_after_net_of_suffix s receiver owner grossAssets shares withdrawFee
    (withdrawFee + 1000000000000000000) receiverTransferSucceeds feeTransferSucceeds result hSub hSuffix

private theorem withdraw_prefix_of_suffix
    (s : ContractState) (receiver owner : Address) (grossAssets shares : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) (result : ContractResult Unit)
    (hAdd : requireSomeUint (safeAdd (s.storage 1) 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
        ContractResult.success (s.storage 1 + 1000000000000000000) s)
    (hSub : requireSomeUint
      (safeSub grossAssets
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
        ContractResult.success
          (grossAssets - mulDiv512Up grossAssets (s.storage 1)
            (s.storage 1 + 1000000000000000000)) s)
    (hSuffix : withdrawSuffix owner receiver shares
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
      (grossAssets - mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
      (s.storageAddr 2) (s.storageAddr 10) receiverTransferSucceeds feeTransferSucceeds s = result) :
    withdrawPrefix s receiver owner grossAssets shares
      receiverTransferSucceeds feeTransferSucceeds s = result := by
  unfold withdrawPrefix
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.feeOnWithdraw) _ s s
    (s.storage 1) (by rfl)]
  exact withdraw_after_divisor_of_suffix s receiver owner grossAssets shares (s.storage 1)
    receiverTransferSucceeds feeTransferSucceeds result hAdd hSub hSuffix

private theorem withdraw_suffix_receiver_revert
    (s : ContractState) (receiver : Address) (shares feeAmount netAssets : Uint256)
    (recipient asset : Address)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val) :
    withdrawSuffix s.thisAddress receiver shares feeAmount netAssets recipient asset false true s =
      ContractResult.revert "SafeERC20FailedOperation" (burnPostState s shares) := by
  unfold withdrawSuffix
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow._burn s.thisAddress shares) _ s
    (burnPostState s shares) () (burn_apply s shares hVault hUnpaused hVaultShares)]
  exact bind_apply_of_revert (Verity.require false "SafeERC20FailedOperation") _
    (burnPostState s shares) (burnPostState s shares) "SafeERC20FailedOperation" (by rfl)

private theorem withdraw_suffix_fee_revert
    (s : ContractState) (receiver : Address) (shares feeAmount netAssets : Uint256)
    (recipient asset : Address)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hFeePositive : 0 < (feeAmount : Nat)) (hRecipient : recipient ≠ zeroAddress) :
    withdrawSuffix s.thisAddress receiver shares feeAmount netAssets recipient asset true false s =
      ContractResult.revert "SafeERC20FailedOperation" (burnPostState s shares) := by
  unfold withdrawSuffix
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow._burn s.thisAddress shares) _ s
    (burnPostState s shares) () (burn_apply s shares hVault hUnpaused hVaultShares)]
  rw [bind_apply_of_success (Verity.require true "SafeERC20FailedOperation") _
    (burnPostState s shares) (burnPostState s shares) () (by rfl)]
  rw [bind_apply_of_success (Contracts.safeTransfer asset receiver netAssets) _
    (burnPostState s shares) (burnPostState s shares) () (by rfl)]
  have hRecipientBool : (recipient != zeroAddress) = true := by
    unfold bne
    rw [beq_eq_false_iff_ne.mpr hRecipient]
    rfl
  have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using ⟨hFeePositive, hRecipientBool⟩
  rw [hFeeFlag]
  simp only [eq_self, ↓reduceIte]
  exact bind_apply_of_revert (Verity.require false "SafeERC20FailedOperation") _
    (burnPostState s shares) (burnPostState s shares) "SafeERC20FailedOperation" (by rfl)

private theorem withdraw_fee_add_apply (s : ContractState)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256) :
    requireSomeUint (safeAdd (s.storage 1) 1000000000000000000)
      "Panic(0x11): arithmetic overflow" s =
      ContractResult.success (s.storage 1 + 1000000000000000000) s := by
  have hFeeAddSafe := Verity.Proofs.Stdlib.Automation.safeAdd_some_val _ _ hFeeAdd
  rw [hFeeAddSafe]
  rfl

private theorem withdraw_fee_sub_apply (s : ContractState) (grossAssets : Uint256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    requireSomeUint
      (safeSub grossAssets
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000)))
      "Panic(0x11): arithmetic underflow" s =
      ContractResult.success
        (grossAssets - mulDiv512Up grossAssets (s.storage 1)
          (s.storage 1 + 1000000000000000000)) s := by
  have hDivisor : s.storage 1 + 1000000000000000000 =
      1000000000000000000 + s.storage 1 :=
    Verity.Core.Uint256.add_comm _ _
  have hSubBound : (grossAssets : Nat) ≥
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000) : Nat) := by
    rw [hDivisor]
    exact Nat.le_of_not_gt hFeeSub
  have hFeeSubSafe := Verity.Proofs.Stdlib.Automation.safeSub_some_val _ _ hSubBound
  rw [hFeeSubSafe]
  rfl

private theorem withdraw_prefix_apply_checked
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    withdrawPrefix s receiver s.thisAddress grossAssets shares true true s =
      ContractResult.success () (burnPostState s shares) := by
  exact withdraw_prefix_apply s receiver shares grossAssets hVault hUnpaused hVaultShares
    (withdraw_fee_add_apply s hFeeAdd) (withdraw_fee_sub_apply s grossAssets hFeeSub)

private theorem withdraw_prefix_apply_checked_paused
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    withdrawPrefix s receiver s.thisAddress grossAssets shares true true s =
      ContractResult.revert "EnforcedPause" s := by
  exact withdraw_prefix_apply_paused s receiver shares grossAssets hVault hPaused
    (withdraw_fee_add_apply s hFeeAdd) (withdraw_fee_sub_apply s grossAssets hFeeSub)

/-- The full source function is linked to the staged evaluator only at this
small definitional boundary. -/
private theorem withdraw_source_eq_prefix
    (s : ContractState) (receiver : Address) (grossAssets shares : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) :
    YoAsyncRedemptionEscrow._withdraw receiver s.thisAddress grossAssets shares
      receiverTransferSucceeds feeTransferSucceeds =
      withdrawPrefix s receiver s.thisAddress grossAssets shares
        receiverTransferSucceeds feeTransferSucceeds := by
  rfl

private theorem withdraw_apply
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    YoAsyncRedemptionEscrow._withdraw receiver s.thisAddress grossAssets shares true true s =
      ContractResult.success () (burnPostState s shares) := by
  exact Eq.trans
    (congrFun (withdraw_source_eq_prefix s receiver grossAssets shares true true) s)
    (withdraw_prefix_apply_checked s receiver shares grossAssets hVault hUnpaused hVaultShares hFeeAdd hFeeSub)

/-- A zero fee recipient bypasses the conditional second transfer, even when
its trusted transfer-outcome flag is `false`. -/
private theorem withdraw_apply_zero_fee_recipient
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat))
    (hFeeRecipient : s.storageAddr 2 = zeroAddress) :
    YoAsyncRedemptionEscrow._withdraw receiver s.thisAddress grossAssets shares true false s =
      ContractResult.success () (burnPostState s shares) := by
  have hSuffix : withdrawSuffix s.thisAddress receiver shares
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
      (grossAssets - mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
      (s.storageAddr 2) (s.storageAddr 10) true false s =
        ContractResult.success () (burnPostState s shares) := by
    unfold withdrawSuffix
    rw [bind_apply_of_success (YoAsyncRedemptionEscrow._burn s.thisAddress shares) _ s
      (burnPostState s shares) () (burn_apply s shares hVault hUnpaused hVaultShares)]
    rw [bind_apply_of_success (Verity.require true "SafeERC20FailedOperation") _
      (burnPostState s shares) (burnPostState s shares) () (by rfl)]
    rw [bind_apply_of_success (Contracts.safeTransfer (s.storageAddr 10) receiver
      (grossAssets - mulDiv512Up grossAssets (s.storage 1)
        (s.storage 1 + 1000000000000000000))) _
      (burnPostState s shares) (burnPostState s shares) () (by rfl)]
    have hFeeFlag :
        (decide (mulDiv512Up grossAssets (s.storage 1)
          (s.storage 1 + 1000000000000000000) > 0) && s.storageAddr 2 != zeroAddress) = false := by
      simp [hFeeRecipient]
    rw [hFeeFlag]
    rfl
  exact Eq.trans
    (congrFun (withdraw_source_eq_prefix s receiver grossAssets shares true false) s)
    (withdraw_prefix_of_suffix s receiver s.thisAddress grossAssets shares true false
      (ContractResult.success () (burnPostState s shares))
      (withdraw_fee_add_apply s hFeeAdd) (withdraw_fee_sub_apply s grossAssets hFeeSub) hSuffix)

/-- A successful withdrawal suffix when the burned account is an arbitrary
request owner instead of the vault pool. -/
private theorem withdraw_suffix_apply_from
    (s : ContractState) (receiver owner : Address) (shares feeAmount netAssets : Uint256)
    (recipient asset : Address)
    (hOwner : owner ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hOwnerShares : shares.val ≤ (s.storageMap 5 owner).val) :
    withdrawSuffix owner receiver shares feeAmount netAssets recipient asset true true s =
      ContractResult.success () (burnFromPostState s owner shares) := by
  unfold withdrawSuffix
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow._burn owner shares) _ s
    (burnFromPostState s owner shares) ()
    (burn_apply_from s owner shares hOwner hUnpaused hOwnerShares)]
  rw [bind_apply_of_success (Verity.require true "SafeERC20FailedOperation") _
    (burnFromPostState s owner shares) (burnFromPostState s owner shares) () (by rfl)]
  rw [bind_apply_of_success (Contracts.safeTransfer asset receiver netAssets) _
    (burnFromPostState s owner shares) (burnFromPostState s owner shares) () (by rfl)]
  by_cases hFeePositive : 0 < (feeAmount : Nat)
  · by_cases hRecipient : recipient ≠ zeroAddress
    · have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        have hRecipientBool : (recipient != zeroAddress) = true := by
          unfold bne
          rw [beq_eq_false_iff_ne.mpr hRecipient]
          rfl
        exact ⟨hFeePositive, hRecipientBool⟩
      rw [hFeeFlag]
      simp only [eq_self, ↓reduceIte]
      rw [bind_apply_of_success (Verity.require true "SafeERC20FailedOperation") _
        (burnFromPostState s owner shares) (burnFromPostState s owner shares) () (by rfl)]
      rfl
    · have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro h
        have hBoth : 0 < (feeAmount : Nat) ∧ recipient ≠ zeroAddress := by
          simpa using h
        exact hRecipient hBoth.2
      rw [hFeeFlag]
      rfl
  · have hFeeFlag : (decide (feeAmount > 0) && recipient != zeroAddress) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro h
      have hBoth : 0 < (feeAmount : Nat) ∧ recipient ≠ zeroAddress := by
        simpa using h
      exact hFeePositive hBoth.1
    rw [hFeeFlag]
    rfl

private theorem withdraw_source_eq_prefix_from
    (s : ContractState) (receiver owner : Address) (grossAssets shares : Uint256)
    (receiverTransferSucceeds feeTransferSucceeds : Bool) :
    YoAsyncRedemptionEscrow._withdraw receiver owner grossAssets shares
      receiverTransferSucceeds feeTransferSucceeds =
      withdrawPrefix s receiver owner grossAssets shares
        receiverTransferSucceeds feeTransferSucceeds := by
  rfl

/-- Execute an instant request withdrawal through the existing staged fee
evaluator, retaining the request owner's exact burn post-state. -/
private theorem withdraw_apply_from
    (s : ContractState) (receiver owner : Address) (shares grossAssets : Uint256)
    (hOwner : owner ≠ 0)
    (hUnpaused : s.storage 3 = 0)
    (hOwnerShares : shares.val ≤ (s.storageMap 5 owner).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    YoAsyncRedemptionEscrow._withdraw receiver owner grossAssets shares true true s =
      ContractResult.success () (burnFromPostState s owner shares) := by
  exact Eq.trans
    (congrFun (withdraw_source_eq_prefix_from s receiver owner grossAssets shares true true) s)
    (withdraw_prefix_of_suffix s receiver owner grossAssets shares true true
      (ContractResult.success () (burnFromPostState s owner shares))
      (withdraw_fee_add_apply s hFeeAdd) (withdraw_fee_sub_apply s grossAssets hFeeSub)
      (withdraw_suffix_apply_from s receiver owner shares
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
        (grossAssets - mulDiv512Up grossAssets (s.storage 1)
          (s.storage 1 + 1000000000000000000))
        (s.storageAddr 2) (s.storageAddr 10) hOwner hUnpaused hOwnerShares))

/-- Execute the instant branch of `requestRedeem` while retaining the request
owner's burn post-state. -/
private theorem requestRedeem_instant_run
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (s : ContractState)
    (hOwner : owner ≠ 0)
    (hReceiver : receiver ≠ 0)
    (hOwnerIsSender : owner = s.sender)
    (hUnpaused : s.storage 3 = 0)
    (hSharesPositive : shares > 0)
    (hOwnerShares : shares.val ≤ (s.storageMap 5 owner).val)
    (hInstant :
      (if externalUnderlyingBalance > s.storage 0 then
        sub externalUnderlyingBalance (s.storage 0)
      else 0) >= grossAssets)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
      externalUnderlyingBalance true true true true).run s =
      ContractResult.success grossAssets (burnFromPostState s owner shares) := by
  have hOwnerBalance : s.storageMap 5 owner >= shares := by
    simpa using hOwnerShares
  have hSharesNonzero : shares.val ≠ 0 := by
    exact Nat.ne_of_gt (by simpa using hSharesPositive)
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.requestRedeem]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.paused) _ s s (s.storage 3)
    (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 3 == 0) "EnforcedPause") _ s s ()
    (by simp [Verity.require, hUnpaused])]
  rw [bind_apply_of_success Verity.msgSender _ s s s.sender (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.shareBalances owner) _ s s
    (s.storageMap 5 owner) (by rfl)]
  rw [bind_apply_of_success (Verity.require (receiver != zeroAddress) "ZeroReceiver") _ s s ()
    (by simp [Verity.require, zeroAddress, hReceiver])]
  rw [bind_apply_of_success (Verity.require (shares > 0) "SharesAmountZero") _ s s ()
    (by simp [Verity.require, hSharesNonzero])]
  rw [bind_apply_of_success (Verity.require (owner == s.sender) "NotSharesOwner") _ s s ()
    (by simp [Verity.require, hOwnerIsSender])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 5 owner >= shares) "InsufficientShares") _ s s ()
    (by simp [Verity.require, hOwnerBalance])]
  rw [bind_apply_of_success (Verity.require true "PreviewRedeemFailed") _ s s () (by rfl)]
  rw [bind_apply_of_success (Verity.require true "UnderlyingBalanceReadFailed") _ s s () (by rfl)]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow._getAvailableBalance externalUnderlyingBalance) _
    s s _ (getAvailableBalance_apply externalUnderlyingBalance s)]
  simp only [hInstant, ↓reduceIte]
  rw [bind_apply_of_success
    (YoAsyncRedemptionEscrow._withdraw receiver owner grossAssets shares true true) _ s
    (burnFromPostState s owner shares) ()
    (withdraw_apply_from s receiver owner shares grossAssets hOwner hUnpaused hOwnerShares
      hFeeAdd hFeeSub)]
  rfl

private theorem withdraw_apply_paused
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hPaused : s.storage 3 = 1)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    YoAsyncRedemptionEscrow._withdraw receiver s.thisAddress grossAssets shares true true s =
      ContractResult.revert "EnforcedPause" s := by
  exact Eq.trans
    (congrFun (withdraw_source_eq_prefix s receiver grossAssets shares true true) s)
    (withdraw_prefix_apply_checked_paused s receiver shares grossAssets hVault hPaused hFeeAdd hFeeSub)

private theorem withdraw_apply_receiver_revert
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    YoAsyncRedemptionEscrow._withdraw receiver s.thisAddress grossAssets shares false true s =
      ContractResult.revert "SafeERC20FailedOperation" (burnPostState s shares) := by
  exact Eq.trans
    (congrFun (withdraw_source_eq_prefix s receiver grossAssets shares false true) s)
    (withdraw_prefix_of_suffix s receiver s.thisAddress grossAssets shares false true
      (ContractResult.revert "SafeERC20FailedOperation" (burnPostState s shares))
      (withdraw_fee_add_apply s hFeeAdd) (withdraw_fee_sub_apply s grossAssets hFeeSub)
      (withdraw_suffix_receiver_revert s receiver shares
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
        (grossAssets - mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
        (s.storageAddr 2) (s.storageAddr 10) hVault hUnpaused hVaultShares))

private theorem withdraw_apply_fee_revert
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256)
    (hVault : s.thisAddress ≠ 0) (hUnpaused : s.storage 3 = 0)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat))
    (hFeePositive : 0 <
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000) : Nat))
    (hRecipient : s.storageAddr 2 ≠ 0) :
    YoAsyncRedemptionEscrow._withdraw receiver s.thisAddress grossAssets shares true false s =
      ContractResult.revert "SafeERC20FailedOperation" (burnPostState s shares) := by
  exact Eq.trans
    (congrFun (withdraw_source_eq_prefix s receiver grossAssets shares true false) s)
    (withdraw_prefix_of_suffix s receiver s.thisAddress grossAssets shares true false
      (ContractResult.revert "SafeERC20FailedOperation" (burnPostState s shares))
      (withdraw_fee_add_apply s hFeeAdd) (withdraw_fee_sub_apply s grossAssets hFeeSub)
      (withdraw_suffix_fee_revert s receiver shares
        (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
        (grossAssets - mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000))
        (s.storageAddr 2) (s.storageAddr 10) hVault hUnpaused hVaultShares hFeePositive
        (by simpa [zeroAddress] using hRecipient)))

/-- Concrete successful fulfillment state. -/
private def fulfilledPostState
    (s : ContractState) (receiver : Address) (shares grossAssets : Uint256) : ContractState :=
  burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares

/-- Execute fulfillment by composing named pending writes with the named burn
path.  This avoids kernel reduction through a five-layer record literal. -/
private theorem fulfillRedeem_apply_authorized
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (authorityAllows : Bool)
    (hAuthorized :
      YoAsyncRedemptionEscrow.isAuthorized true authorityAllows s =
        ContractResult.success true s)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) <= MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows true true s =
      ContractResult.success () (fulfilledPostState s receiver shares grossAssets) := by
  have hShareGuard : (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver) = true := by
    simp [hPendingShares, hShareBound]
  have hAssetGuard : (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver) = true := by
    simp [hPendingAssets, hAssetBound]
  have hGlobalGuard : s.storage 0 >= grossAssets := by
    simpa using hGlobalBound
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true authorityAllows) _ s s true hAuthorized]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by
        simp [Verity.require, hPendingShares, hShareBound])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s () (by
        simp [Verity.require, hPendingAssets, hAssetBound])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 0 >= grossAssets)
    "Panic(0x11): arithmetic underflow") _ s s ()
    (by simp [Verity.require, hGlobalGuard])]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver
      (sub (s.storageMap 6 receiver) shares)) _ s
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) ()
    (setMapping_apply_mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver
      (sub (s.storageMap 7 receiver) grossAssets)) _
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets)) ()
    (setMapping_apply_mapWriteState
      (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (sub (s.storage 0) grossAssets)) _
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))
    (pendingFulfillPostState s receiver shares grossAssets) () (by rfl)]
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress = s.thisAddress := rfl
  have hPendingUnpaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 0 := by
    simp [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hUnpaused]
  have hPendingVaultShares : shares.val ≤
      ((pendingFulfillPostState s receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState s receiver shares grossAssets).thisAddress).val := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultShares
  have hPendingFeeAdd :
      ((pendingFulfillPostState s receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeAdd
  have hPendingFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        (1000000000000000000 + (pendingFulfillPostState s receiver shares grossAssets).storage 1) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeSub
  rw [bind_apply_of_success Verity.contractAddress _
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets).thisAddress (by rfl)]
  simpa [fulfilledPostState, hPendingVault] using
    withdraw_apply (pendingFulfillPostState s receiver shares grossAssets) receiver shares grossAssets
      (by simpa [hPendingVault] using hVault) hPendingUnpaused hPendingVaultShares hPendingFeeAdd hPendingFeeSub

private theorem fulfillRedeem_apply_authorized_of_withdraw
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (authorityAllows receiverTransferSucceeds feeTransferSucceeds : Bool) (result : ContractResult Unit)
    (hAuthorized : YoAsyncRedemptionEscrow.isAuthorized true authorityAllows s =
      ContractResult.success true s)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hWithdraw : YoAsyncRedemptionEscrow._withdraw receiver
      (pendingFulfillPostState s receiver shares grossAssets).thisAddress grossAssets shares
      receiverTransferSucceeds feeTransferSucceeds
      (pendingFulfillPostState s receiver shares grossAssets) = result) :
    YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows
      receiverTransferSucceeds feeTransferSucceeds s = result := by
  have hShareGuard : (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver) = true := by
    simp [hPendingShares, hShareBound]
  have hAssetGuard : (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver) = true := by
    simp [hPendingAssets, hAssetBound]
  have hGlobalGuard : s.storage 0 >= grossAssets := by
    simpa using hGlobalBound
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true authorityAllows) _ s s true hAuthorized]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by
        simp [Verity.require, hPendingShares, hShareBound])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s () (by
        simp [Verity.require, hPendingAssets, hAssetBound])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success (Verity.require (s.storage 0 >= grossAssets)
    "Panic(0x11): arithmetic underflow") _ s s () (by
      simp [Verity.require, hGlobalGuard])]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver
      (sub (s.storageMap 6 receiver) shares)) _ s
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) ()
    (setMapping_apply_mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver
      (sub (s.storageMap 7 receiver) grossAssets)) _
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets)) ()
    (setMapping_apply_mapWriteState
      (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (sub (s.storage 0) grossAssets)) _
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))
    (pendingFulfillPostState s receiver shares grossAssets) () (by rfl)]
  rw [bind_apply_of_success Verity.contractAddress _
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets).thisAddress (by rfl)]
  exact hWithdraw

private theorem fulfillRedeem_run_authority_revert
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets false false true true).run s =
      ContractResult.revert "AuthorityCanCallReverted" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_revert (YoAsyncRedemptionEscrow.isAuthorized false false) _ s s
    "AuthorityCanCallReverted" (isAuthorized_false_apply s hAuthority)]

private theorem cancelRedeem_run_authority_revert
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0) :
    (YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets false false).run s =
      ContractResult.revert "AuthorityCanCallReverted" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.cancelRedeem]
  rw [bind_apply_of_revert (YoAsyncRedemptionEscrow.isAuthorized false false) _ s s
    "AuthorityCanCallReverted" (isAuthorized_false_apply s hAuthority)]

private theorem fulfillRedeem_run_receiver_revert
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0) (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true false true).run s =
      ContractResult.revert "SafeERC20FailedOperation" s := by
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hVault
  have hPendingUnpaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hUnpaused
  have hPendingVaultShares : shares.val ≤
      ((pendingFulfillPostState s receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState s receiver shares grossAssets).thisAddress).val := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultShares
  have hPendingFeeAdd :
      ((pendingFulfillPostState s receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeAdd
  have hPendingFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        (1000000000000000000 + (pendingFulfillPostState s receiver shares grossAssets).storage 1) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeSub
  have hWithdraw : YoAsyncRedemptionEscrow._withdraw receiver
      (pendingFulfillPostState s receiver shares grossAssets).thisAddress grossAssets shares false true
      (pendingFulfillPostState s receiver shares grossAssets) =
        ContractResult.revert "SafeERC20FailedOperation"
          (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares) :=
    withdraw_apply_receiver_revert (pendingFulfillPostState s receiver shares grossAssets)
      receiver shares grossAssets hPendingVault hPendingUnpaused hPendingVaultShares hPendingFeeAdd hPendingFeeSub
  have hRaw := fulfillRedeem_apply_authorized_of_withdraw receiver shares grossAssets s true false true
    (ContractResult.revert "SafeERC20FailedOperation"
      (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares))
    (isAuthorized_true_true_apply s hAuthority) hPendingShares hPendingAssets hShareBound hAssetBound
    hGlobalBound hWithdraw
  unfold Contract.run
  rw [hRaw]

private theorem fulfillRedeem_run_fee_revert
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0) (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat))
    (hFeePositive : 0 <
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000) : Nat))
    (hFeeRecipient : s.storageAddr 2 ≠ 0) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true false).run s =
      ContractResult.revert "SafeERC20FailedOperation" s := by
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hVault
  have hPendingUnpaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hUnpaused
  have hPendingVaultShares : shares.val ≤
      ((pendingFulfillPostState s receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState s receiver shares grossAssets).thisAddress).val := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultShares
  have hPendingFeeAdd :
      ((pendingFulfillPostState s receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeAdd
  have hPendingFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        (1000000000000000000 + (pendingFulfillPostState s receiver shares grossAssets).storage 1) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeSub
  have hPendingFeePositive : 0 <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        ((pendingFulfillPostState s receiver shares grossAssets).storage 1 + 1000000000000000000) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeePositive
  have hPendingRecipient : (pendingFulfillPostState s receiver shares grossAssets).storageAddr 2 ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeRecipient
  have hWithdraw : YoAsyncRedemptionEscrow._withdraw receiver
      (pendingFulfillPostState s receiver shares grossAssets).thisAddress grossAssets shares true false
      (pendingFulfillPostState s receiver shares grossAssets) =
        ContractResult.revert "SafeERC20FailedOperation"
          (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares) :=
    withdraw_apply_fee_revert (pendingFulfillPostState s receiver shares grossAssets)
      receiver shares grossAssets hPendingVault hPendingUnpaused hPendingVaultShares hPendingFeeAdd hPendingFeeSub
      hPendingFeePositive hPendingRecipient
  have hRaw := fulfillRedeem_apply_authorized_of_withdraw receiver shares grossAssets s true true false
    (ContractResult.revert "SafeERC20FailedOperation"
      (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares))
    (isAuthorized_true_true_apply s hAuthority) hPendingShares hPendingAssets hShareBound hAssetBound
    hGlobalBound hWithdraw
  unfold Contract.run
  rw [hRaw]

private theorem fulfillRedeem_run_true
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) <= MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s =
      ContractResult.success () (fulfilledPostState s receiver shares grossAssets) := by
  unfold Contract.run
  rw [fulfillRedeem_apply_authorized receiver shares grossAssets s true
    (isAuthorized_true_true_apply s hAuthority) hAuthority hVault hPendingShares hPendingAssets
    hShareBound hAssetBound hGlobalBound hVaultShares hUnpaused hFeeAdd hFeeSub]

private theorem fulfillRedeem_run_authorized
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (authorityAllows : Bool)
    (hAuthorized :
      YoAsyncRedemptionEscrow.isAuthorized true authorityAllows s =
        ContractResult.success true s)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) <= MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows true true).run s =
      ContractResult.success () (fulfilledPostState s receiver shares grossAssets) := by
  unfold Contract.run
  rw [fulfillRedeem_apply_authorized receiver shares grossAssets s authorityAllows hAuthorized
    hAuthority hVault hPendingShares hPendingAssets hShareBound hAssetBound hGlobalBound hVaultShares
    hUnpaused hFeeAdd hFeeSub]

private theorem fulfillRedeem_apply_paused
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hPaused : s.storage 3 = 1)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true s =
      ContractResult.revert "EnforcedPause"
        (pendingFulfillPostState s receiver shares grossAssets) := by
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by
        simp [Verity.require, hPendingShares, hShareBound])]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 7 receiver != 0 && grossAssets <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s () (by
        simp [Verity.require, hPendingAssets, hAssetBound])]
  rw [bind_apply_of_success (getStorage YoAsyncRedemptionEscrow.totalPendingAssets) _ s s
    (s.storage 0) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storage 0 >= grossAssets) "Panic(0x11): arithmetic underflow") _ s s () (by
      simp [Verity.require, hGlobalBound])]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingShares receiver (sub (s.storageMap 6 receiver) shares)) _ s
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) ()
    (setMapping_apply_mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))]
  rw [bind_apply_of_success
    (setMapping YoAsyncRedemptionEscrow.pendingAssets receiver
      (sub (s.storageMap 7 receiver) grossAssets)) _
    (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares))
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets)) ()
    (setMapping_apply_mapWriteState
      (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))]
  rw [bind_apply_of_success
    (setStorage YoAsyncRedemptionEscrow.totalPendingAssets (sub (s.storage 0) grossAssets)) _
    (mapWriteState (mapWriteState s 6 receiver (sub (s.storageMap 6 receiver) shares)) 7 receiver
      (sub (s.storageMap 7 receiver) grossAssets))
    (pendingFulfillPostState s receiver shares grossAssets) () (by rfl)]
  rw [bind_apply_of_success Verity.contractAddress _
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets)
    (pendingFulfillPostState s receiver shares grossAssets).thisAddress (by rfl)]
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hVault
  have hPendingPaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 1 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hPaused
  have hPendingFeeAdd :
      ((pendingFulfillPostState s receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hFeeAdd
  have hPendingFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        (1000000000000000000 + (pendingFulfillPostState s receiver shares grossAssets).storage 1) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hFeeSub
  simpa using withdraw_apply_paused (pendingFulfillPostState s receiver shares grossAssets)
    receiver shares grossAssets hPendingVault hPendingPaused hPendingFeeAdd hPendingFeeSub

private theorem fulfillRedeem_run_paused
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run (pausedStateOf s) =
      ContractResult.revert "EnforcedPause" (pausedStateOf s) := by
  have hPausedAuthority : (pausedStateOf s).storageAddr 9 ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hAuthority
  have hPausedVault : (pausedStateOf s).thisAddress ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hVault
  have hPausedShares : (pausedStateOf s).storageMap 6 receiver ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hPendingShares
  have hPausedAssets : (pausedStateOf s).storageMap 7 receiver ≠ 0 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hPendingAssets
  have hPausedShareBound : shares.val ≤ ((pausedStateOf s).storageMap 6 receiver).val := by
    simpa [pausedStateOf, ContractState.writeSlot] using hShareBound
  have hPausedAssetBound : grossAssets.val ≤ ((pausedStateOf s).storageMap 7 receiver).val := by
    simpa [pausedStateOf, ContractState.writeSlot] using hAssetBound
  have hPausedGlobalBound : grossAssets.val ≤ ((pausedStateOf s).storage 0).val := by
    simpa [pausedStateOf, ContractState.writeSlot] using hGlobalBound
  have hPausedFeeAdd : ((pausedStateOf s).storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pausedStateOf, ContractState.writeSlot] using hFeeAdd
  have hPausedFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pausedStateOf s).storage 1)
        (1000000000000000000 + (pausedStateOf s).storage 1) : Nat) := by
    simpa [pausedStateOf, ContractState.writeSlot] using hFeeSub
  have hPaused : (pausedStateOf s).storage 3 = 1 := by
    simp [pausedStateOf, ContractState.writeSlot]
  unfold Contract.run
  rw [fulfillRedeem_apply_paused receiver shares grossAssets (pausedStateOf s)
    hPausedAuthority hPausedVault hPausedShares hPausedAssets hPausedShareBound hPausedAssetBound
    hPausedGlobalBound hPaused hPausedFeeAdd hPausedFeeSub]

/-- Cancellation follows the source guards, then transfers the selected pooled
shares while decrementing the receiver's independent pending components. -/
theorem cancel_redeem_accounting
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hShareBound : shares <= pendingSharesOf s receiver)
    (hAssetBound : grossAssets <= pendingAssetsOf s receiver)
    (hGlobalBound : grossAssets <= totalPendingAssetsOf s)
    (hVaultShares : shares <= shareBalanceOf s (vaultAddress s))
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0) :
    let result :=
      (YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets true true).run s
    cancel_redeem_accounting_spec shares grossAssets receiver s result := by
  have hAuthority' : authorityOf s ≠ zeroAddress := by simpa using hAuthority
  have hVault' : vaultAddress s ≠ zeroAddress := by simpa using hVault
  have hReceiver' : receiver ≠ zeroAddress := by simpa using hReceiver
  have hPendingShares' : pendingSharesOf s receiver ≠ 0 := by simpa using hPendingShares
  have hPendingAssets' : pendingAssetsOf s receiver ≠ 0 := by simpa using hPendingAssets
  have hShareBound' : shares.val ≤ (pendingSharesOf s receiver).val := by simpa using hShareBound
  have hAssetBound' : grossAssets.val ≤ (pendingAssetsOf s receiver).val := by simpa using hAssetBound
  have hGlobalBound' : grossAssets.val ≤ (totalPendingAssetsOf s).val := by simpa using hGlobalBound
  have hVaultShares' : shares.val ≤ (shareBalanceOf s (vaultAddress s)).val := by simpa using hVaultShares
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by simpa [authorityOf, zeroAddress] using hAuthority'
  have hVaultSlot : s.thisAddress ≠ 0 := by simpa [vaultAddress, zeroAddress] using hVault'
  have hReceiverSlot : receiver ≠ 0 := by simpa [zeroAddress] using hReceiver'
  have hPendingSharesSlot : s.storageMap 6 receiver ≠ 0 := by
    simpa [pendingSharesOf] using hPendingShares'
  have hPendingAssetsSlot : s.storageMap 7 receiver ≠ 0 := by
    simpa [pendingAssetsOf] using hPendingAssets'
  have hShareBoundSlot : shares.val ≤ (s.storageMap 6 receiver).val := by
    simpa [pendingSharesOf] using hShareBound'
  have hAssetBoundSlot : grossAssets.val ≤ (s.storageMap 7 receiver).val := by
    simpa [pendingAssetsOf] using hAssetBound'
  have hGlobalBoundSlot : grossAssets.val ≤ (s.storage 0).val := by
    simpa [totalPendingAssetsOf] using hGlobalBound'
  have hVaultSharesSlot : shares.val ≤ (s.storageMap 5 s.thisAddress).val := by
    simpa [shareBalanceOf, vaultAddress] using hVaultShares'
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  by_cases hReceiverVault : receiver = vaultAddress s
  · subst receiver
    have hPendingSharesVault : s.storageMap 6 s.thisAddress ≠ 0 := by
      simpa [vaultAddress] using hPendingSharesSlot
    have hPendingAssetsVault : s.storageMap 7 s.thisAddress ≠ 0 := by
      simpa [vaultAddress] using hPendingAssetsSlot
    have hShareBoundVault : shares.val ≤ (s.storageMap 6 s.thisAddress).val := by
      simpa [vaultAddress] using hShareBoundSlot
    have hAssetBoundVault : grossAssets.val ≤ (s.storageMap 7 s.thisAddress).val := by
      simpa [vaultAddress] using hAssetBoundSlot
    unfold cancel_redeem_accounting_spec
    simp [YoAsyncRedemptionEscrow.cancelRedeem, YoAsyncRedemptionEscrow.isAuthorized,
      YoAsyncRedemptionEscrow._transfer, YoAsyncRedemptionEscrow._update,
      YoAsyncRedemptionEscrow._updateSelf, YoAsyncRedemptionEscrow.authority,
      YoAsyncRedemptionEscrow.owner, YoAsyncRedemptionEscrow.paused,
      YoAsyncRedemptionEscrow.totalSupply, YoAsyncRedemptionEscrow.shareBalances,
      YoAsyncRedemptionEscrow.pendingShares, YoAsyncRedemptionEscrow.pendingAssets,
      YoAsyncRedemptionEscrow.totalPendingAssets, authorityOf, vaultAddress, pausedOf,
      totalSupplyOf, pendingSharesOf, pendingAssetsOf, totalPendingAssetsOf, shareBalanceOf,
      getStorage, getStorageAddr, getMapping, setStorage, setMapping, msgSender,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
      Verity.contractAddress, zeroAddress, hAuthoritySlot, hVaultSlot, hReceiverSlot,
      hPendingSharesVault, hPendingAssetsVault, hShareBoundVault, hAssetBoundVault,
      hGlobalBoundSlot, hVaultSharesSlot, hUnpausedSlot]
  · unfold cancel_redeem_accounting_spec
    have hVaultReceiver : s.thisAddress ≠ receiver := by
      simpa [vaultAddress, eq_comm] using hReceiverVault
    simp [YoAsyncRedemptionEscrow.cancelRedeem, YoAsyncRedemptionEscrow.isAuthorized,
      YoAsyncRedemptionEscrow._transfer, YoAsyncRedemptionEscrow._update,
      YoAsyncRedemptionEscrow._updateSelf, YoAsyncRedemptionEscrow.authority,
      YoAsyncRedemptionEscrow.owner, YoAsyncRedemptionEscrow.paused,
      YoAsyncRedemptionEscrow.totalSupply, YoAsyncRedemptionEscrow.shareBalances,
      YoAsyncRedemptionEscrow.pendingShares, YoAsyncRedemptionEscrow.pendingAssets,
      YoAsyncRedemptionEscrow.totalPendingAssets, authorityOf, vaultAddress, pausedOf,
      totalSupplyOf, pendingSharesOf, pendingAssetsOf, totalPendingAssetsOf, shareBalanceOf,
      getStorage, getStorageAddr, getMapping, setStorage, setMapping, msgSender,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
      Verity.contractAddress, zeroAddress, hAuthoritySlot, hVaultSlot, hReceiverSlot,
      hPendingSharesSlot, hPendingAssetsSlot, hShareBoundSlot, hAssetBoundSlot,
      hGlobalBoundSlot, hVaultSharesSlot, hUnpausedSlot, hReceiverVault, hVaultReceiver]
    intro h
    exact (hVaultReceiver h.symm).elim

/-- A queued request takes the insufficient-liquidity branch, transfers shares
to the vault, and adds both receiver-keyed pending components. -/
theorem queued_request_aggregation
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (previewSucceeds balanceReadSucceeds : Bool) (s : ContractState)
    (hUnpaused : pausedOf s = 0)
    (hVault : vaultAddress s != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hShares : shares > 0)
    (hGross : grossAssets > 0)
    (hOwnerShares : shareBalanceOf s owner >= shares)
    (hQueued : availableUnderlyingOf s externalUnderlyingBalance < grossAssets)
    (hErc20 : erc20WellFormed s)
    (hTotalAdd : checkedAddFits (totalPendingAssetsOf s) grossAssets)
    (hSharesAdd : checkedAddFits (pendingSharesOf s receiver) shares)
    (hAssetsAdd : checkedAddFits (pendingAssetsOf s receiver) grossAssets)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s)
    (hPreviewSucceeds : previewSucceeds = true)
    (hBalanceReadSucceeds : balanceReadSucceeds = true) :
    let result :=
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
        externalUnderlyingBalance previewSucceeds balanceReadSucceeds true true).run s
    queued_request_aggregation_spec shares grossAssets receiver owner s result := by
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hOwnerSlot : owner ≠ 0 := by simpa [zeroAddress] using (show owner ≠ zeroAddress by simpa using hOwner)
  have hReceiverSlot : receiver ≠ 0 := by simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hOwnerVault : owner ≠ s.thisAddress := by simpa [vaultAddress] using hOwnerNotVault
  have hSender : s.sender = owner := hOwnerIsSender.symm
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hSharesPos : 0 < shares.val := by simpa using hShares
  have hOwnerBalance : shares.val ≤ (s.storageMap 5 owner).val := by
    simpa [shareBalanceOf] using hOwnerShares
  have hQueuedSlot :
      (if externalUnderlyingBalance > s.storage 0 then sub externalUnderlyingBalance (s.storage 0) else 0) <
        grossAssets := by
    simpa [availableUnderlyingOf, totalPendingAssetsOf] using hQueued
  have hTotalFits : (s.storage 0 : Nat) + (grossAssets : Nat) ≤ MAX_UINT256 := by
    simpa [checkedAddFits, totalPendingAssetsOf] using hTotalAdd
  have hSharesFits : (s.storageMap 6 receiver : Nat) + (shares : Nat) ≤ MAX_UINT256 := by
    simpa [checkedAddFits, pendingSharesOf] using hSharesAdd
  have hAssetsFits : (s.storageMap 7 receiver : Nat) + (grossAssets : Nat) ≤ MAX_UINT256 := by
    simpa [checkedAddFits, pendingAssetsOf] using hAssetsAdd
  have hDirect :
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
        externalUnderlyingBalance true true true true).run s =
        ContractResult.success 0 (queuedPostState s shares grossAssets receiver owner) :=
    requestRedeem_queued_run shares grossAssets externalUnderlyingBalance receiver owner s
      hVaultSlot hOwnerSlot hReceiverSlot hOwnerVault hOwnerIsSender hUnpausedSlot hSharesPos
      hOwnerBalance hQueuedSlot hTotalFits hSharesFits hAssetsFits
  subst previewSucceeds
  subst balanceReadSucceeds
  change queued_request_aggregation_spec shares grossAssets receiver owner s
    ((YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
      externalUnderlyingBalance true true true true).run s)
  unfold queued_request_aggregation_spec
  refine ⟨queuedPostState s shares grossAssets receiver owner, hDirect, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pendingSharesOf, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap]
  · simp [pendingAssetsOf, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap]
  · simp [totalPendingAssetsOf, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap]
  · simp [totalSupplyOf, queuedPostState, mapWriteState, ContractState.writeSlot]
  · intro hOwnerNotVault'
    have hOwnerVault' : owner ≠ s.thisAddress := by simpa [vaultAddress] using hOwnerNotVault'
    have hVaultOwner' : s.thisAddress ≠ owner := hOwnerVault'.symm
    constructor <;>
      simp [shareBalanceOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap, vaultAddress, hOwnerVault', hVaultOwner']

/-- The public wrapper contributes only its first pause guard and otherwise
delegates to the same queued request execution. -/
theorem redeem_wrapper
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (s : ContractState)
    (hVault : vaultAddress s != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hUnpaused : pausedOf s = 0)
    (hSharesPositive : shares > 0)
    (hGrossPositive : grossAssets > 0)
    (hOwnerShares : shareBalanceOf s owner >= shares)
    (hQueued : availableUnderlyingOf s externalUnderlyingBalance < grossAssets)
    (hErc20 : erc20WellFormed s)
    (hTotalAdd : checkedAddFits (totalPendingAssetsOf s) grossAssets)
    (hSharesAdd : checkedAddFits (pendingSharesOf s receiver) shares)
    (hAssetsAdd : checkedAddFits (pendingAssetsOf s receiver) grossAssets)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    redeem_wrapper_spec shares grossAssets externalUnderlyingBalance receiver owner s := by
  have hQueue := queued_request_aggregation shares grossAssets externalUnderlyingBalance receiver owner
    true true s hUnpaused hVault hOwner hReceiver hOwnerNotVault hOwnerIsSender hSharesPositive
    hGrossPositive hOwnerShares hQueued hErc20 hTotalAdd hSharesAdd hAssetsAdd hUnderlyingNotVault rfl rfl
  dsimp at hQueue
  unfold queued_request_aggregation_spec at hQueue
  rcases hQueue with ⟨queuedState, hDirect, hSharesPost, hAssetsPost, hTotalPost, hSupplyPost, hBalances⟩
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hDelegate :
      (YoAsyncRedemptionEscrow.redeem shares receiver owner grossAssets externalUnderlyingBalance
        true true true true).run s =
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets externalUnderlyingBalance
        true true true true).run s := by
    rw [YoAsyncRedemptionEscrow.redeem]
    cases hRequest :
        YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets externalUnderlyingBalance
          true true true true s <;>
      simp [Contract.run, Bind.bind, Verity.bind, getStorage, Verity.require,
        YoAsyncRedemptionEscrow.paused, Verity.pure, Pure.pure, hUnpausedSlot, hRequest]
  have hRedeem :
      (YoAsyncRedemptionEscrow.redeem shares receiver owner grossAssets externalUnderlyingBalance
        true true true true).run s = ContractResult.success 0 queuedState := by
    rw [hDelegate]
    exact hDirect
  unfold redeem_wrapper_spec
  have hPaused :
      (YoAsyncRedemptionEscrow.redeem shares receiver owner grossAssets externalUnderlyingBalance
        true true true true).run (pausedStateOf s) =
        ContractResult.revert "EnforcedPause" (pausedStateOf s) := by
    have hPausedGuard : ((1 : Uint256) == 0) = false := by native_decide
    unfold pausedStateOf
    rw [YoAsyncRedemptionEscrow.redeem]
    simp [Contract.run, Bind.bind, Verity.bind, getStorage, Verity.require,
      YoAsyncRedemptionEscrow.paused, Verity.pure, Pure.pure, Verity.ContractState.writeSlot,
      hPausedGuard]
  simp only [hRedeem, ContractResult.snd_success]
  exact ⟨True.intro, hDirect, hSharesPost, hAssetsPost, hTotalPost, hPaused⟩

/-- Successful fulfillment follows the independently bounded pending writes,
then burns pooled shares and applies the current fee configuration. -/
theorem fulfill_redeem_accounting
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hShareBound : shares <= pendingSharesOf s receiver)
    (hAssetBound : grossAssets <= pendingAssetsOf s receiver)
    (hGlobalBound : grossAssets <= totalPendingAssetsOf s)
    (hVaultShares : shares <= shareBalanceOf s (vaultAddress s))
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    let result :=
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s
    fulfill_redeem_accounting_spec shares grossAssets receiver s result := by
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hPendingSharesSlot : s.storageMap 6 receiver ≠ 0 := by
    simpa [pendingSharesOf] using (show pendingSharesOf s receiver ≠ 0 by simpa using hPendingShares)
  have hPendingAssetsSlot : s.storageMap 7 receiver ≠ 0 := by
    simpa [pendingAssetsOf] using (show pendingAssetsOf s receiver ≠ 0 by simpa using hPendingAssets)
  have hShareBoundSlot : shares.val ≤ (s.storageMap 6 receiver).val := by simpa [pendingSharesOf] using hShareBound
  have hAssetBoundSlot : grossAssets.val ≤ (s.storageMap 7 receiver).val := by simpa [pendingAssetsOf] using hAssetBound
  have hGlobalBoundSlot : grossAssets.val ≤ (s.storage 0).val := by simpa [totalPendingAssetsOf] using hGlobalBound
  have hVaultSharesSlot : shares.val ≤ (s.storageMap 5 s.thisAddress).val := by
    simpa [shareBalanceOf, vaultAddress] using hVaultShares
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeFitsSlot : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeDenominator] using hFeeFits
  have hFeeBound :
      (mulDiv512Up grossAssets (s.storage 1) (add (s.storage 1) feeDenominator) : Nat) ≤
        (grossAssets : Nat) := by
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using feeAmountOf_le_gross s grossAssets hFeeDivisor
  have hFeeUnderflowSlot :
      ¬(grossAssets : Nat) <
        (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 =
      add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm (s.storage 1) (1000000000000000000 : Uint256)).symm]
    omega
  have hRun := fulfillRedeem_run_true receiver shares grossAssets s hAuthoritySlot hVaultSlot
    hPendingSharesSlot hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot
    hVaultSharesSlot hUnpausedSlot hFeeFitsSlot hFeeUnderflowSlot
  unfold fulfill_redeem_accounting_spec
  refine ⟨fulfilledPostState s receiver shares grossAssets, hRun, hShareBound, hAssetBound,
    hPendingShares, hPendingAssets, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, shareBalanceOf, vaultAddress]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, totalSupplyOf]
  · exact (Verity.Core.Uint256.sub_add_cancel_left grossAssets
      (feeAmountOf s grossAssets)).symm

/-- A nonzero authority returning `false` reaches owner fallback, whereas a
reverting authority call is observed before that fallback. -/
theorem owner_fallback_authorization
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hOwner : ownerOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hSharesPositive : shares > 0)
    (hGrossPositive : grossAssets > 0)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hShareBound : shares <= pendingSharesOf s receiver)
    (hAssetBound : grossAssets <= pendingAssetsOf s receiver)
    (hGlobalBound : grossAssets <= totalPendingAssetsOf s)
    (hVaultShares : shares <= shareBalanceOf s (vaultAddress s))
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    owner_fallback_authorization_spec receiver shares grossAssets s := by
  let ownerState := { s with sender := ownerOf s }
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hOwnerSender : ownerState.sender = ownerState.storageAddr 8 := by
    simp [ownerState, ownerOf]
  have hOwnerAuthorized :
      YoAsyncRedemptionEscrow.isAuthorized true false ownerState =
        ContractResult.success true ownerState :=
    isAuthorized_true_false_owner_apply ownerState (by simpa [ownerState] using hAuthoritySlot)
      hOwnerSender
  have hVaultSlot : ownerState.thisAddress ≠ 0 := by simpa [ownerState, vaultAddress, zeroAddress] using hVault
  have hPendingSharesSlot : ownerState.storageMap 6 receiver ≠ 0 := by
    simpa [ownerState, pendingSharesOf] using hPendingShares
  have hPendingAssetsSlot : ownerState.storageMap 7 receiver ≠ 0 := by
    simpa [ownerState, pendingAssetsOf] using hPendingAssets
  have hShareBoundSlot : shares.val ≤ (ownerState.storageMap 6 receiver).val := by
    simpa [ownerState, pendingSharesOf] using hShareBound
  have hAssetBoundSlot : grossAssets.val ≤ (ownerState.storageMap 7 receiver).val := by
    simpa [ownerState, pendingAssetsOf] using hAssetBound
  have hGlobalBoundSlot : grossAssets.val ≤ (ownerState.storage 0).val := by
    simpa [ownerState, totalPendingAssetsOf] using hGlobalBound
  have hVaultSharesSlot : shares.val ≤ (ownerState.storageMap 5 ownerState.thisAddress).val := by
    simpa [ownerState, shareBalanceOf, vaultAddress] using hVaultShares
  have hUnpausedSlot : ownerState.storage 3 = 0 := by simpa [ownerState, pausedOf] using hUnpaused
  have hFeeFitsSlot : (ownerState.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [ownerState, feeDivisorFits, feeOnWithdrawOf, checkedAddFits, feeDenominator] using hFeeDivisor
  have hFeeBound :
      (mulDiv512Up grossAssets (ownerState.storage 1)
        (add (ownerState.storage 1) feeDenominator) : Nat) ≤ grossAssets.val := by
    simpa [ownerState, feeAmountOf, feeAmountWith, feeOnWithdrawOf] using
      feeAmountOf_le_gross s grossAssets hFeeDivisor
  have hFeeUnderflowSlot : ¬grossAssets.val <
      (mulDiv512Up grossAssets (ownerState.storage 1)
        (1000000000000000000 + ownerState.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + ownerState.storage 1 =
      add (ownerState.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge hFeeBound
  have hFallbackRun := fulfillRedeem_run_authorized receiver shares grossAssets ownerState false
    hOwnerAuthorized (by simpa [ownerState] using hAuthoritySlot) hVaultSlot hPendingSharesSlot
    hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot hVaultSharesSlot
    hUnpausedSlot hFeeFitsSlot hFeeUnderflowSlot
  unfold owner_fallback_authorization_spec
  simp only [ownerState, hFallbackRun, ContractResult.snd_success]
  refine ⟨True.intro, ?_, ?_, ?_⟩
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf]
  · simp [YoAsyncRedemptionEscrow.fulfillRedeem, YoAsyncRedemptionEscrow.isAuthorized,
      YoAsyncRedemptionEscrow.authority, getStorageAddr, msgSender, zeroAddress,
      Verity.require, Verity.bind, Bind.bind, Contract.run, hAuthoritySlot]

/-- From a two-sided record, each source-permitted `(0,0)` settlement succeeds
without changing observable storage; mapping-key bookkeeping is excluded. -/
theorem zero_component_lifecycle
    (receiver : Address) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    zero_component_lifecycle_spec receiver s := by
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hPendingSharesSlot : s.storageMap 6 receiver ≠ 0 := by
    simpa [pendingSharesOf] using (show pendingSharesOf s receiver ≠ 0 by simpa using hPendingShares)
  have hPendingAssetsSlot : s.storageMap 7 receiver ≠ 0 := by
    simpa [pendingAssetsOf] using (show pendingAssetsOf s receiver ≠ 0 by simpa using hPendingAssets)
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeNoOverflowSlot : ¬MAX_UINT256 < (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) := by
    have : ¬MAX_UINT256 < (s.storage 1 : Nat) + (feeDenominator : Nat) := by omega
    simpa [feeDenominator] using this
  have hFeeZero : mulDiv512Up 0 (s.storage 1) (1000000000000000000 + s.storage 1) = 0 := by
    apply Verity.Core.Uint256.ext
    have hLe := feeAmountOf_le_gross s 0 hFeeDivisor
    have hEq : (mulDiv512Up 0 (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) = 0 := by
      rw [show (1000000000000000000 : Uint256) + s.storage 1 =
        add (s.storage 1) feeDenominator by
        change (1000000000000000000 : Uint256) + s.storage 1 = s.storage 1 + (1000000000000000000 : Uint256)
        exact (Verity.Core.Uint256.add_comm _ _).symm]
      simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using Nat.eq_zero_of_le_zero hLe
    simpa using hEq
  have hFeeFitsSlot : (s.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeDenominator] using hFeeFits
  have hFeeSub : ¬(0 : Uint256).val <
      (mulDiv512Up 0 (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    simp [hFeeZero]
  have hFulfilled := fulfillRedeem_run_true receiver 0 0 s hAuthoritySlot hVaultSlot
    hPendingSharesSlot hPendingAssetsSlot (by simp) (by simp) (by simp) (by simp)
    hUnpausedSlot hFeeFitsSlot hFeeSub
  have hCancelled := cancelRedeem_run_zero receiver s hAuthoritySlot hVaultSlot
    (by simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver))
    hPendingSharesSlot hPendingAssetsSlot hUnpausedSlot
  unfold zero_component_lifecycle_spec
  refine ⟨fulfilledPostState s receiver 0 0, cancelZeroPostState s receiver, hFulfilled,
    hCancelled, ?_, ?_⟩
  · simp [evmObservableStorageEq, fulfilledPostState, burnPostState, pendingFulfillPostState,
      mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      uint_sub_zero, uint_add_zero]
    constructor
    · funext sl
      by_cases h4 : sl = 4 <;> by_cases h0 : sl = 0 <;>
        simp [h4, h0, uint_sub_zero]
    · funext sl key
      by_cases h5 : sl = 5 ∧ key = s.thisAddress <;>
        by_cases h7 : sl = 7 ∧ key = receiver <;>
        by_cases h6 : sl = 6 ∧ key = receiver <;>
          simp [h5, h7, h6, uint_sub_zero]
  · by_cases hSelf : s.thisAddress = receiver
    · simp [evmObservableStorageEq, cancelZeroPostState, transferZeroPostState,
        pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hSelf, uint_sub_zero]
      constructor
      · funext sl
        by_cases h0 : sl = 0 <;> simp [h0, uint_sub_zero]
      · funext sl key
        by_cases h7 : sl = 7 ∧ key = receiver <;>
          by_cases h6 : sl = 6 ∧ key = receiver <;>
            simp [h7, h6, uint_sub_zero]
    · simp [evmObservableStorageEq, cancelZeroPostState, transferZeroPostState,
        pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hSelf, uint_sub_zero, uint_add_zero]
      have hSelfBool : (s.thisAddress == receiver) = false := by simp [hSelf]
      constructor
      · funext sl
        by_cases h0 : sl = 0 <;> simp [h0, uint_sub_zero]
      · funext sl key
        by_cases h5r : sl = 5 ∧ key = receiver <;>
          by_cases h5v : sl = 5 ∧ key = s.thisAddress <;>
          by_cases h7 : sl = 7 ∧ key = receiver <;>
          by_cases h6 : sl = 6 ∧ key = receiver <;>
            simp [h5r, h5v, h7, h6, hSelf, hSelfBool, uint_sub_zero, uint_add_zero]

/-- Each selected failure reaches its source boundary and `Contract.run`
normalizes the observable state back to the caller's snapshot. -/
theorem lifecycle_rollback
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hOwnerContext : s.sender = ownerOf s)
    (hOwner : ownerOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hShareBound : shares <= pendingSharesOf s receiver)
    (hAssetBound : grossAssets <= pendingAssetsOf s receiver)
    (hGlobalBound : grossAssets <= totalPendingAssetsOf s)
    (hVaultShares : shares <= shareBalanceOf s (vaultAddress s))
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hPositiveFee : feeAmountOf s grossAssets > 0)
    (hFeeRecipient : feeRecipientOf s != zeroAddress)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    lifecycle_rollback_spec receiver shares grossAssets s := by
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hReceiverSlot : receiver ≠ 0 := by simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hPendingSharesSlot : s.storageMap 6 receiver ≠ 0 := by
    simpa [pendingSharesOf] using (show pendingSharesOf s receiver ≠ 0 by simpa using hPendingShares)
  have hPendingAssetsSlot : s.storageMap 7 receiver ≠ 0 := by
    simpa [pendingAssetsOf] using (show pendingAssetsOf s receiver ≠ 0 by simpa using hPendingAssets)
  have hShareBoundSlot : shares.val ≤ (s.storageMap 6 receiver).val := by simpa [pendingSharesOf] using hShareBound
  have hAssetBoundSlot : grossAssets.val ≤ (s.storageMap 7 receiver).val := by simpa [pendingAssetsOf] using hAssetBound
  have hGlobalBoundSlot : grossAssets.val ≤ (s.storage 0).val := by simpa [totalPendingAssetsOf] using hGlobalBound
  have hVaultSharesSlot : shares.val ≤ (s.storageMap 5 s.thisAddress).val := by
    simpa [shareBalanceOf, vaultAddress] using hVaultShares
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeNoOverflowSlot : ¬MAX_UINT256 < (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) := by
    have : ¬MAX_UINT256 < (s.storage 1 : Nat) + (feeDenominator : Nat) := by omega
    simpa [feeDenominator] using this
  have hFeeBound :
      (mulDiv512Up grossAssets (s.storage 1) (add (s.storage 1) feeDenominator) : Nat) ≤ grossAssets.val := by
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using feeAmountOf_le_gross s grossAssets hFeeDivisor
  have hFeeUnderflowSlot : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 = add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 = s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    omega
  have hFeePositiveSlot : 0 <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 = add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 = s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using hPositiveFee
  have hFeeRecipientSlot : s.storageAddr 2 ≠ 0 := by
    simpa [feeRecipientOf, zeroAddress] using (show feeRecipientOf s ≠ zeroAddress by simpa using hFeeRecipient)
  have hPausedFulfill := fulfillRedeem_run_paused receiver shares grossAssets s hAuthoritySlot hVaultSlot
    hPendingSharesSlot hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot
    (by simpa [feeDenominator] using hFeeFits) hFeeUnderflowSlot
  have hPausedCancel := cancelRedeem_run_paused receiver shares grossAssets s hAuthoritySlot hVaultSlot
    hReceiverSlot hPendingSharesSlot hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot
  have hFeePositiveForward : 0 <
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000) : Nat) := by
    rw [Verity.Core.Uint256.add_comm]
    exact hFeePositiveSlot
  unfold lifecycle_rollback_spec
  dsimp
  refine ⟨fulfillRedeem_run_authority_revert receiver shares grossAssets s hAuthoritySlot,
    cancelRedeem_run_authority_revert receiver shares grossAssets s hAuthoritySlot,
    hPausedFulfill, hPausedCancel, ?_, ?_⟩
  · exact fulfillRedeem_run_receiver_revert receiver shares grossAssets s hAuthoritySlot hVaultSlot
      hPendingSharesSlot hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot
      hVaultSharesSlot hUnpausedSlot (by simpa [feeDenominator] using hFeeFits) hFeeUnderflowSlot
  · exact fulfillRedeem_run_fee_revert receiver shares grossAssets s hAuthoritySlot hVaultSlot
      hPendingSharesSlot hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot
      hVaultSharesSlot hUnpausedSlot (by simpa [feeDenominator] using hFeeFits) hFeeUnderflowSlot
      hFeePositiveForward hFeeRecipientSlot

/-- Successful preview and balance-read outcomes are explicit assumptions. The
    theorem distinguishes the source instant and queued request transitions. -/
theorem request_redeem_branching
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (previewSucceeds balanceReadSucceeds : Bool) (s : ContractState)
    (hUnpaused : pausedOf s = 0)
    (hVault : vaultAddress s != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwnerIsSender : owner = s.sender)
    (hShares : shares > 0)
    (hOwnerShares : shareBalanceOf s owner >= shares)
    (hErc20 : erc20WellFormed s)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s)
    (hPreviewSucceeds : previewSucceeds = true)
    (hBalanceReadSucceeds : balanceReadSucceeds = true)
    (hQueuedAdds : availableUnderlyingOf s externalUnderlyingBalance < grossAssets →
      checkedAddFits (totalPendingAssetsOf s) grossAssets ∧
      checkedAddFits (pendingSharesOf s receiver) shares ∧
      checkedAddFits (pendingAssetsOf s receiver) grossAssets) :
    let result :=
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
        externalUnderlyingBalance previewSucceeds balanceReadSucceeds true true).run s
    request_redeem_branching_spec shares grossAssets externalUnderlyingBalance receiver owner s result := by
  subst previewSucceeds
  subst balanceReadSucceeds
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hOwnerSlot : owner ≠ 0 := by simpa [zeroAddress] using (show owner ≠ zeroAddress by simpa using hOwner)
  have hReceiverSlot : receiver ≠ 0 := by
    simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hSharesPositive : shares > 0 := hShares
  have hOwnerSharesSlot : shares.val ≤ (s.storageMap 5 owner).val := by
    simpa [shareBalanceOf] using hOwnerShares
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeFitsSlot : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeDenominator] using hFeeFits
  have hFeeBound :
      (mulDiv512Up grossAssets (s.storage 1) (add (s.storage 1) feeDenominator) : Nat) ≤
        (grossAssets : Nat) := by
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using
      feeAmountOf_le_gross s grossAssets hFeeDivisor
  have hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 =
      add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge hFeeBound
  by_cases hInstant : availableUnderlyingOf s externalUnderlyingBalance >= grossAssets
  · have hInstantSlot :
        (if externalUnderlyingBalance > s.storage 0 then
          sub externalUnderlyingBalance (s.storage 0)
        else 0) >= grossAssets := by
      simpa [availableUnderlyingOf, totalPendingAssetsOf] using hInstant
    have hRun := requestRedeem_instant_run shares grossAssets externalUnderlyingBalance receiver owner s
      hOwnerSlot hReceiverSlot hOwnerIsSender hUnpausedSlot hSharesPositive hOwnerSharesSlot
      hInstantSlot hFeeFitsSlot hFeeSub
    unfold request_redeem_branching_spec
    refine ⟨burnFromPostState s owner shares, ?_, ?_⟩
    · simpa [hInstant] using hRun
    · simp [hInstant, pendingSharesOf, pendingAssetsOf, totalPendingAssetsOf, shareBalanceOf,
        totalSupplyOf, burnFromPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]
  · have hQueued : availableUnderlyingOf s externalUnderlyingBalance < grossAssets :=
      Nat.lt_of_not_ge hInstant
    rcases hQueuedAdds hQueued with ⟨hTotalAdd, hSharesAdd, hAssetsAdd⟩
    have hQueuedSlot :
        (if externalUnderlyingBalance > s.storage 0 then
          sub externalUnderlyingBalance (s.storage 0)
        else 0) < grossAssets := by
      simpa [availableUnderlyingOf, totalPendingAssetsOf] using hQueued
    have hTotalFits : (s.storage 0 : Nat) + (grossAssets : Nat) ≤ MAX_UINT256 := by
      simpa [checkedAddFits, totalPendingAssetsOf] using hTotalAdd
    have hSharesFits : (s.storageMap 6 receiver : Nat) + (shares : Nat) ≤ MAX_UINT256 := by
      simpa [checkedAddFits, pendingSharesOf] using hSharesAdd
    have hAssetsFits : (s.storageMap 7 receiver : Nat) + (grossAssets : Nat) ≤ MAX_UINT256 := by
      simpa [checkedAddFits, pendingAssetsOf] using hAssetsAdd
    by_cases hOwnerVault : owner = vaultAddress s
    · have hSender : s.sender = s.thisAddress := by
        simpa [vaultAddress, hOwnerVault] using hOwnerIsSender.symm
      have hOwnerVaultShares : s.storageMap 5 s.thisAddress >= shares := by
        simpa [shareBalanceOf, vaultAddress, hOwnerVault] using hOwnerShares
      have hRun := requestRedeem_queued_run_self shares grossAssets externalUnderlyingBalance receiver s
        hVaultSlot hReceiverSlot hSender hUnpausedSlot hSharesPositive hOwnerVaultShares hQueuedSlot
        hTotalFits hSharesFits hAssetsFits
      unfold request_redeem_branching_spec
      refine ⟨(let afterTotal := s.writeSlot 0 (add (s.storage 0) grossAssets)
        let afterShares := mapWriteState afterTotal 6 receiver
          (add (s.storageMap 6 receiver) shares)
        mapWriteState afterShares 7 receiver (add (s.storageMap 7 receiver) grossAssets)), ?_, ?_⟩
      · simpa [hInstant, hOwnerVault, vaultAddress] using hRun
      · simp [hInstant, pendingSharesOf, pendingAssetsOf, totalPendingAssetsOf, totalSupplyOf,
          mapWriteState, ContractState.writeSlot, ContractState.writeMap]
    · have hOwnerNotVault : owner ≠ s.thisAddress := by
        simpa [vaultAddress] using hOwnerVault
      have hRun := requestRedeem_queued_run shares grossAssets externalUnderlyingBalance receiver owner s
        hVaultSlot hOwnerSlot hReceiverSlot hOwnerNotVault hOwnerIsSender hUnpausedSlot
        hSharesPositive (by simpa [shareBalanceOf] using hOwnerShares) hQueuedSlot hTotalFits
        hSharesFits hAssetsFits
      unfold request_redeem_branching_spec
      refine ⟨queuedPostState s shares grossAssets receiver owner, ?_, ?_⟩
      · simpa [hInstant] using hRun
      · simp [hInstant, pendingSharesOf, pendingAssetsOf, totalPendingAssetsOf, totalSupplyOf,
          queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]

/-- Distinct non-vault owners make two positive-gross queued requests under
    separate sender contexts and aggregate into one receiver record. -/
theorem two_owner_queue_aggregation
    (firstShares firstGross secondShares secondGross : Uint256)
    (firstOwner secondOwner receiver : Address) (s : ContractState)
    (hDistinctOwners : firstOwner != secondOwner)
    (hVault : vaultAddress s != zeroAddress)
    (hFirstOwner : firstOwner != zeroAddress)
    (hSecondOwner : secondOwner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hFirstNotVault : firstOwner != vaultAddress s)
    (hSecondNotVault : secondOwner != vaultAddress s)
    (hFirstPositive : firstShares > 0)
    (hSecondPositive : secondShares > 0)
    (hFirstGrossPositive : firstGross > 0)
    (hSecondGrossPositive : secondGross > 0)
    (hUnpaused : pausedOf s = 0)
    (hFirstShares : shareBalanceOf s firstOwner >= firstShares)
    (hSecondShares : shareBalanceOf s secondOwner >= secondShares)
    (hErc20 : erc20WellFormed s)
    (hVaultSequentialCapacity :
      (shareBalanceOf s (vaultAddress s) : Nat) + (firstShares : Nat) + (secondShares : Nat) <=
        (totalSupplyOf s : Nat))
    (hTotalCapacity : (totalPendingAssetsOf s : Nat) + (firstGross : Nat) + (secondGross : Nat) <= MAX_UINT256)
    (hSharesCapacity : (pendingSharesOf s receiver : Nat) + (firstShares : Nat) + (secondShares : Nat) <= MAX_UINT256)
    (hAssetsCapacity : (pendingAssetsOf s receiver : Nat) + (firstGross : Nat) + (secondGross : Nat) <= MAX_UINT256)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    two_owner_queue_aggregation_spec firstShares firstGross secondShares secondGross
      firstOwner secondOwner receiver s := by
  let firstState := { s with sender := firstOwner }
  let firstPost := queuedPostState firstState firstShares firstGross receiver firstOwner
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hReceiverSlot : receiver ≠ 0 := by
    simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hFirstOwnerSlot : firstOwner ≠ 0 := by
    simpa [zeroAddress] using (show firstOwner ≠ zeroAddress by simpa using hFirstOwner)
  have hSecondOwnerSlot : secondOwner ≠ 0 := by
    simpa [zeroAddress] using (show secondOwner ≠ zeroAddress by simpa using hSecondOwner)
  have hFirstNotVaultSlot : firstOwner ≠ s.thisAddress := by
    simpa [vaultAddress] using hFirstNotVault
  have hSecondNotVaultSlot : secondOwner ≠ s.thisAddress := by
    simpa [vaultAddress] using hSecondNotVault
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hTotalCapacitySlot : (s.storage 0 : Nat) + (firstGross : Nat) + (secondGross : Nat) ≤
      MAX_UINT256 := by
    simpa [totalPendingAssetsOf] using hTotalCapacity
  have hSharesCapacitySlot : (s.storageMap 6 receiver : Nat) + (firstShares : Nat) +
      (secondShares : Nat) ≤ MAX_UINT256 := by
    simpa [pendingSharesOf] using hSharesCapacity
  have hAssetsCapacitySlot : (s.storageMap 7 receiver : Nat) + (firstGross : Nat) +
      (secondGross : Nat) ≤ MAX_UINT256 := by
    simpa [pendingAssetsOf] using hAssetsCapacity
  have hFirstTotalFit : (s.storage 0 : Nat) + (firstGross : Nat) ≤ MAX_UINT256 := by omega
  have hFirstSharesFit : (s.storageMap 6 receiver : Nat) + (firstShares : Nat) ≤ MAX_UINT256 := by omega
  have hFirstAssetsFit : (s.storageMap 7 receiver : Nat) + (firstGross : Nat) ≤ MAX_UINT256 := by omega
  have hFirstQueued :
      (if (0 : Uint256) > s.storage 0 then sub 0 (s.storage 0) else 0) < firstGross := by
    simpa using hFirstGrossPositive
  have hFirstRun :
      (YoAsyncRedemptionEscrow.requestRedeem firstShares receiver firstOwner firstGross 0
        true true true true).run firstState = ContractResult.success 0 firstPost := by
    apply requestRedeem_queued_run firstShares firstGross 0 receiver firstOwner firstState
    · simpa [firstState] using hVaultSlot
    · simpa [firstState] using hFirstOwnerSlot
    · simpa [firstState] using hReceiverSlot
    · simpa [firstState] using hFirstNotVaultSlot
    · rfl
    · simpa [firstState] using hUnpausedSlot
    · exact hFirstPositive
    · simpa [firstState, shareBalanceOf] using hFirstShares
    · simpa [firstState] using hFirstQueued
    · simpa [firstState] using hFirstTotalFit
    · simpa [firstState] using hFirstSharesFit
    · simpa [firstState] using hFirstAssetsFit
  let secondState := { firstPost with sender := secondOwner }
  have hFirstTotalVal : (add (s.storage 0) firstGross : Nat) =
      (s.storage 0 : Nat) + (firstGross : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hFirstTotalFit)
  have hFirstSharesVal : (add (s.storageMap 6 receiver) firstShares : Nat) =
      (s.storageMap 6 receiver : Nat) + (firstShares : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hFirstSharesFit)
  have hFirstAssetsVal : (add (s.storageMap 7 receiver) firstGross : Nat) =
      (s.storageMap 7 receiver : Nat) + (firstGross : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hFirstAssetsFit)
  have hSecondTotalBase : secondState.storage 0 = add (s.storage 0) firstGross := by
    simp [secondState, firstPost, firstState, queuedPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap]
  have hSecondSharesBase : secondState.storageMap 6 receiver =
      add (s.storageMap 6 receiver) firstShares := by
    simp [secondState, firstPost, firstState, queuedPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap]
  have hSecondAssetsBase : secondState.storageMap 7 receiver =
      add (s.storageMap 7 receiver) firstGross := by
    simp [secondState, firstPost, firstState, queuedPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap]
  have hSecondTotalFit : (secondState.storage 0 : Nat) + (secondGross : Nat) ≤ MAX_UINT256 := by
    rw [hSecondTotalBase, hFirstTotalVal]
    omega
  have hSecondSharesFit : (secondState.storageMap 6 receiver : Nat) + (secondShares : Nat) ≤ MAX_UINT256 := by
    rw [hSecondSharesBase, hFirstSharesVal]
    omega
  have hSecondAssetsFit : (secondState.storageMap 7 receiver : Nat) + (secondGross : Nat) ≤ MAX_UINT256 := by
    rw [hSecondAssetsBase, hFirstAssetsVal]
    omega
  have hSecondNotFirst : secondOwner ≠ firstOwner := by
    simpa using (show firstOwner ≠ secondOwner by simpa using hDistinctOwners).symm
  have hSecondOwnerBalance : secondState.storageMap 5 secondOwner >= secondShares := by
    simpa [secondState, firstPost, firstState, queuedPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, hSecondNotFirst, hSecondNotVaultSlot]
      using hSecondShares
  have hSecondQueued :
      (if (0 : Uint256) > secondState.storage 0 then sub 0 (secondState.storage 0) else 0) <
        secondGross := by
    simpa using hSecondGrossPositive
  have hSecondRun :
      (YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
        true true true true).run secondState =
      ContractResult.success 0 (queuedPostState secondState secondShares secondGross receiver secondOwner) := by
    apply requestRedeem_queued_run secondShares secondGross 0 receiver secondOwner secondState
    · simpa [secondState, firstPost, firstState, queuedPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap] using hVaultSlot
    · exact hSecondOwnerSlot
    · exact hReceiverSlot
    · simpa [secondState, firstPost, firstState, queuedPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap] using hSecondNotVaultSlot
    · rfl
    · simpa [secondState, firstPost, firstState, queuedPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap] using hUnpausedSlot
    · exact hSecondPositive
    · exact hSecondOwnerBalance
    · exact hSecondQueued
    · exact hSecondTotalFit
    · exact hSecondSharesFit
    · exact hSecondAssetsFit
  have hSecondPendingShares : pendingSharesOf secondState receiver =
      add (pendingSharesOf s receiver) firstShares := by
    simpa [pendingSharesOf] using hSecondSharesBase
  have hSecondPendingAssets : pendingAssetsOf secondState receiver =
      add (pendingAssetsOf s receiver) firstGross := by
    simpa [pendingAssetsOf] using hSecondAssetsBase
  have hSecondPendingTotal : totalPendingAssetsOf secondState =
      add (totalPendingAssetsOf s) firstGross := by
    simpa [totalPendingAssetsOf] using hSecondTotalBase
  have hFinalShares :
      pendingSharesOf (queuedPostState secondState secondShares secondGross receiver secondOwner) receiver =
        add (add (pendingSharesOf s receiver) firstShares) secondShares := by
    rw [show pendingSharesOf
      (queuedPostState secondState secondShares secondGross receiver secondOwner) receiver =
        add (pendingSharesOf secondState receiver) secondShares by
      simp [pendingSharesOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [hSecondPendingShares]
  have hFinalAssets :
      pendingAssetsOf (queuedPostState secondState secondShares secondGross receiver secondOwner) receiver =
        add (add (pendingAssetsOf s receiver) firstGross) secondGross := by
    rw [show pendingAssetsOf
      (queuedPostState secondState secondShares secondGross receiver secondOwner) receiver =
        add (pendingAssetsOf secondState receiver) secondGross by
      simp [pendingAssetsOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [hSecondPendingAssets]
  have hFinalTotal :
      totalPendingAssetsOf (queuedPostState secondState secondShares secondGross receiver secondOwner) =
        add (add (totalPendingAssetsOf s) firstGross) secondGross := by
    rw [show totalPendingAssetsOf
      (queuedPostState secondState secondShares secondGross receiver secondOwner) =
        add (totalPendingAssetsOf secondState) secondGross by
      simp [totalPendingAssetsOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [hSecondPendingTotal]
  unfold two_owner_queue_aggregation_spec
  dsimp
  rw [show { s with sender := firstOwner } = firstState by rfl, hFirstRun]
  simp only [ContractResult.snd_success]
  change True ∧
    ((YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
      true true true true).run secondState = ContractResult.success 0
        ((YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
          true true true true).run secondState).snd) ∧
    pendingSharesOf
      ((YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
        true true true true).run secondState).snd receiver =
      add (add (pendingSharesOf s receiver) firstShares) secondShares ∧
    pendingAssetsOf
      ((YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
        true true true true).run secondState).snd receiver =
      add (add (pendingAssetsOf s receiver) firstGross) secondGross ∧
    totalPendingAssetsOf
      ((YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
        true true true true).run secondState).snd =
      add (add (totalPendingAssetsOf s) firstGross) secondGross
  rw [hSecondRun]
  simp only [ContractResult.snd_success]
  exact ⟨True.intro, True.intro, hFinalShares, hFinalAssets, hFinalTotal⟩

/-- Once the share component is present but the asset component is zero, the
second independent pending guard rejects both settlement entrypoints. -/
private theorem fulfillRedeem_run_invalid_assets
    (receiver : Address) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver = 0) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 0 true true true true).run s =
      ContractResult.revert "InvalidAssetsAmount" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && 0 <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by simp [Verity.require, hPendingShares])]
  rw [bind_apply_of_revert
    (Verity.require (s.storageMap 7 receiver != 0 && 0 <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s "InvalidAssetsAmount" (by
        simp [Verity.require, hPendingAssets])]

private theorem cancelRedeem_run_invalid_assets
    (receiver : Address) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver = 0) :
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run s =
      ContractResult.revert "InvalidAssetsAmount" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.cancelRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_success
    (Verity.require (s.storageMap 6 receiver != 0 && 0 <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s () (by simp [Verity.require, hPendingShares])]
  rw [bind_apply_of_revert
    (Verity.require (s.storageMap 7 receiver != 0 && 0 <= s.storageMap 7 receiver)
      "InvalidAssetsAmount") _ s s "InvalidAssetsAmount" (by
        simp [Verity.require, hPendingAssets])]

/-- A zero share component reaches the first pending guard before any asset
state is inspected. -/
private theorem fulfillRedeem_run_invalid_shares
    (receiver : Address) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hPendingShares : s.storageMap 6 receiver = 0) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 0 true true true true).run s =
      ContractResult.revert "InvalidSharesAmount" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_revert
    (Verity.require (s.storageMap 6 receiver != 0 && 0 <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s "InvalidSharesAmount" (by
        simp [Verity.require, hPendingShares])]

private theorem cancelRedeem_run_invalid_shares
    (receiver : Address) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hPendingShares : s.storageMap 6 receiver = 0) :
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run s =
      ContractResult.revert "InvalidSharesAmount" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.cancelRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_revert
    (Verity.require (s.storageMap 6 receiver != 0 && 0 <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s "InvalidSharesAmount" (by
        simp [Verity.require, hPendingShares])]

/-- One-sided records are produced by real zero-component settlements from a
    queued pair; both dormant directions are then repaired by a positive queue. -/
theorem malformed_pair_lifecycle
    (receiver owner repairOwner : Address)
    (queuedShares queuedGross repairShares repairGross : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hRepairOwner : repairOwner != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hRepairOwnerNotVault : repairOwner != vaultAddress s)
    (hDistinctOwners : owner != repairOwner)
    (hUnpaused : pausedOf s = 0)
    (hQueuedSharesPositive : queuedShares > 0)
    (hQueuedGrossPositive : queuedGross > 0)
    (hRepairSharesPositive : repairShares > 0)
    (hRepairGrossPositive : repairGross > 0)
    (hInitialPendingShares : pendingSharesOf s receiver = 0)
    (hInitialPendingAssets : pendingAssetsOf s receiver = 0)
    (hInitialPendingTotal : totalPendingAssetsOf s = 0)
    (hOwnerShares : shareBalanceOf s owner >= queuedShares)
    (hRepairOwnerShares : shareBalanceOf s repairOwner >= repairShares)
    (hErc20 : erc20WellFormed s)
    (hVaultSequentialCapacity :
      (shareBalanceOf s (vaultAddress s) : Nat) + (queuedShares : Nat) + (repairShares : Nat) <=
        (totalSupplyOf s : Nat))
    (hQueuedCancelReceiverFit : (shareBalanceOf s receiver : Nat) + (queuedShares : Nat) <= MAX_UINT256)
    (hRepairSharesAdd : (queuedShares : Nat) + (repairShares : Nat) <= MAX_UINT256)
    (hRepairAssetsAdd : (queuedGross : Nat) + (repairGross : Nat) <= MAX_UINT256)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    malformed_pair_lifecycle_spec receiver owner repairOwner queuedShares queuedGross repairShares repairGross s := by
  let queueState := { s with sender := owner }
  let queuedState := queuedPostState queueState queuedShares queuedGross receiver owner
  let shareOnlyState := fulfilledPostState queuedState receiver 0 queuedGross
  let assetOnlyState := cancelledPostState queuedState receiver queuedShares 0
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hReceiverSlot : receiver ≠ 0 := by
    simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hOwnerSlot : owner ≠ 0 := by simpa [zeroAddress] using (show owner ≠ zeroAddress by simpa using hOwner)
  have hRepairOwnerSlot : repairOwner ≠ 0 := by
    simpa [zeroAddress] using (show repairOwner ≠ zeroAddress by simpa using hRepairOwner)
  have hOwnerNotVaultSlot : owner ≠ s.thisAddress := by simpa [vaultAddress] using hOwnerNotVault
  have hRepairOwnerNotVaultSlot : repairOwner ≠ s.thisAddress := by
    simpa [vaultAddress] using hRepairOwnerNotVault
  have hRepairNotOwner : repairOwner ≠ owner := by
    simpa using (show owner ≠ repairOwner by simpa using hDistinctOwners).symm
  have hUnpausedSlot : s.storage 3 = 0 := by simpa [pausedOf] using hUnpaused
  have hInitialSharesSlot : s.storageMap 6 receiver = 0 := by
    simpa [pendingSharesOf] using hInitialPendingShares
  have hInitialAssetsSlot : s.storageMap 7 receiver = 0 := by
    simpa [pendingAssetsOf] using hInitialPendingAssets
  have hInitialTotalSlot : s.storage 0 = 0 := by
    simpa [totalPendingAssetsOf] using hInitialPendingTotal
  have hQueueTotalFit : (s.storage 0 : Nat) + (queuedGross : Nat) ≤ MAX_UINT256 := by
    rw [hInitialTotalSlot]
    simpa using Verity.Core.Uint256.val_le_max queuedGross
  have hQueueSharesFit : (s.storageMap 6 receiver : Nat) + (queuedShares : Nat) ≤ MAX_UINT256 := by
    rw [hInitialSharesSlot]
    simpa using Verity.Core.Uint256.val_le_max queuedShares
  have hQueueAssetsFit : (s.storageMap 7 receiver : Nat) + (queuedGross : Nat) ≤ MAX_UINT256 := by
    rw [hInitialAssetsSlot]
    simpa using Verity.Core.Uint256.val_le_max queuedGross
  have hQueuedZero :
      (if (0 : Uint256) > s.storage 0 then sub 0 (s.storage 0) else 0) < queuedGross := by
    simpa using hQueuedGrossPositive
  have hQueuedRun :
      (YoAsyncRedemptionEscrow.requestRedeem queuedShares receiver owner queuedGross 0
        true true true true).run queueState = ContractResult.success 0 queuedState := by
    apply requestRedeem_queued_run queuedShares queuedGross 0 receiver owner queueState
    · simpa [queueState] using hVaultSlot
    · simpa [queueState] using hOwnerSlot
    · simpa [queueState] using hReceiverSlot
    · simpa [queueState] using hOwnerNotVaultSlot
    · rfl
    · simpa [queueState] using hUnpausedSlot
    · exact hQueuedSharesPositive
    · simpa [queueState, shareBalanceOf] using hOwnerShares
    · simpa [queueState] using hQueuedZero
    · simpa [queueState] using hQueueTotalFit
    · simpa [queueState] using hQueueSharesFit
    · simpa [queueState] using hQueueAssetsFit
  have hQueuedPendingShares : pendingSharesOf queuedState receiver = queuedShares := by
    simp [queuedState, queueState, queuedPostState, mapWriteState, pendingSharesOf,
      ContractState.writeSlot, ContractState.writeMap, hInitialSharesSlot]
    exact Verity.Core.Uint256.zero_add queuedShares
  have hQueuedPendingAssets : pendingAssetsOf queuedState receiver = queuedGross := by
    simp [queuedState, queueState, queuedPostState, mapWriteState, pendingAssetsOf,
      ContractState.writeSlot, ContractState.writeMap, hInitialAssetsSlot]
    exact Verity.Core.Uint256.zero_add queuedGross
  have hQueuedPendingTotal : totalPendingAssetsOf queuedState = queuedGross := by
    simp [queuedState, queueState, queuedPostState, mapWriteState, totalPendingAssetsOf,
      ContractState.writeSlot, ContractState.writeMap, hInitialTotalSlot]
    exact Verity.Core.Uint256.zero_add queuedGross
  have hQueuedAuthority : queuedState.storageAddr 9 ≠ 0 := by
    simpa [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hAuthoritySlot
  have hQueuedVault : queuedState.thisAddress ≠ 0 := by
    simpa [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hVaultSlot
  have hQueuedUnpaused : queuedState.storage 3 = 0 := by
    simpa [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hUnpausedSlot
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeFitsSlot : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeDenominator] using hFeeFits
  have hFeeBound :
      (mulDiv512Up queuedGross (s.storage 1) (add (s.storage 1) feeDenominator) : Nat) ≤
        (queuedGross : Nat) := by
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using
      feeAmountOf_le_gross s queuedGross hFeeDivisor
  have hFeeSub : ¬queuedGross.val <
      (mulDiv512Up queuedGross (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 =
      add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge hFeeBound
  have hQueuedFeeFit : (queuedState.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hFeeFitsSlot
  have hQueuedFeeSub : ¬queuedGross.val <
      (mulDiv512Up queuedGross (queuedState.storage 1)
        (1000000000000000000 + queuedState.storage 1) : Nat) := by
    simpa [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hFeeSub
  have hVaultCapacity : (s.storageMap 5 s.thisAddress : Nat) + (queuedShares : Nat) ≤ MAX_UINT256 := by
    have hSeq : (s.storageMap 5 s.thisAddress : Nat) + (queuedShares : Nat) +
        (repairShares : Nat) ≤ (s.storage 4 : Nat) := by
      simpa [shareBalanceOf, vaultAddress, totalSupplyOf] using hVaultSequentialCapacity
    have hSupplyMax : (s.storage 4 : Nat) ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max _
    omega
  have hVaultAddVal : (add (s.storageMap 5 s.thisAddress) queuedShares : Nat) =
      (s.storageMap 5 s.thisAddress : Nat) + (queuedShares : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hVaultCapacity)
  have hQueuedVaultBalanceBase : queuedState.storageMap 5 queuedState.thisAddress =
      add (s.storageMap 5 s.thisAddress) queuedShares := by
    simp [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, hOwnerNotVaultSlot]
  have hQueuedVaultShares : (0 : Uint256).val ≤
      (queuedState.storageMap 5 queuedState.thisAddress).val := Nat.zero_le _
  have hQueuedSharesNe : queuedShares ≠ 0 := by
    intro hZero
    have hVal : queuedShares.val = 0 := by simpa [hZero]
    exact (Nat.ne_of_gt (by simpa using hQueuedSharesPositive)) hVal
  have hQueuedGrossNe : queuedGross ≠ 0 := by
    intro hZero
    have hVal : queuedGross.val = 0 := by simpa [hZero]
    exact (Nat.ne_of_gt (by simpa using hQueuedGrossPositive)) hVal
  have hQueuedPendingSharesSlot : queuedState.storageMap 6 receiver = queuedShares :=
    hQueuedPendingShares
  have hQueuedPendingAssetsSlot : queuedState.storageMap 7 receiver = queuedGross :=
    hQueuedPendingAssets
  have hQueuedPendingTotalSlot : queuedState.storage 0 = queuedGross :=
    hQueuedPendingTotal
  have hShareOnlyRun :
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 queuedGross true true true true).run queuedState =
        ContractResult.success () shareOnlyState := by
    apply fulfillRedeem_run_true receiver 0 queuedGross queuedState hQueuedAuthority hQueuedVault
    · rw [hQueuedPendingSharesSlot]
      exact hQueuedSharesNe
    · rw [hQueuedPendingAssetsSlot]
      exact hQueuedGrossNe
    · simp
    · rw [hQueuedPendingAssetsSlot]
    · rw [hQueuedPendingTotalSlot]
    · exact hQueuedVaultShares
    · exact hQueuedUnpaused
    · exact hQueuedFeeFit
    · exact hQueuedFeeSub
  have hQueuedVaultForCancel : queuedShares.val ≤
      (queuedState.storageMap 5 queuedState.thisAddress).val := by
    rw [hQueuedVaultBalanceBase, hVaultAddVal]
    omega
  have hAssetOnlyRun :
      (YoAsyncRedemptionEscrow.cancelRedeem receiver queuedShares 0 true true).run queuedState =
        ContractResult.success () assetOnlyState := by
    apply cancelRedeem_run_true receiver queuedShares 0 queuedState hQueuedAuthority hQueuedVault
      (by simpa [zeroAddress] using hReceiverSlot)
    · rw [hQueuedPendingSharesSlot]
      exact hQueuedSharesNe
    · rw [hQueuedPendingAssetsSlot]
      exact hQueuedGrossNe
    · rw [hQueuedPendingSharesSlot]
    · simp
    · simp
    · exact hQueuedVaultForCancel
    · exact hQueuedUnpaused
  have hShareOnlyPendingShares : pendingSharesOf shareOnlyState receiver = queuedShares := by
    simp [shareOnlyState, fulfilledPostState, burnPostState, pendingFulfillPostState,
      pendingSharesOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hQueuedPendingSharesSlot]
    exact uint_sub_zero queuedShares
  have hShareOnlyPendingAssets : pendingAssetsOf shareOnlyState receiver = 0 := by
    simp [shareOnlyState, fulfilledPostState, burnPostState, pendingFulfillPostState,
      pendingAssetsOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hQueuedPendingAssetsSlot]
    exact Verity.Core.Uint256.sub_self queuedGross
  have hShareOnlyPendingTotal : totalPendingAssetsOf shareOnlyState = 0 := by
    simp [shareOnlyState, fulfilledPostState, burnPostState, pendingFulfillPostState,
      totalPendingAssetsOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hQueuedPendingTotalSlot]
    exact Verity.Core.Uint256.sub_self queuedGross
  have hAssetOnlyPendingShares : pendingSharesOf assetOnlyState receiver = 0 := by
    by_cases hSelf : queuedState.thisAddress = receiver
    · simp [assetOnlyState, cancelledPostState, transferPostState, pendingFulfillPostState,
        pendingSharesOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hQueuedPendingSharesSlot, hSelf]
      exact Verity.Core.Uint256.sub_self queuedShares
    · simp [assetOnlyState, cancelledPostState, transferPostState, pendingFulfillPostState,
        pendingSharesOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hQueuedPendingSharesSlot, hSelf]
      exact Verity.Core.Uint256.sub_self queuedShares
  have hAssetOnlyPendingAssets : pendingAssetsOf assetOnlyState receiver = queuedGross := by
    by_cases hSelf : queuedState.thisAddress = receiver
    · simp [assetOnlyState, cancelledPostState, transferPostState, pendingFulfillPostState,
        pendingAssetsOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hQueuedPendingAssetsSlot, hSelf]
      exact uint_sub_zero queuedGross
    · simp [assetOnlyState, cancelledPostState, transferPostState, pendingFulfillPostState,
        pendingAssetsOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hQueuedPendingAssetsSlot, hSelf]
      exact uint_sub_zero queuedGross
  have hAssetOnlyPendingTotal : totalPendingAssetsOf assetOnlyState = queuedGross := by
    by_cases hSelf : queuedState.thisAddress = receiver
    · simp [assetOnlyState, cancelledPostState, transferPostState, pendingFulfillPostState,
        totalPendingAssetsOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hQueuedPendingTotalSlot, hSelf]
      exact uint_sub_zero queuedGross
    · simp [assetOnlyState, cancelledPostState, transferPostState, pendingFulfillPostState,
        totalPendingAssetsOf, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hQueuedPendingTotalSlot, hSelf]
      exact uint_sub_zero queuedGross
  have hShareOnlyAuthority : shareOnlyState.storageAddr 9 ≠ 0 := by
    simpa [shareOnlyState, fulfilledPostState, burnPostState, pendingFulfillPostState,
      queuedState, mapWriteState, ContractState.writeSlot, ContractState.writeMap] using hQueuedAuthority
  have hAssetOnlyAuthority : assetOnlyState.storageAddr 9 ≠ 0 := by
    unfold assetOnlyState cancelledPostState transferPostState
    split <;>
      simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap] using hQueuedAuthority
  have hShareOnlyPendingSharesSlot : shareOnlyState.storageMap 6 receiver = queuedShares :=
    hShareOnlyPendingShares
  have hShareOnlyPendingAssetsSlot : shareOnlyState.storageMap 7 receiver = 0 :=
    hShareOnlyPendingAssets
  have hShareOnlyFulfill := fulfillRedeem_run_invalid_assets receiver shareOnlyState hShareOnlyAuthority
    (by rw [hShareOnlyPendingSharesSlot]; exact hQueuedSharesNe)
    hShareOnlyPendingAssetsSlot
  have hShareOnlyCancel := cancelRedeem_run_invalid_assets receiver shareOnlyState hShareOnlyAuthority
    (by rw [hShareOnlyPendingSharesSlot]; exact hQueuedSharesNe)
    hShareOnlyPendingAssetsSlot
  have hAssetOnlyFulfill := fulfillRedeem_run_invalid_shares receiver assetOnlyState hAssetOnlyAuthority
    (by simpa [pendingSharesOf] using hAssetOnlyPendingShares)
  have hAssetOnlyCancel := cancelRedeem_run_invalid_shares receiver assetOnlyState hAssetOnlyAuthority
    (by simpa [pendingSharesOf] using hAssetOnlyPendingShares)
  let repairShareState := { shareOnlyState with sender := repairOwner }
  let repairAssetState := { assetOnlyState with sender := repairOwner }
  have hRepairSharePendingShares : repairShareState.storageMap 6 receiver = queuedShares := by
    simpa [repairShareState, pendingSharesOf] using hShareOnlyPendingShares
  have hRepairSharePendingAssets : repairShareState.storageMap 7 receiver = 0 := by
    simpa [repairShareState, pendingAssetsOf] using hShareOnlyPendingAssets
  have hRepairSharePendingTotal : repairShareState.storage 0 = 0 := by
    simpa [repairShareState, totalPendingAssetsOf] using hShareOnlyPendingTotal
  have hRepairAssetPendingShares : repairAssetState.storageMap 6 receiver = 0 := by
    simpa [repairAssetState, pendingSharesOf] using hAssetOnlyPendingShares
  have hRepairAssetPendingAssets : repairAssetState.storageMap 7 receiver = queuedGross := by
    simpa [repairAssetState, pendingAssetsOf] using hAssetOnlyPendingAssets
  have hRepairAssetPendingTotal : repairAssetState.storage 0 = queuedGross := by
    simpa [repairAssetState, totalPendingAssetsOf] using hAssetOnlyPendingTotal
  have hRepairShareThis : repairShareState.thisAddress = s.thisAddress := by
    rfl
  have hRepairAssetThis : repairAssetState.thisAddress = s.thisAddress := by
    unfold repairAssetState assetOnlyState cancelledPostState transferPostState
    split <;> rfl
  have hRepairSharePaused : repairShareState.storage 3 = s.storage 3 := by
    rfl
  have hRepairAssetPaused : repairAssetState.storage 3 = s.storage 3 := by
    unfold repairAssetState assetOnlyState cancelledPostState transferPostState
    split <;> rfl
  have hQueuedThis : queuedState.thisAddress = s.thisAddress := by
    rfl
  have hVaultNotRepair : s.thisAddress ≠ repairOwner := hRepairOwnerNotVaultSlot.symm
  have hOwnerNotRepair : owner ≠ repairOwner := hRepairNotOwner.symm
  have hQueuedRepairBalance : queuedState.storageMap 5 repairOwner = s.storageMap 5 repairOwner := by
    simp [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, hRepairOwnerNotVaultSlot, hRepairNotOwner]
  have hRepairShareBalanceEq : repairShareState.storageMap 5 repairOwner =
      queuedState.storageMap 5 repairOwner := by
    simp [repairShareState, shareOnlyState, fulfilledPostState, burnPostState,
      pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hQueuedThis, hRepairOwnerNotVaultSlot]
  have hRepairShareBalance : repairShareState.storageMap 5 repairOwner >= repairShares := by
    rw [hRepairShareBalanceEq, hQueuedRepairBalance]
    simpa [shareBalanceOf] using hRepairOwnerShares
  have hRepairAssetBalance : repairAssetState.storageMap 5 repairOwner >= repairShares := by
    by_cases hRepairReceiver : repairOwner = receiver
    · subst repairOwner
      have hReceiverNotVault : receiver ≠ s.thisAddress := by
        simpa [vaultAddress] using hRepairOwnerNotVault
      have hVaultNotReceiver : s.thisAddress ≠ receiver := hReceiverNotVault.symm
      have hOwnerNotReceiver : owner ≠ receiver := hRepairNotOwner.symm
      have hReceiverAddVal : (add (s.storageMap 5 receiver) queuedShares : Nat) =
          (s.storageMap 5 receiver : Nat) + (queuedShares : Nat) := by
        exact Verity.Core.Uint256.add_eq_of_lt
          (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hQueuedCancelReceiverFit)
      have hQueuedReceiverBalance : queuedState.storageMap 5 receiver = s.storageMap 5 receiver := by
        simp [queuedState, queueState, queuedPostState, mapWriteState, ContractState.writeSlot,
          ContractState.writeMap, hReceiverNotVault, hRepairNotOwner]
      have hAssetReceiverBalance : repairAssetState.storageMap 5 receiver =
          add (queuedState.storageMap 5 receiver) queuedShares := by
        simp [repairAssetState, assetOnlyState, cancelledPostState, transferPostState,
          pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
          hQueuedThis, hVaultNotReceiver, hReceiverNotVault]
      have hRepairSharesVal : repairShares.val ≤ (s.storageMap 5 receiver).val := by
        simpa [shareBalanceOf] using hRepairOwnerShares
      rw [hAssetReceiverBalance, hQueuedReceiverBalance]
      change repairShares.val ≤ (add (s.storageMap 5 receiver) queuedShares).val
      rw [hReceiverAddVal]
      omega
    · have hReceiverNotRepair : receiver ≠ repairOwner := fun h => hRepairReceiver h.symm
      have hAssetRepairBalanceEq : repairAssetState.storageMap 5 repairOwner =
          queuedState.storageMap 5 repairOwner := by
        unfold repairAssetState assetOnlyState cancelledPostState transferPostState
        split <;>
          simp [pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
            ContractState.writeMap, hQueuedThis, hRepairOwnerNotVaultSlot, hRepairReceiver]
      rw [hAssetRepairBalanceEq, hQueuedRepairBalance]
      simpa [shareBalanceOf] using hRepairOwnerShares
  have hRepairShareVault : repairShareState.thisAddress ≠ 0 := by
    rw [hRepairShareThis]
    exact hVaultSlot
  have hRepairAssetVault : repairAssetState.thisAddress ≠ 0 := by
    rw [hRepairAssetThis]
    exact hVaultSlot
  have hRepairShareUnpaused : repairShareState.storage 3 = 0 := by
    rw [hRepairSharePaused]
    exact hUnpausedSlot
  have hRepairAssetUnpaused : repairAssetState.storage 3 = 0 := by
    rw [hRepairAssetPaused]
    exact hUnpausedSlot
  have hRepairShareRun :
      (YoAsyncRedemptionEscrow.requestRedeem repairShares receiver repairOwner repairGross 0
        true true true true).run repairShareState =
        ContractResult.success 0
          (queuedPostState repairShareState repairShares repairGross receiver repairOwner) := by
    apply requestRedeem_queued_run repairShares repairGross 0 receiver repairOwner repairShareState
    · exact hRepairShareVault
    · exact hRepairOwnerSlot
    · exact hReceiverSlot
    · rw [hRepairShareThis]
      exact hRepairOwnerNotVaultSlot
    · rfl
    · exact hRepairShareUnpaused
    · exact hRepairSharesPositive
    · exact hRepairShareBalance
    · simpa using hRepairGrossPositive
    · rw [hRepairSharePendingTotal]
      simpa using Verity.Core.Uint256.val_le_max repairGross
    · rw [hRepairSharePendingShares]
      exact hRepairSharesAdd
    · rw [hRepairSharePendingAssets]
      simpa using Verity.Core.Uint256.val_le_max repairGross
  have hRepairAssetRun :
      (YoAsyncRedemptionEscrow.requestRedeem repairShares receiver repairOwner repairGross 0
        true true true true).run repairAssetState =
        ContractResult.success 0
          (queuedPostState repairAssetState repairShares repairGross receiver repairOwner) := by
    apply requestRedeem_queued_run repairShares repairGross 0 receiver repairOwner repairAssetState
    · exact hRepairAssetVault
    · exact hRepairOwnerSlot
    · exact hReceiverSlot
    · rw [hRepairAssetThis]
      exact hRepairOwnerNotVaultSlot
    · rfl
    · exact hRepairAssetUnpaused
    · exact hRepairSharesPositive
    · exact hRepairAssetBalance
    · simpa using hRepairGrossPositive
    · rw [hRepairAssetPendingTotal]
      exact hRepairAssetsAdd
    · rw [hRepairAssetPendingShares]
      simpa using Verity.Core.Uint256.val_le_max repairShares
    · rw [hRepairAssetPendingAssets]
      exact hRepairAssetsAdd
  have hFinalRepairShareShares :
      pendingSharesOf
        (queuedPostState repairShareState repairShares repairGross receiver repairOwner) receiver =
        add queuedShares repairShares := by
    rw [show pendingSharesOf
      (queuedPostState repairShareState repairShares repairGross receiver repairOwner) receiver =
        add (pendingSharesOf repairShareState receiver) repairShares by
      simp [pendingSharesOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [show pendingSharesOf repairShareState receiver = queuedShares by
      simpa [pendingSharesOf] using hRepairSharePendingShares]
  have hFinalRepairShareAssets :
      pendingAssetsOf
        (queuedPostState repairShareState repairShares repairGross receiver repairOwner) receiver =
        repairGross := by
    rw [show pendingAssetsOf
      (queuedPostState repairShareState repairShares repairGross receiver repairOwner) receiver =
        add (pendingAssetsOf repairShareState receiver) repairGross by
      simp [pendingAssetsOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [show pendingAssetsOf repairShareState receiver = 0 by
      simpa [pendingAssetsOf] using hRepairSharePendingAssets]
    exact Verity.Core.Uint256.zero_add repairGross
  have hFinalRepairAssetShares :
      pendingSharesOf
        (queuedPostState repairAssetState repairShares repairGross receiver repairOwner) receiver =
        repairShares := by
    rw [show pendingSharesOf
      (queuedPostState repairAssetState repairShares repairGross receiver repairOwner) receiver =
        add (pendingSharesOf repairAssetState receiver) repairShares by
      simp [pendingSharesOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [show pendingSharesOf repairAssetState receiver = 0 by
      simpa [pendingSharesOf] using hRepairAssetPendingShares]
    exact Verity.Core.Uint256.zero_add repairShares
  have hFinalRepairAssetAssets :
      pendingAssetsOf
        (queuedPostState repairAssetState repairShares repairGross receiver repairOwner) receiver =
        add queuedGross repairGross := by
    rw [show pendingAssetsOf
      (queuedPostState repairAssetState repairShares repairGross receiver repairOwner) receiver =
        add (pendingAssetsOf repairAssetState receiver) repairGross by
      simp [pendingAssetsOf, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap]]
    rw [show pendingAssetsOf repairAssetState receiver = queuedGross by
      simpa [pendingAssetsOf] using hRepairAssetPendingAssets]
  unfold malformed_pair_lifecycle_spec
  dsimp
  rw [show { s with sender := owner } = queueState by rfl, hQueuedRun]
  simp only [ContractResult.snd_success]
  rw [hShareOnlyRun, hAssetOnlyRun]
  simp only [ContractResult.snd_success]
  rw [hShareOnlyFulfill, hShareOnlyCancel, hAssetOnlyFulfill, hAssetOnlyCancel,
    hRepairShareRun, hRepairAssetRun]
  simp only [ContractResult.snd_success]
  refine ⟨queuedPostState repairShareState repairShares repairGross receiver repairOwner,
    queuedPostState repairAssetState repairShares repairGross receiver repairOwner,
    True.intro, True.intro, True.intro, hShareOnlyPendingShares, hShareOnlyPendingAssets,
    hShareOnlyPendingTotal, hAssetOnlyPendingShares, hAssetOnlyPendingAssets, hAssetOnlyPendingTotal,
    True.intro, True.intro, True.intro, True.intro, rfl, rfl, hFinalRepairShareShares, hFinalRepairShareAssets,
    hFinalRepairAssetShares, hFinalRepairAssetAssets⟩

/-- Under the explicit no-callback-state-mutation assumption, a successful
    fulfillment directly changes only the selected receiver record. -/
theorem lifecycle_bounds_and_isolation
    (receiver other : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hShareBound : shares <= pendingSharesOf s receiver)
    (hAssetBound : grossAssets <= pendingAssetsOf s receiver)
    (hGlobalBound : grossAssets <= totalPendingAssetsOf s)
    (hVaultShares : shares <= shareBalanceOf s (vaultAddress s))
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    let result :=
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s
    lifecycle_bounds_and_isolation_spec shares grossAssets receiver other s result := by
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using
      (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using
      (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hPendingSharesSlot : s.storageMap 6 receiver ≠ 0 := by
    simpa [pendingSharesOf] using
      (show pendingSharesOf s receiver ≠ 0 by simpa using hPendingShares)
  have hPendingAssetsSlot : s.storageMap 7 receiver ≠ 0 := by
    simpa [pendingAssetsOf] using
      (show pendingAssetsOf s receiver ≠ 0 by simpa using hPendingAssets)
  have hShareBoundSlot : shares.val ≤ (s.storageMap 6 receiver).val := by
    simpa [pendingSharesOf] using hShareBound
  have hAssetBoundSlot : grossAssets.val ≤ (s.storageMap 7 receiver).val := by
    simpa [pendingAssetsOf] using hAssetBound
  have hGlobalBoundSlot : grossAssets.val ≤ (s.storage 0).val := by
    simpa [totalPendingAssetsOf] using hGlobalBound
  have hVaultSharesSlot : shares.val ≤ (s.storageMap 5 s.thisAddress).val := by
    simpa [shareBalanceOf, vaultAddress] using hVaultShares
  have hUnpausedSlot : s.storage 3 = 0 := by
    simpa [pausedOf] using hUnpaused
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeFitsSlot : (s.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeDenominator] using hFeeFits
  have hFeeBound :
      (mulDiv512Up grossAssets (s.storage 1) (add (s.storage 1) feeDenominator) : Nat) ≤
        grossAssets.val := by
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using
      feeAmountOf_le_gross s grossAssets hFeeDivisor
  have hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1)
        (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 =
      add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge hFeeBound
  have hRun := fulfillRedeem_run_true receiver shares grossAssets s hAuthoritySlot hVaultSlot
    hPendingSharesSlot hPendingAssetsSlot hShareBoundSlot hAssetBoundSlot hGlobalBoundSlot
    hVaultSharesSlot hUnpausedSlot hFeeFitsSlot hFeeSub
  unfold lifecycle_bounds_and_isolation_spec
  refine ⟨fulfilledPostState s receiver shares grossAssets, hRun, hShareBound, hAssetBound, ?_, ?_,
    ?_, ?_⟩
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf]
  · intro hDistinct
    have hOther : other ≠ receiver := by
      intro hEqual
      subst other
      simp at hDistinct
    constructor <;>
      simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, pendingAssetsOf,
        hOther]

/-- Source-reachable Candidate G trace from a queued `(100,200)` pair. It
    proves all six zero-component settlement shapes and the positive,
    non-proportional `(1,199)` fulfillment remain accepted. -/
theorem candidate_g_source_reachability
    (receiver owner : Address) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hReceiverNotOwner : receiver != owner)
    (hReceiverNotVault : receiver != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hUnpaused : pausedOf s = 0)
    (hInitialPendingShares : pendingSharesOf s receiver = 0)
    (hInitialPendingAssets : pendingAssetsOf s receiver = 0)
    (hInitialPendingTotal : totalPendingAssetsOf s = 0)
    (hOwnerShares : shareBalanceOf s owner >= 100)
    (hErc20 : erc20WellFormed s)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    candidate_g_source_reachable_spec receiver owner s := by
  let q := queuedPostState s 100 200 receiver owner
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using
      (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using
      (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hReceiverSlot : receiver ≠ 0 := by
    simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hOwnerSlot : owner ≠ 0 := by
    simpa [zeroAddress] using (show owner ≠ zeroAddress by simpa using hOwner)
  have hOwnerNotVaultSlot : owner ≠ s.thisAddress := by
    simpa [vaultAddress] using hOwnerNotVault
  have hUnpausedSlot : s.storage 3 = 0 := by
    simpa [pausedOf] using hUnpaused
  have hInitialShares : s.storageMap 6 receiver = 0 := by
    simpa [pendingSharesOf] using hInitialPendingShares
  have hInitialAssets : s.storageMap 7 receiver = 0 := by
    simpa [pendingAssetsOf] using hInitialPendingAssets
  have hInitialTotal : s.storage 0 = 0 := by
    simpa [totalPendingAssetsOf] using hInitialPendingTotal
  have hOwnerBalance : (100 : Uint256).val ≤ (s.storageMap 5 owner).val := by
    simpa [shareBalanceOf] using hOwnerShares
  have hQueueRun :
      (YoAsyncRedemptionEscrow.requestRedeem 100 receiver owner 200 0
        true true true true).run s = ContractResult.success 0 q := by
    apply requestRedeem_queued_run 100 200 0 receiver owner s hVaultSlot hOwnerSlot hReceiverSlot
      hOwnerNotVaultSlot hOwnerIsSender hUnpausedSlot (by native_decide) hOwnerBalance
    · rw [hInitialTotal]
      native_decide
    · rw [hInitialTotal]
      native_decide
    · rw [hInitialShares]
      native_decide
    · rw [hInitialAssets]
      native_decide
  have hQAuthority : q.storageAddr 9 ≠ 0 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hAuthoritySlot
  have hQVault : q.thisAddress ≠ 0 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultSlot
  have hQUnpaused : q.storage 3 = 0 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hUnpausedSlot
  have hQShares : q.storageMap 6 receiver = 100 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hInitialShares]
    exact Verity.Core.Uint256.zero_add 100
  have hQAssets : q.storageMap 7 receiver = 200 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hInitialAssets]
    exact Verity.Core.Uint256.zero_add 200
  have hQTotal : q.storage 0 = 200 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hInitialTotal]
    exact Verity.Core.Uint256.zero_add 200
  have hVaultPlusFit : (s.storageMap 5 s.thisAddress : Nat) + (100 : Nat) ≤ MAX_UINT256 := by
    have hVaultNotOwner : (s.thisAddress != owner) = true := by
      simpa [BEq.beq] using (Ne.symm hOwnerNotVaultSlot)
    have hBound : (s.storageMap 5 s.thisAddress : Nat) + (s.storageMap 5 owner : Nat) ≤
        (s.storage 4 : Nat) := by
      simpa [shareBalanceOf, totalSupplyOf] using
        hErc20.2 s.thisAddress owner hVaultNotOwner
    have hSupplyMax : (s.storage 4 : Nat) ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max _
    change (s.storageMap 5 s.thisAddress : Nat) + (100 : Nat) ≤ MAX_UINT256
    have hOwnerNat : (100 : Nat) ≤ (s.storageMap 5 owner : Nat) := hOwnerBalance
    omega
  have hVaultPlusVal : (add (s.storageMap 5 s.thisAddress) 100 : Nat) =
      (s.storageMap 5 s.thisAddress : Nat) + (100 : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hVaultPlusFit)
  have hQVaultBase : q.storageMap 5 q.thisAddress = add (s.storageMap 5 s.thisAddress) 100 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hOwnerNotVaultSlot]
  have hQVaultHundred : (100 : Uint256).val ≤ (q.storageMap 5 q.thisAddress).val := by
    rw [hQVaultBase]
    change (100 : Nat) ≤ (add (s.storageMap 5 s.thisAddress) 100 : Nat)
    rw [hVaultPlusVal]
    omega
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hQFeeFits : (q.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      feeDenominator] using hFeeFits
  have hFeeSub (amount : Uint256) : ¬amount.val <
      (mulDiv512Up amount (s.storage 1) (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 =
      add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge (by
      simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using
        feeAmountOf_le_gross s amount hFeeDivisor)
  have hQFeeSub (amount : Uint256) : ¬amount.val <
      (mulDiv512Up amount (q.storage 1) (1000000000000000000 + q.storage 1) : Nat) := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeSub amount
  have hFulfill00 := fulfillRedeem_run_true receiver 0 0 q hQAuthority hQVault
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQTotal]; native_decide) (by simp)
    hQUnpaused hQFeeFits (hQFeeSub 0)
  have hCancel00 := cancelRedeem_run_zero receiver q hQAuthority hQVault hReceiverSlot
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide) hQUnpaused
  have hFulfill0Full := fulfillRedeem_run_true receiver 0 200 q hQAuthority hQVault
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQShares]; native_decide) (by rw [hQAssets])
    (by rw [hQTotal]) (by simp)
    hQUnpaused hQFeeFits (hQFeeSub 200)
  have hFulfillFull0 := fulfillRedeem_run_true receiver 100 0 q hQAuthority hQVault
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQShares]) (by rw [hQAssets]; native_decide)
    (by rw [hQTotal]; native_decide) hQVaultHundred
    hQUnpaused hQFeeFits (hQFeeSub 0)
  have hCancel0Full := cancelRedeem_run_true receiver 0 200 q hQAuthority hQVault hReceiverSlot
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQShares]; native_decide) (by rw [hQAssets])
    (by rw [hQTotal]) (by simp) hQUnpaused
  have hCancelFull0 := cancelRedeem_run_true receiver 100 0 q hQAuthority hQVault hReceiverSlot
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQShares]) (by rw [hQAssets]; native_decide)
    (by rw [hQTotal]; native_decide) hQVaultHundred hQUnpaused
  have hNonProportional := fulfillRedeem_run_true receiver 1 199 q hQAuthority hQVault
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQShares]; native_decide) (by rw [hQAssets]; native_decide)
    (by rw [hQTotal]; native_decide) (by
      change (1 : Nat) ≤ (q.storageMap 5 q.thisAddress : Nat)
      have hOneHundred : (1 : Nat) ≤ (100 : Nat) := by native_decide
      exact hOneHundred.trans hQVaultHundred) hQUnpaused hQFeeFits (hQFeeSub 199)
  unfold candidate_g_source_reachable_spec
  dsimp
  rw [hQueueRun]
  simp only [ContractResult.snd_success]
  rw [hFulfill00, hCancel00, hFulfill0Full, hFulfillFull0, hCancel0Full, hCancelFull0,
    hNonProportional]
  simp only [ContractResult.snd_success]
  refine ⟨True.intro, True.intro, True.intro, ?_, ?_, True.intro, ?_, ?_, ?_, True.intro,
    ?_, ?_, ?_, True.intro, ?_, ?_, ?_, True.intro, ?_, ?_, ?_, True.intro, ?_, ?_, ?_⟩
  · simp [evmObservableStorageEq, fulfilledPostState, burnPostState, pendingFulfillPostState,
      mapWriteState, ContractState.writeSlot, ContractState.writeMap, uint_sub_zero]
    constructor
    · funext sl
      by_cases h4 : sl = 4 <;> by_cases h0 : sl = 0 <;> simp [h4, h0, uint_sub_zero]
    · funext sl key
      by_cases h5 : sl = 5 ∧ key = q.thisAddress <;>
        by_cases h7 : sl = 7 ∧ key = receiver <;>
        by_cases h6 : sl = 6 ∧ key = receiver <;>
          simp [h5, h7, h6, uint_sub_zero]
  · by_cases hSelf : q.thisAddress = receiver
    · simp [evmObservableStorageEq, cancelZeroPostState, transferZeroPostState,
        pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hSelf, uint_sub_zero]
      constructor
      · funext sl
        by_cases h0 : sl = 0 <;> simp [h0, uint_sub_zero]
      · funext sl key
        by_cases h7 : sl = 7 ∧ key = receiver <;>
          by_cases h6 : sl = 6 ∧ key = receiver <;>
            simp [h7, h6, uint_sub_zero]
    · simp [evmObservableStorageEq, cancelZeroPostState, transferZeroPostState,
        pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
        hSelf, uint_sub_zero, uint_add_zero]
      have hSelfBool : (q.thisAddress == receiver) = false := by simp [hSelf]
      constructor
      · funext sl
        by_cases h0 : sl = 0 <;> simp [h0, uint_sub_zero]
      · funext sl key
        by_cases h5r : sl = 5 ∧ key = receiver <;>
          by_cases h5v : sl = 5 ∧ key = q.thisAddress <;>
          by_cases h7 : sl = 7 ∧ key = receiver <;>
          by_cases h6 : sl = 6 ∧ key = receiver <;>
            simp [h5r, h5v, h7, h6, hSelf, hSelfBool, uint_sub_zero, uint_add_zero]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, hQShares] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hQAssets] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf, hQTotal] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, hQShares] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hQAssets] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf, hQTotal] <;> native_decide
  · by_cases hSelf : q.thisAddress = receiver <;>
      simp [cancelledPostState, transferPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, hQShares, hSelf,
        uint_sub_zero, uint_sub_self]
  · by_cases hSelf : q.thisAddress = receiver <;>
      simp [cancelledPostState, transferPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hQAssets, hSelf,
        uint_sub_zero, uint_sub_self]
  · by_cases hSelf : q.thisAddress = receiver <;>
      simp [cancelledPostState, transferPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf, hQTotal, hSelf,
        uint_sub_zero, uint_sub_self]
  · by_cases hSelf : q.thisAddress = receiver <;>
      simp [cancelledPostState, transferPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, hQShares, hSelf,
        uint_sub_zero, uint_sub_self]
  · by_cases hSelf : q.thisAddress = receiver <;>
      simp [cancelledPostState, transferPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hQAssets, hSelf,
        uint_sub_zero, uint_sub_self]
  · by_cases hSelf : q.thisAddress = receiver <;>
      simp [cancelledPostState, transferPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf, hQTotal, hSelf,
        uint_sub_zero, uint_sub_self]
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, hQShares] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hQAssets] <;> native_decide
  · simp [fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, totalPendingAssetsOf, hQTotal] <;> native_decide

/-- A cleared record rejects fulfillment before inspecting either requested
component, so this form covers replay of the original nonzero pair. -/
private theorem fulfillRedeem_run_invalid_shares_replay
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : s.storageAddr 9 ≠ 0)
    (hPendingShares : s.storageMap 6 receiver = 0) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s =
      ContractResult.revert "InvalidSharesAmount" s := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.fulfillRedeem]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true true) _ s s true
    (isAuthorized_true_true_apply s hAuthority)]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingShares receiver) _ s s
    (s.storageMap 6 receiver) (by rfl)]
  rw [bind_apply_of_success (getMapping YoAsyncRedemptionEscrow.pendingAssets receiver) _ s s
    (s.storageMap 7 receiver) (by rfl)]
  rw [bind_apply_of_revert
    (Verity.require (s.storageMap 6 receiver != 0 && shares <= s.storageMap 6 receiver)
      "InvalidSharesAmount") _ s s "InvalidSharesAmount" (by
        simp [Verity.require, hPendingShares])]

/-- Full clear rejects immediate replay; a distinct, funded request owner can
    queue the pair again, with capacity for both source-permitted burns. -/
theorem full_clear_requeue_replay
    (receiver requestOwner : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hRequestOwner : requestOwner != zeroAddress)
    (hRequestOwnerNotVault : requestOwner != vaultAddress s)
    (hSharesPositive : shares > 0)
    (hGrossPositive : grossAssets > 0)
    (hUnpaused : pausedOf s = 0)
    (hPendingShares : pendingSharesOf s receiver = shares)
    (hPendingAssets : pendingAssetsOf s receiver = grossAssets)
    (hGlobal : totalPendingAssetsOf s >= grossAssets)
    (hVaultShares : shareBalanceOf s (vaultAddress s) >= shares)
    (hRequestShares : shareBalanceOf s requestOwner >= shares)
    (hErc20 : erc20WellFormed s)
    (hTwoBurnCapacity : 2 * (shares : Nat) <= (totalSupplyOf s : Nat))
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    full_clear_requeue_replay_spec receiver requestOwner shares grossAssets s := by
  let cleared := fulfilledPostState s receiver shares grossAssets
  let queueState := { cleared with sender := requestOwner }
  let repopulated := queuedPostState queueState shares grossAssets receiver requestOwner
  let final := fulfilledPostState repopulated receiver shares grossAssets
  have hAuthoritySlot : s.storageAddr 9 ≠ 0 := by
    simpa [authorityOf, zeroAddress] using
      (show authorityOf s ≠ zeroAddress by simpa using hAuthority)
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using
      (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hReceiverSlot : receiver ≠ 0 := by
    simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hRequestOwnerSlot : requestOwner ≠ 0 := by
    simpa [zeroAddress] using (show requestOwner ≠ zeroAddress by simpa using hRequestOwner)
  have hRequestOwnerNotVaultSlot : requestOwner ≠ s.thisAddress := by
    simpa [vaultAddress] using hRequestOwnerNotVault
  have hUnpausedSlot : s.storage 3 = 0 := by
    simpa [pausedOf] using hUnpaused
  have hPendingSharesSlot : s.storageMap 6 receiver = shares := by
    simpa [pendingSharesOf] using hPendingShares
  have hPendingAssetsSlot : s.storageMap 7 receiver = grossAssets := by
    simpa [pendingAssetsOf] using hPendingAssets
  have hGlobalSlot : grossAssets.val ≤ (s.storage 0).val := by
    simpa [totalPendingAssetsOf] using hGlobal
  have hVaultSharesSlot : shares.val ≤ (s.storageMap 5 s.thisAddress).val := by
    simpa [shareBalanceOf, vaultAddress] using hVaultShares
  have hRequestSharesSlot : shares.val ≤ (s.storageMap 5 requestOwner).val := by
    simpa [shareBalanceOf] using hRequestShares
  have hSharesNe : shares ≠ 0 := by
    intro hZero
    have : shares.val = 0 := by simpa [hZero]
    exact (Nat.ne_of_gt (by simpa using hSharesPositive)) this
  have hGrossNe : grossAssets ≠ 0 := by
    intro hZero
    have : grossAssets.val = 0 := by simpa [hZero]
    exact (Nat.ne_of_gt (by simpa using hGrossPositive)) this
  have hFeeFits : (s.storage 1 : Nat) + (feeDenominator : Nat) ≤ MAX_UINT256 := by
    simpa [feeDivisorFits, feeOnWithdrawOf, checkedAddFits] using hFeeDivisor
  have hFeeFitsSlot : (s.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeDenominator] using hFeeFits
  have hFeeBound :
      (mulDiv512Up grossAssets (s.storage 1) (add (s.storage 1) feeDenominator) : Nat) ≤
        grossAssets.val := by
    simpa [feeAmountOf, feeAmountWith, feeOnWithdrawOf] using
      feeAmountOf_le_gross s grossAssets hFeeDivisor
  have hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1)
        (1000000000000000000 + s.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + s.storage 1 =
      add (s.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + s.storage 1 =
        s.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge hFeeBound
  have hSettlement :
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s =
        ContractResult.success () cleared := by
    apply fulfillRedeem_run_true receiver shares grossAssets s hAuthoritySlot hVaultSlot
      (by rw [hPendingSharesSlot]; exact hSharesNe)
      (by rw [hPendingAssetsSlot]; exact hGrossNe)
      (by rw [hPendingSharesSlot])
      (by rw [hPendingAssetsSlot]) hGlobalSlot hVaultSharesSlot hUnpausedSlot hFeeFitsSlot hFeeSub
  have hClearedShares : cleared.storageMap 6 receiver = 0 := by
    simp [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, hPendingSharesSlot]
    exact Verity.Core.Uint256.sub_self shares
  have hClearedAssets : cleared.storageMap 7 receiver = 0 := by
    simp [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, hPendingAssetsSlot]
    exact Verity.Core.Uint256.sub_self grossAssets
  have hClearedAuthority : cleared.storageAddr 9 ≠ 0 := by
    simpa [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap] using hAuthoritySlot
  have hImmediateReplay := fulfillRedeem_run_invalid_shares_replay receiver shares grossAssets cleared
    hClearedAuthority hClearedShares
  have hClearedVault : cleared.thisAddress ≠ 0 := by
    simpa [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap] using hVaultSlot
  have hClearedUnpaused : cleared.storage 3 = 0 := by
    simpa [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap] using hUnpausedSlot
  have hClearedTotalFit : (cleared.storage 0 : Nat) + grossAssets.val ≤ MAX_UINT256 := by
    change (sub (s.storage 0) grossAssets : Nat) + grossAssets.val ≤ MAX_UINT256
    rw [Verity.EVM.Uint256.sub_eq_of_le hGlobalSlot]
    have hMax : (s.storage 0 : Nat) ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max _
    omega
  have hClearedRequestShares : shares.val ≤ (cleared.storageMap 5 requestOwner).val := by
    simp [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, hRequestOwnerNotVaultSlot]
    exact hRequestSharesSlot
  have hRequeue :
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver requestOwner grossAssets 0
        true true true true).run queueState = ContractResult.success 0 repopulated := by
    apply requestRedeem_queued_run shares grossAssets 0 receiver requestOwner queueState
    · simpa [queueState] using hClearedVault
    · exact hRequestOwnerSlot
    · exact hReceiverSlot
    · simpa [queueState] using hRequestOwnerNotVaultSlot
    · rfl
    · simpa [queueState] using hClearedUnpaused
    · exact hSharesPositive
    · simpa [queueState] using hClearedRequestShares
    · simpa using hGrossPositive
    · simpa [queueState] using hClearedTotalFit
    · rw [show queueState.storageMap 6 receiver = 0 by
        simpa [queueState] using hClearedShares]
      simpa using Verity.Core.Uint256.val_le_max shares
    · rw [show queueState.storageMap 7 receiver = 0 by
        simpa [queueState] using hClearedAssets]
      simpa using Verity.Core.Uint256.val_le_max grossAssets
  have hRepopulatedShares : repopulated.storageMap 6 receiver = shares := by
    simp [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState, hClearedShares]
    exact Verity.Core.Uint256.zero_add shares
  have hRepopulatedAssets : repopulated.storageMap 7 receiver = grossAssets := by
    simp [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState, hClearedAssets]
    exact Verity.Core.Uint256.zero_add grossAssets
  have hRepopulatedTotal : repopulated.storage 0 = add (cleared.storage 0) grossAssets := by
    simp [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState]
  have hRepopulatedAuthority : repopulated.storageAddr 9 ≠ 0 := by
    simpa [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState] using hClearedAuthority
  have hRepopulatedVault : repopulated.thisAddress ≠ 0 := by
    simpa [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState] using hClearedVault
  have hRepopulatedUnpaused : repopulated.storage 3 = 0 := by
    simpa [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState] using hClearedUnpaused
  have hRepopulatedVaultShares : shares.val ≤
      (repopulated.storageMap 5 repopulated.thisAddress).val := by
    have hVaultAfterClear : cleared.storageMap 5 cleared.thisAddress =
        sub (s.storageMap 5 s.thisAddress) shares := by
      simp [cleared, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
        ContractState.writeSlot, ContractState.writeMap]
    have hVaultAfterQueue : repopulated.storageMap 5 repopulated.thisAddress =
        add (cleared.storageMap 5 cleared.thisAddress) shares := by
      simp [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
        ContractState.writeMap, queueState, hRequestOwnerNotVaultSlot]
    rw [hVaultAfterQueue, hVaultAfterClear]
    have hRestored : add (sub (s.storageMap 5 s.thisAddress) shares) shares =
        s.storageMap 5 s.thisAddress := by
      exact Verity.Core.Uint256.sub_add_cancel_left _ _
    rw [hRestored]
    exact hVaultSharesSlot
  have hRepopulatedFeeFits : (repopulated.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState, cleared, fulfilledPostState, burnPostState,
      pendingFulfillPostState] using hFeeFitsSlot
  have hRepopulatedFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (repopulated.storage 1)
        (1000000000000000000 + repopulated.storage 1) : Nat) := by
    simpa [repopulated, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, queueState, cleared, fulfilledPostState, burnPostState,
      pendingFulfillPostState] using hFeeSub
  have hReplay :
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run
        repopulated = ContractResult.success () final := by
    apply fulfillRedeem_run_true receiver shares grossAssets repopulated hRepopulatedAuthority
      hRepopulatedVault (by rw [hRepopulatedShares]; exact hSharesNe)
      (by rw [hRepopulatedAssets]; exact hGrossNe) (by rw [hRepopulatedShares])
      (by rw [hRepopulatedAssets])
    · rw [hRepopulatedTotal]
      have hAdd : (add (cleared.storage 0) grossAssets : Nat) =
          (cleared.storage 0 : Nat) + grossAssets.val := by
        exact Verity.Core.Uint256.add_eq_of_lt
          (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hClearedTotalFit)
      rw [hAdd]
      omega
    · exact hRepopulatedVaultShares
    · exact hRepopulatedUnpaused
    · exact hRepopulatedFeeFits
    · exact hRepopulatedFeeSub
  unfold full_clear_requeue_replay_spec
  dsimp
  rw [hSettlement]
  simp only [ContractResult.snd_success]
  rw [hImmediateReplay]
  simp only [ContractResult.snd_revert]
  rw [show { cleared with sender := requestOwner } = queueState by rfl, hRequeue]
  simp only [ContractResult.snd_success]
  rw [hReplay]
  simp only [ContractResult.snd_success]
  refine ⟨True.intro, ?_, ?_, True.intro, True.intro, ?_, ?_, True.intro, ?_, ?_⟩
  · simpa [pendingSharesOf] using hClearedShares
  · simpa [pendingAssetsOf] using hClearedAssets
  · simpa [pendingSharesOf] using hRepopulatedShares
  · simpa [pendingAssetsOf] using hRepopulatedAssets
  · simp [final, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingSharesOf, hRepopulatedShares,
      uint_sub_self]
  · simp [final, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hRepopulatedAssets,
      uint_sub_self]

private theorem isAuthorized_no_authority_owner_apply
    (s : ContractState) (hNoAuthority : s.storageAddr 9 = 0)
    (hSenderOwner : s.sender = s.storageAddr 8) :
    YoAsyncRedemptionEscrow.isAuthorized true false s = ContractResult.success true s := by
  rw [YoAsyncRedemptionEscrow.isAuthorized]
  simp [Bind.bind, Verity.bind, getStorageAddr, msgSender, YoAsyncRedemptionEscrow.authority,
    YoAsyncRedemptionEscrow.owner, zeroAddress, hNoAuthority, hSenderOwner, Verity.pure, Pure.pure]

private theorem updateWithdrawFee_run_authorized
    (newFee : Uint256) (s : ContractState)
    (hAuthorized : YoAsyncRedemptionEscrow.isAuthorized true false s =
      ContractResult.success true s)
    (hFeeBound : newFee < maxFee) :
    (YoAsyncRedemptionEscrow.updateWithdrawFee newFee true false).run s =
      ContractResult.success () (s.writeSlot 1 newFee) := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.updateWithdrawFee]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true false) _ s s true hAuthorized]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rw [bind_apply_of_success (Verity.require (newFee < 100000000000000000) "InvalidFee") _ s s ()
    (by simpa [Verity.require, maxFee] using hFeeBound)]
  rfl

private theorem updateFeeRecipient_run_authorized
    (recipient : Address) (s : ContractState)
    (hAuthorized : YoAsyncRedemptionEscrow.isAuthorized true false s =
      ContractResult.success true s) :
    (YoAsyncRedemptionEscrow.updateFeeRecipient recipient true false).run s =
      ContractResult.success () (s.writeAddrSlot 2 recipient) := by
  unfold Contract.run
  rw [YoAsyncRedemptionEscrow.updateFeeRecipient]
  rw [bind_apply_of_success (YoAsyncRedemptionEscrow.isAuthorized true false) _ s s true hAuthorized]
  rw [bind_apply_of_success (Verity.require true "Unauthorized") _ s s () (by rfl)]
  rfl

private theorem fulfillRedeem_run_authorized_fee_revert
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (authorityAllows : Bool)
    (hAuthorized :
      YoAsyncRedemptionEscrow.isAuthorized true authorityAllows s =
        ContractResult.success true s)
    (hAuthority : s.storageAddr 9 = 0)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat))
    (hFeePositive : 0 <
      (mulDiv512Up grossAssets (s.storage 1) (s.storage 1 + 1000000000000000000) : Nat))
    (hFeeRecipient : s.storageAddr 2 ≠ 0) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows true false).run s =
      ContractResult.revert "SafeERC20FailedOperation" s := by
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVault
  have hPendingUnpaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hUnpaused
  have hPendingVaultShares : shares.val ≤
      ((pendingFulfillPostState s receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState s receiver shares grossAssets).thisAddress).val := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultShares
  have hPendingFeeAdd :
      ((pendingFulfillPostState s receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeAdd
  have hPendingFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        (1000000000000000000 + (pendingFulfillPostState s receiver shares grossAssets).storage 1) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeSub
  have hPendingFeePositive : 0 <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        ((pendingFulfillPostState s receiver shares grossAssets).storage 1 + 1000000000000000000) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeePositive
  have hPendingRecipient : (pendingFulfillPostState s receiver shares grossAssets).storageAddr 2 ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeRecipient
  have hWithdraw : YoAsyncRedemptionEscrow._withdraw receiver
      (pendingFulfillPostState s receiver shares grossAssets).thisAddress grossAssets shares true false
      (pendingFulfillPostState s receiver shares grossAssets) =
        ContractResult.revert "SafeERC20FailedOperation"
          (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares) :=
    withdraw_apply_fee_revert (pendingFulfillPostState s receiver shares grossAssets)
      receiver shares grossAssets hPendingVault hPendingUnpaused hPendingVaultShares hPendingFeeAdd
      hPendingFeeSub hPendingFeePositive hPendingRecipient
  have hRaw := fulfillRedeem_apply_authorized_of_withdraw receiver shares grossAssets s authorityAllows
    true false (ContractResult.revert "SafeERC20FailedOperation"
      (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares)) hAuthorized
    hPendingShares hPendingAssets hShareBound hAssetBound hGlobalBound hWithdraw
  unfold Contract.run
  rw [hRaw]

private theorem fulfillRedeem_run_authorized_no_authority
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (authorityAllows : Bool)
    (hAuthorized :
      YoAsyncRedemptionEscrow.isAuthorized true authorityAllows s =
        ContractResult.success true s)
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows true true).run s =
      ContractResult.success () (fulfilledPostState s receiver shares grossAssets) := by
  have hPendingVault : (pendingFulfillPostState s receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVault
  have hPendingUnpaused : (pendingFulfillPostState s receiver shares grossAssets).storage 3 = 0 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hUnpaused
  have hPendingVaultShares : shares.val ≤
      ((pendingFulfillPostState s receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState s receiver shares grossAssets).thisAddress).val := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultShares
  have hPendingFeeAdd :
      ((pendingFulfillPostState s receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeAdd
  have hPendingFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState s receiver shares grossAssets).storage 1)
        (1000000000000000000 + (pendingFulfillPostState s receiver shares grossAssets).storage 1) : Nat) := by
    simpa [pendingFulfillPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hFeeSub
  have hWithdraw : YoAsyncRedemptionEscrow._withdraw receiver
      (pendingFulfillPostState s receiver shares grossAssets).thisAddress grossAssets shares true true
      (pendingFulfillPostState s receiver shares grossAssets) =
        ContractResult.success ()
          (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares) :=
    withdraw_apply (pendingFulfillPostState s receiver shares grossAssets) receiver shares grossAssets
      hPendingVault hPendingUnpaused hPendingVaultShares hPendingFeeAdd hPendingFeeSub
  have hRaw := fulfillRedeem_apply_authorized_of_withdraw receiver shares grossAssets s authorityAllows
    true true (ContractResult.success ()
      (burnPostState (pendingFulfillPostState s receiver shares grossAssets) shares)) hAuthorized
    hPendingShares hPendingAssets hShareBound hAssetBound hGlobalBound hWithdraw
  unfold Contract.run
  rw [hRaw]
  rfl

/-- Setting a zero fee recipient preserves all fulfillment guards while
eliminating the second-transfer branch.  Keeping the address write abstract
avoids repeatedly elaborating the concrete queued state at the call site. -/
private theorem fulfillRedeem_run_authorized_no_authority_zero_recipient
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (authorityAllows : Bool)
    (hAuthorized :
      YoAsyncRedemptionEscrow.isAuthorized true authorityAllows (s.writeAddrSlot 2 zeroAddress) =
        ContractResult.success true (s.writeAddrSlot 2 zeroAddress))
    (hVault : s.thisAddress ≠ 0)
    (hPendingShares : s.storageMap 6 receiver ≠ 0)
    (hPendingAssets : s.storageMap 7 receiver ≠ 0)
    (hShareBound : shares.val ≤ (s.storageMap 6 receiver).val)
    (hAssetBound : grossAssets.val ≤ (s.storageMap 7 receiver).val)
    (hGlobalBound : grossAssets.val ≤ (s.storage 0).val)
    (hVaultShares : shares.val ≤ (s.storageMap 5 s.thisAddress).val)
    (hUnpaused : s.storage 3 = 0)
    (hFeeAdd : (s.storage 1 : Nat) + ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256)
    (hFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets (s.storage 1) (1000000000000000000 + s.storage 1) : Nat)) :
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows true false).run
        (s.writeAddrSlot 2 zeroAddress) =
      ContractResult.success ()
        (fulfilledPostState (s.writeAddrSlot 2 zeroAddress) receiver shares grossAssets) := by
  let zeroState := s.writeAddrSlot 2 zeroAddress
  have hZeroVault : (pendingFulfillPostState zeroState receiver shares grossAssets).thisAddress ≠ 0 := by
    simpa [zeroState, pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, ContractState.writeAddrSlot] using hVault
  have hZeroUnpaused : (pendingFulfillPostState zeroState receiver shares grossAssets).storage 3 = 0 := by
    simpa [zeroState, pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, ContractState.writeAddrSlot] using hUnpaused
  have hZeroVaultShares : shares.val ≤
      ((pendingFulfillPostState zeroState receiver shares grossAssets).storageMap 5
        (pendingFulfillPostState zeroState receiver shares grossAssets).thisAddress).val := by
    simpa [zeroState, pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, ContractState.writeAddrSlot] using hVaultShares
  have hZeroFeeAdd :
      ((pendingFulfillPostState zeroState receiver shares grossAssets).storage 1 : Nat) +
        ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [zeroState, pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, ContractState.writeAddrSlot] using hFeeAdd
  have hZeroFeeSub : ¬grossAssets.val <
      (mulDiv512Up grossAssets ((pendingFulfillPostState zeroState receiver shares grossAssets).storage 1)
        (1000000000000000000 +
          (pendingFulfillPostState zeroState receiver shares grossAssets).storage 1) : Nat) := by
    simpa [zeroState, pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, ContractState.writeAddrSlot] using hFeeSub
  have hZeroRecipient :
      (pendingFulfillPostState zeroState receiver shares grossAssets).storageAddr 2 = zeroAddress := by
    simp [zeroState, pendingFulfillPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, ContractState.writeAddrSlot]
  have hWithdraw : YoAsyncRedemptionEscrow._withdraw receiver
      (pendingFulfillPostState zeroState receiver shares grossAssets).thisAddress grossAssets shares true false
      (pendingFulfillPostState zeroState receiver shares grossAssets) =
        ContractResult.success ()
          (burnPostState (pendingFulfillPostState zeroState receiver shares grossAssets) shares) :=
    withdraw_apply_zero_fee_recipient (pendingFulfillPostState zeroState receiver shares grossAssets)
      receiver shares grossAssets hZeroVault hZeroUnpaused hZeroVaultShares hZeroFeeAdd hZeroFeeSub
      hZeroRecipient
  have hRaw := fulfillRedeem_apply_authorized_of_withdraw receiver shares grossAssets zeroState authorityAllows
    true false (ContractResult.success ()
      (burnPostState (pendingFulfillPostState zeroState receiver shares grossAssets) shares))
    (by simpa [zeroState] using hAuthorized)
    (by simpa [zeroState, ContractState.writeAddrSlot] using hPendingShares)
    (by simpa [zeroState, ContractState.writeAddrSlot] using hPendingAssets)
    (by simpa [zeroState, ContractState.writeAddrSlot] using hShareBound)
    (by simpa [zeroState, ContractState.writeAddrSlot] using hAssetBound)
    (by simpa [zeroState, ContractState.writeAddrSlot] using hGlobalBound) hWithdraw
  change (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true authorityAllows true false).run
      zeroState = ContractResult.success ()
        (fulfilledPostState zeroState receiver shares grossAssets)
  unfold Contract.run
  rw [hRaw]
  rfl

/-- Queue `(100,200)`, owner-update the fee, then fulfill under zero-recipient
    and receiver-equals-fee-recipient configurations. The flags are trusted ECM
    outcome/revert abstractions, so no external token balance delta is claimed. -/
theorem fee_aliasing
    (receiver owner : Address) (newFee : Uint256) (s : ContractState)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hStoredOwner : ownerOf s = owner)
    (hNoAuthority : authorityOf s = zeroAddress)
    (hUnpaused : pausedOf s = 0)
    (hInitialPendingShares : pendingSharesOf s receiver = 0)
    (hInitialPendingAssets : pendingAssetsOf s receiver = 0)
    (hInitialPendingTotal : totalPendingAssetsOf s = 0)
    (hOwnerShares : shareBalanceOf s owner >= 100)
    (hErc20 : erc20WellFormed s)
    (hNewFeePositive : newFee > 0)
    (hNewFeeBound : newFee < maxFee)
    (hFeeChanged : feeOnWithdrawOf s != newFee)
    (hNewFeeDivisor : checkedAddFits newFee feeDenominator)
    (hPositiveNewFeeAmount : feeAmountWith 200 newFee > 0)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    fee_aliasing_spec receiver owner newFee s := by
  let q := queuedPostState s 100 200 receiver owner
  let feeState := q.writeSlot 1 newFee
  let zeroRecipientState := feeState.writeAddrSlot 2 zeroAddress
  let aliasRecipientState := feeState.writeAddrSlot 2 receiver
  let zeroFulfilled := fulfilledPostState zeroRecipientState receiver 100 200
  let aliasFulfilled := fulfilledPostState aliasRecipientState receiver 100 200
  have hVaultSlot : s.thisAddress ≠ 0 := by
    simpa [vaultAddress, zeroAddress] using
      (show vaultAddress s ≠ zeroAddress by simpa using hVault)
  have hReceiverSlot : receiver ≠ 0 := by
    simpa [zeroAddress] using (show receiver ≠ zeroAddress by simpa using hReceiver)
  have hOwnerSlot : owner ≠ 0 := by
    simpa [zeroAddress] using (show owner ≠ zeroAddress by simpa using hOwner)
  have hOwnerNotVaultSlot : owner ≠ s.thisAddress := by
    simpa [vaultAddress] using hOwnerNotVault
  have hSenderOwner : s.sender = s.storageAddr 8 := by
    simpa [ownerOf] using hOwnerIsSender.symm.trans hStoredOwner.symm
  have hNoAuthoritySlot : s.storageAddr 9 = 0 := by
    simpa [authorityOf, zeroAddress] using hNoAuthority
  have hUnpausedSlot : s.storage 3 = 0 := by
    simpa [pausedOf] using hUnpaused
  have hInitialShares : s.storageMap 6 receiver = 0 := by
    simpa [pendingSharesOf] using hInitialPendingShares
  have hInitialAssets : s.storageMap 7 receiver = 0 := by
    simpa [pendingAssetsOf] using hInitialPendingAssets
  have hInitialTotal : s.storage 0 = 0 := by
    simpa [totalPendingAssetsOf] using hInitialPendingTotal
  have hOwnerBalance : (100 : Uint256).val ≤ (s.storageMap 5 owner).val := by
    simpa [shareBalanceOf] using hOwnerShares
  have hQueueRun :
      (YoAsyncRedemptionEscrow.requestRedeem 100 receiver owner 200 0
        true true true true).run s = ContractResult.success 0 q := by
    apply requestRedeem_queued_run 100 200 0 receiver owner s hVaultSlot hOwnerSlot hReceiverSlot
      hOwnerNotVaultSlot hOwnerIsSender hUnpausedSlot (by native_decide) hOwnerBalance
    · rw [hInitialTotal]
      native_decide
    · rw [hInitialTotal]
      native_decide
    · rw [hInitialShares]
      native_decide
    · rw [hInitialAssets]
      native_decide
  have hQNoAuthority : q.storageAddr 9 = 0 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hNoAuthoritySlot
  have hQSenderOwner : q.sender = q.storageAddr 8 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hSenderOwner
  have hQAuthorized := isAuthorized_no_authority_owner_apply q hQNoAuthority hQSenderOwner
  have hQVault : q.thisAddress ≠ 0 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hVaultSlot
  have hQUnpaused : q.storage 3 = 0 := by
    simpa [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap]
      using hUnpausedSlot
  have hQShares : q.storageMap 6 receiver = 100 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hInitialShares]
    exact Verity.Core.Uint256.zero_add 100
  have hQAssets : q.storageMap 7 receiver = 200 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hInitialAssets]
    exact Verity.Core.Uint256.zero_add 200
  have hQTotal : q.storage 0 = 200 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hInitialTotal]
    exact Verity.Core.Uint256.zero_add 200
  have hVaultPlusFit : (s.storageMap 5 s.thisAddress : Nat) + (100 : Nat) ≤ MAX_UINT256 := by
    have hVaultNotOwner : (s.thisAddress != owner) = true := by
      simpa [BEq.beq] using (Ne.symm hOwnerNotVaultSlot)
    have hBound : (s.storageMap 5 s.thisAddress : Nat) + (s.storageMap 5 owner : Nat) ≤
        (s.storage 4 : Nat) := by
      simpa [shareBalanceOf, totalSupplyOf] using
        hErc20.2 s.thisAddress owner hVaultNotOwner
    have hSupplyMax : (s.storage 4 : Nat) ≤ MAX_UINT256 := Verity.Core.Uint256.val_le_max _
    change (s.storageMap 5 s.thisAddress : Nat) + (100 : Nat) ≤ MAX_UINT256
    have hOwnerNat : (100 : Nat) ≤ (s.storageMap 5 owner : Nat) := hOwnerBalance
    omega
  have hVaultPlusVal : (add (s.storageMap 5 s.thisAddress) 100 : Nat) =
      (s.storageMap 5 s.thisAddress : Nat) + (100 : Nat) := by
    exact Verity.Core.Uint256.add_eq_of_lt
      (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _ hVaultPlusFit)
  have hQVaultBase : q.storageMap 5 q.thisAddress = add (s.storageMap 5 s.thisAddress) 100 := by
    simp [q, queuedPostState, mapWriteState, ContractState.writeSlot, ContractState.writeMap,
      hOwnerNotVaultSlot]
  have hQVaultShares : (100 : Uint256).val ≤ (q.storageMap 5 q.thisAddress).val := by
    rw [hQVaultBase]
    change (100 : Nat) ≤ (add (s.storageMap 5 s.thisAddress) 100 : Nat)
    rw [hVaultPlusVal]
    omega
  have hFeeUpdate := updateWithdrawFee_run_authorized newFee q hQAuthorized hNewFeeBound
  have hFeeNoAuthority : feeState.storageAddr 9 = 0 := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hNoAuthoritySlot
  have hFeeSenderOwner : feeState.sender = feeState.storageAddr 8 := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hSenderOwner
  have hFeeAuthorized := isAuthorized_no_authority_owner_apply feeState hFeeNoAuthority hFeeSenderOwner
  have hZeroRecipientUpdate :=
    updateFeeRecipient_run_authorized zeroAddress feeState hFeeAuthorized
  have hAliasRecipientUpdate :=
    updateFeeRecipient_run_authorized receiver feeState hFeeAuthorized
  have hFeeUpdateState :
      (YoAsyncRedemptionEscrow.updateWithdrawFee newFee true false).run q =
        ContractResult.success () feeState := by
    simpa [feeState] using hFeeUpdate
  have hZeroRecipientUpdateState :
      (YoAsyncRedemptionEscrow.updateFeeRecipient zeroAddress true false).run feeState =
        ContractResult.success () zeroRecipientState := by
    simpa [zeroRecipientState] using hZeroRecipientUpdate
  have hZeroRecipientUpdateZero :
      (YoAsyncRedemptionEscrow.updateFeeRecipient 0 true false).run feeState =
        ContractResult.success () zeroRecipientState := by
    simpa [zeroAddress] using hZeroRecipientUpdateState
  have hAliasRecipientUpdateState :
      (YoAsyncRedemptionEscrow.updateFeeRecipient receiver true false).run feeState =
        ContractResult.success () aliasRecipientState := by
    simpa [aliasRecipientState] using hAliasRecipientUpdate
  have hFeeVault : feeState.thisAddress ≠ 0 := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hVaultSlot
  have hFeeUnpaused : feeState.storage 3 = 0 := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap] using hUnpausedSlot
  have hFeeShares : feeState.storageMap 6 receiver = 100 := by
    simpa [feeState] using hQShares
  have hFeeAssets : feeState.storageMap 7 receiver = 200 := by
    simpa [feeState] using hQAssets
  have hFeeTotal : feeState.storage 0 = 200 := by
    simpa [feeState] using hQTotal
  have hFeeVaultShares : (100 : Uint256).val ≤
      (feeState.storageMap 5 feeState.thisAddress).val := by
    simpa [feeState] using hQVaultShares
  have hFeeAdd : (feeState.storage 1 : Nat) +
      ((1000000000000000000 : Uint256) : Nat) ≤ MAX_UINT256 := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, feeDenominator, checkedAddFits] using hNewFeeDivisor
  have hFeeBound :
      (mulDiv512Up 200 (feeState.storage 1) (add (feeState.storage 1) feeDenominator) : Nat) ≤
        (200 : Uint256).val := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, feeAmountWith] using
      mulDiv512Up_le_left_of_right_lt 200 newFee (add newFee feeDenominator) (by
        have hDenominatorPos : 0 < (feeDenominator : Nat) := by native_decide
        have hAddVal : (add newFee feeDenominator : Nat) = newFee.val + feeDenominator.val := by
          exact Verity.Core.Uint256.add_eq_of_lt
            (Verity.Proofs.Stdlib.Automation.lt_modulus_of_le_max_uint256 _
              (by simpa [checkedAddFits] using hNewFeeDivisor))
        rw [hAddVal]
        omega)
  have hFeeSub : ¬(200 : Uint256).val <
      (mulDiv512Up 200 (feeState.storage 1)
        (1000000000000000000 + feeState.storage 1) : Nat) := by
    rw [show (1000000000000000000 : Uint256) + feeState.storage 1 =
      add (feeState.storage 1) feeDenominator by
      change (1000000000000000000 : Uint256) + feeState.storage 1 =
        feeState.storage 1 + (1000000000000000000 : Uint256)
      exact (Verity.Core.Uint256.add_comm _ _).symm]
    exact Nat.not_lt_of_ge hFeeBound
  have hFeePositive : 0 <
      (mulDiv512Up 200 (feeState.storage 1)
        (feeState.storage 1 + 1000000000000000000) : Nat) := by
    simpa [feeState, q, queuedPostState, mapWriteState, ContractState.writeSlot,
      ContractState.writeMap, feeAmountWith] using hPositiveNewFeeAmount
  have hZeroNoAuthority : zeroRecipientState.storageAddr 9 = 0 := by
    simpa [zeroRecipientState] using hFeeNoAuthority
  have hZeroSenderOwner : zeroRecipientState.sender = zeroRecipientState.storageAddr 8 := by
    simpa [zeroRecipientState] using hFeeSenderOwner
  have hZeroAuthorized :=
    isAuthorized_no_authority_owner_apply zeroRecipientState hZeroNoAuthority hZeroSenderOwner
  have hZeroAuthorizedBase :
      YoAsyncRedemptionEscrow.isAuthorized true false (feeState.writeAddrSlot 2 zeroAddress) =
        ContractResult.success true (feeState.writeAddrSlot 2 zeroAddress) := by
    simpa [zeroRecipientState] using hZeroAuthorized
  have hAliasNoAuthority : aliasRecipientState.storageAddr 9 = 0 := by
    simpa [aliasRecipientState] using hFeeNoAuthority
  have hAliasSenderOwner : aliasRecipientState.sender = aliasRecipientState.storageAddr 8 := by
    simpa [aliasRecipientState] using hFeeSenderOwner
  have hAliasAuthorized :=
    isAuthorized_no_authority_owner_apply aliasRecipientState hAliasNoAuthority hAliasSenderOwner
  have hZeroAssets : zeroRecipientState.storageMap 7 receiver = 200 := by
    simpa [zeroRecipientState] using hFeeAssets
  have hAliasAssets : aliasRecipientState.storageMap 7 receiver = 200 := by
    simpa [aliasRecipientState] using hFeeAssets
  have hZeroFulfill :
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true false).run
        zeroRecipientState = ContractResult.success () zeroFulfilled := by
    change (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true false).run
      (feeState.writeAddrSlot 2 zeroAddress) = ContractResult.success ()
        (fulfilledPostState (feeState.writeAddrSlot 2 zeroAddress) receiver 100 200)
    exact fulfillRedeem_run_authorized_no_authority_zero_recipient receiver 100 200 feeState false
      hZeroAuthorizedBase hFeeVault
      (show feeState.storageMap 6 receiver ≠ 0 by rw [hFeeShares]; native_decide)
      (show feeState.storageMap 7 receiver ≠ 0 by rw [hFeeAssets]; native_decide)
      (by rw [hFeeShares]) (by rw [hFeeAssets]) (by rw [hFeeTotal]) hFeeVaultShares
      hFeeUnpaused hFeeAdd hFeeSub
  have hAliasFulfill :
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true true).run
        aliasRecipientState = ContractResult.success () aliasFulfilled := by
    change (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true true).run
      aliasRecipientState = ContractResult.success ()
        (fulfilledPostState aliasRecipientState receiver 100 200)
    apply fulfillRedeem_run_authorized_no_authority receiver 100 200 aliasRecipientState false
      hAliasAuthorized
    · simpa [aliasRecipientState] using hFeeVault
    · simpa [aliasRecipientState] using (show feeState.storageMap 6 receiver ≠ 0 by
        rw [hFeeShares]; native_decide)
    · simpa [aliasRecipientState] using (show feeState.storageMap 7 receiver ≠ 0 by
        rw [hFeeAssets]; native_decide)
    · simpa [aliasRecipientState, hFeeShares]
    · simpa [aliasRecipientState, hFeeAssets]
    · simpa [aliasRecipientState, hFeeTotal]
    · simpa [aliasRecipientState] using hFeeVaultShares
    · simpa [aliasRecipientState] using hFeeUnpaused
    · simpa [aliasRecipientState] using hFeeAdd
    · simpa [aliasRecipientState] using hFeeSub
  have hAliasRecipient : aliasRecipientState.storageAddr 2 ≠ 0 := by
    simpa [aliasRecipientState, zeroAddress] using hReceiverSlot
  have hAliasFeeFailure :=
    fulfillRedeem_run_authorized_fee_revert receiver 100 200 aliasRecipientState false
      hAliasAuthorized hAliasNoAuthority
      (by simpa [aliasRecipientState] using hFeeVault)
      (by simpa [aliasRecipientState] using (show feeState.storageMap 6 receiver ≠ 0 by
        rw [hFeeShares]; native_decide))
      (by simpa [aliasRecipientState] using (show feeState.storageMap 7 receiver ≠ 0 by
        rw [hFeeAssets]; native_decide))
      (by simpa [aliasRecipientState, hFeeShares])
      (by simpa [aliasRecipientState, hFeeAssets])
      (by simpa [aliasRecipientState, hFeeTotal])
      (by simpa [aliasRecipientState] using hFeeVaultShares)
      (by simpa [aliasRecipientState] using hFeeUnpaused)
      (by simpa [aliasRecipientState] using hFeeAdd)
      (by simpa [aliasRecipientState] using hFeeSub)
      (by simpa [aliasRecipientState] using hFeePositive)
      hAliasRecipient
  unfold fee_aliasing_spec
  dsimp
  rw [hQueueRun]
  simp only [ContractResult.snd_success]
  rw [hFeeUpdateState]
  simp only [ContractResult.snd_success]
  rw [hZeroRecipientUpdateZero]
  simp only [ContractResult.snd_success]
  rw [hAliasRecipientUpdateState]
  simp only [ContractResult.snd_success]
  rw [hZeroFulfill, hAliasFulfill, hAliasFeeFailure]
  refine ⟨zeroFulfilled, aliasFulfilled, True.intro, True.intro, True.intro, True.intro, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, rfl⟩
  · simp [feeOnWithdrawOf, feeState]
  · simp [feeOnWithdrawOf, zeroRecipientState, feeState]
  · simp [feeOnWithdrawOf, aliasRecipientState, feeState]
  · simp [feeRecipientOf, zeroRecipientState, feeState]
  · simp [feeRecipientOf, aliasRecipientState, feeState]
  · simp [feeAmountOf, feeAmountWith, feeOnWithdrawOf, zeroRecipientState, feeState]
  · simp [feeAmountOf, feeAmountWith, feeOnWithdrawOf, aliasRecipientState, feeState]
  · simp [zeroFulfilled, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hZeroAssets, uint_sub_self]
  · simp [aliasFulfilled, fulfilledPostState, burnPostState, pendingFulfillPostState, mapWriteState,
      ContractState.writeSlot, ContractState.writeMap, pendingAssetsOf, hAliasAssets, uint_sub_self]

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
