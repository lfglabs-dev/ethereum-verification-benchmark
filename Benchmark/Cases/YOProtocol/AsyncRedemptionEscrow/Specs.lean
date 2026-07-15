import Verity.Specs.Common
import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Contract

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-! ## Article-readable state accessors and assumptions -/

def totalPendingAssetsOf (s : ContractState) : Uint256 := s.storage 0
def feeOnWithdrawOf (s : ContractState) : Uint256 := s.storage 1
def feeRecipientOf (s : ContractState) : Address := s.storageAddr 2
def pausedOf (s : ContractState) : Uint256 := s.storage 3
def totalSupplyOf (s : ContractState) : Uint256 := s.storage 4
def shareBalanceOf (s : ContractState) (account : Address) : Uint256 := s.storageMap 5 account
def pendingSharesOf (s : ContractState) (receiver : Address) : Uint256 := s.storageMap 6 receiver
def pendingAssetsOf (s : ContractState) (receiver : Address) : Uint256 := s.storageMap 7 receiver
def ownerOf (s : ContractState) : Address := s.storageAddr 8
def authorityOf (s : ContractState) : Address := s.storageAddr 9
def underlyingTokenOf (s : ContractState) : Address := s.storageAddr 10
def vaultAddress (s : ContractState) : Address := s.thisAddress

/-- Source `_getAvailableBalance` evaluated from the successful external
    `balanceOf` snapshot supplied to the call. -/
def availableUnderlyingOf (s : ContractState) (externalUnderlyingBalance : Uint256) : Uint256 :=
  if externalUnderlyingBalance > totalPendingAssetsOf s then
    sub externalUnderlyingBalance (totalPendingAssetsOf s)
  else
    0

/-- A Solidity checked addition is available at this explicit boundary. -/
def checkedAddFits (x y : Uint256) : Prop :=
  (x : Nat) + (y : Nat) <= MAX_UINT256

/-- The source's `feeBasisPoints + DENOMINATOR` checked addition fits. -/
def feeDivisorFits (s : ContractState) : Prop :=
  checkedAddFits (feeOnWithdrawOf s) feeDenominator

/-- Current `_feeOnTotal(gross, feeOnWithdraw)`. -/
def feeAmountWith (grossAssets fee : Uint256) : Uint256 :=
  mulDiv512Up grossAssets fee (add fee feeDenominator)

def feeAmountOf (s : ContractState) (grossAssets : Uint256) : Uint256 :=
  feeAmountWith grossAssets (feeOnWithdrawOf s)

/-- Fee-exclusive amount handed to ERC4626's receiver SafeERC20 transfer. -/
def netAssetsOf (s : ContractState) (grossAssets : Uint256) : Uint256 :=
  sub grossAssets (feeAmountOf s grossAssets)

/-- The local two-account consequence of the inherited ERC-20 invariant.

    OpenZeppelin's `_update` uses unchecked supply subtraction and recipient
    addition because a well-formed ERC-20 state has aggregate balances bounded
    by supply.  The modeled mapping is intentionally unbounded, so theorem
    interfaces state exactly the two-account consequence needed by a selected
    movement.  It implies `toBalance + amount <= totalSupply <= MAX_UINT256`
    whenever `amount <= fromBalance` and `from != to`; it also gives the burn
    supply bound.  This is a theorem hypothesis, never a runtime supply guard. -/
def erc20WellFormed (s : ContractState) : Prop :=
  (∀ account, shareBalanceOf s account <= totalSupplyOf s) ∧
  (∀ fromAddr toAddr,
    fromAddr != toAddr →
    (shareBalanceOf s fromAddr : Nat) + (shareBalanceOf s toAddr : Nat) <=
      (totalSupplyOf s : Nat))

/-- Equality of EVM-observable local storage channels. `knownAddresses` is
    verifier bookkeeping for mapping sums, not EVM storage, so source no-ops
    intentionally do not require whole `ContractState` equality. -/
def evmObservableStorageEq (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap ∧
  s'.storageMapUint = s.storageMapUint ∧
  s'.storageMap2 = s.storageMap2 ∧
  s'.storageArray = s.storageArray

def pausedStateOf (s : ContractState) : ContractState :=
  Verity.ContractState.writeSlot s 3 1

/-! ## Phase-3 theorem interfaces

Every successful transition below names a successful `ContractResult`, rather
than observing `.snd` alone.  `previewSucceeds`, `balanceReadSucceeds`, and
the transfer flags are trusted outcome/revert abstractions at external-call
boundaries.  They do not assert executable ERC-20 token semantics or external
token-balance deltas.  The case assumes no authority/token callback mutates any
modeled vault storage during such a boundary; for the pinned deployment the
underlying USDC address is also distinct from the vault address.
-/

/-- A successful request takes the exact source instant or queued branch. -/
def request_redeem_branching_spec
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  ∃ s',
    result = ContractResult.success
      (if availableUnderlyingOf s externalUnderlyingBalance >= grossAssets then grossAssets else 0) s' ∧
    if availableUnderlyingOf s externalUnderlyingBalance >= grossAssets then
      pendingSharesOf s' receiver = pendingSharesOf s receiver ∧
      pendingAssetsOf s' receiver = pendingAssetsOf s receiver ∧
      totalPendingAssetsOf s' = totalPendingAssetsOf s ∧
      shareBalanceOf s' owner = sub (shareBalanceOf s owner) shares ∧
      totalSupplyOf s' = sub (totalSupplyOf s) shares
    else
      totalSupplyOf s' = totalSupplyOf s ∧
      pendingSharesOf s' receiver = add (pendingSharesOf s receiver) shares ∧
      pendingAssetsOf s' receiver = add (pendingAssetsOf s receiver) grossAssets ∧
      totalPendingAssetsOf s' = add (totalPendingAssetsOf s) grossAssets

/-- A successful queued request pools shares and aggregates the receiver key. -/
def queued_request_aggregation_spec
    (shares grossAssets : Uint256) (receiver owner : Address)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  ∃ s',
    result = ContractResult.success 0 s' ∧
    pendingSharesOf s' receiver = add (pendingSharesOf s receiver) shares ∧
    pendingAssetsOf s' receiver = add (pendingAssetsOf s receiver) grossAssets ∧
    totalPendingAssetsOf s' = add (totalPendingAssetsOf s) grossAssets ∧
    totalSupplyOf s' = totalSupplyOf s ∧
    (owner != vaultAddress s →
      shareBalanceOf s' owner = sub (shareBalanceOf s owner) shares ∧
      shareBalanceOf s' (vaultAddress s) = add (shareBalanceOf s (vaultAddress s)) shares)

/-- Two successful, sender-specific queue calls aggregate to one receiver. -/
def two_owner_queue_aggregation_spec
    (firstShares firstGross secondShares secondGross : Uint256)
    (firstOwner secondOwner receiver : Address) (s : ContractState) : Prop :=
  let firstState := { s with sender := firstOwner }
  let first :=
    (YoAsyncRedemptionEscrow.requestRedeem firstShares receiver firstOwner firstGross 0
      true true true true).run firstState
  let afterFirst := first.snd
  let secondState := { afterFirst with sender := secondOwner }
  let second :=
    (YoAsyncRedemptionEscrow.requestRedeem secondShares receiver secondOwner secondGross 0
      true true true true).run secondState
  let afterSecond := second.snd
  first = ContractResult.success 0 afterFirst ∧
  second = ContractResult.success 0 afterSecond ∧
  pendingSharesOf afterSecond receiver =
    add (add (pendingSharesOf s receiver) firstShares) secondShares ∧
  pendingAssetsOf afterSecond receiver =
    add (add (pendingAssetsOf s receiver) firstGross) secondGross ∧
  totalPendingAssetsOf afterSecond =
    add (add (totalPendingAssetsOf s) firstGross) secondGross

/-- Successful fulfillment performs exact independent component decrements and
    burns pooled shares. Gross pending assets remain distinct from net/fee
    transfer units. -/
def fulfill_redeem_accounting_spec
    (shares grossAssets : Uint256) (receiver : Address)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  ∃ s',
    result = ContractResult.success () s' ∧
    shares <= pendingSharesOf s receiver ∧
    grossAssets <= pendingAssetsOf s receiver ∧
    pendingSharesOf s receiver != 0 ∧
    pendingAssetsOf s receiver != 0 ∧
    pendingSharesOf s' receiver = sub (pendingSharesOf s receiver) shares ∧
    pendingAssetsOf s' receiver = sub (pendingAssetsOf s receiver) grossAssets ∧
    totalPendingAssetsOf s' = sub (totalPendingAssetsOf s) grossAssets ∧
    shareBalanceOf s' (vaultAddress s) = sub (shareBalanceOf s (vaultAddress s)) shares ∧
    totalSupplyOf s' = sub (totalSupplyOf s) shares ∧
    grossAssets = add (netAssetsOf s grossAssets) (feeAmountOf s grossAssets)

/-- Successful cancellation has identical pending decrements and transfers
    pooled shares to the receiver. The vault self-transfer has no net balance
    delta. -/
def cancel_redeem_accounting_spec
    (shares grossAssets : Uint256) (receiver : Address)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  ∃ s',
    result = ContractResult.success () s' ∧
    shares <= pendingSharesOf s receiver ∧
    grossAssets <= pendingAssetsOf s receiver ∧
    pendingSharesOf s receiver != 0 ∧
    pendingAssetsOf s receiver != 0 ∧
    pendingSharesOf s' receiver = sub (pendingSharesOf s receiver) shares ∧
    pendingAssetsOf s' receiver = sub (pendingAssetsOf s receiver) grossAssets ∧
    totalPendingAssetsOf s' = sub (totalPendingAssetsOf s) grossAssets ∧
    totalSupplyOf s' = totalSupplyOf s ∧
    (receiver = vaultAddress s →
      shareBalanceOf s' (vaultAddress s) = shareBalanceOf s (vaultAddress s)) ∧
    (receiver != vaultAddress s →
      shareBalanceOf s' (vaultAddress s) = sub (shareBalanceOf s (vaultAddress s)) shares ∧
      shareBalanceOf s' receiver = add (shareBalanceOf s receiver) shares)

/-- Successful fulfillment directly changes only its selected receiver record
    and the matching global gross counter under the explicit external-state
    non-mutation assumption documented above. -/
def lifecycle_bounds_and_isolation_spec
    (shares grossAssets : Uint256) (receiver other : Address)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  ∃ s',
    result = ContractResult.success () s' ∧
    shares <= pendingSharesOf s receiver ∧
    grossAssets <= pendingAssetsOf s receiver ∧
    pendingSharesOf s' receiver = sub (pendingSharesOf s receiver) shares ∧
    pendingAssetsOf s' receiver = sub (pendingAssetsOf s receiver) grossAssets ∧
    totalPendingAssetsOf s' = sub (totalPendingAssetsOf s) grossAssets ∧
    (receiver != other →
      pendingSharesOf s' other = pendingSharesOf s other ∧
      pendingAssetsOf s' other = pendingAssetsOf s other)

/-- `(0,0)` settlement calls are source-permitted from a two-sided record.
    They succeed and leave EVM-observable storage/mappings unchanged; Verity's
    internal `knownAddresses` bookkeeping may grow because mapping writes occur. -/
def zero_component_lifecycle_spec (receiver : Address) (s : ContractState) : Prop :=
  let fulfilled :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 0 true true true true).run s
  let cancelled :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run s
  ∃ fulfilledState cancelledState,
    fulfilled = ContractResult.success () fulfilledState ∧
    cancelled = ContractResult.success () cancelledState ∧
    evmObservableStorageEq s fulfilledState ∧
    evmObservableStorageEq s cancelledState

/-- One-sided records are constructed by source-permitted zero-component
    settlements from an actual queued pair, not assumed arbitrarily. Both are
    dormant, and a positive same-receiver queue repairs either direction. -/
def malformed_pair_lifecycle_spec
    (receiver owner repairOwner : Address)
    (queuedShares queuedGross repairShares repairGross : Uint256)
    (s : ContractState) : Prop :=
  let queueState := { s with sender := owner }
  let queued :=
    (YoAsyncRedemptionEscrow.requestRedeem queuedShares receiver owner queuedGross 0
      true true true true).run queueState
  let q := queued.snd
  let shareOnly :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 queuedGross true true true true).run q
  let assetOnly :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver queuedShares 0 true true).run q
  let shareOnlyState := shareOnly.snd
  let assetOnlyState := assetOnly.snd
  let shareOnlyFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 0 true true true true).run shareOnlyState
  let shareOnlyCancel :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run shareOnlyState
  let assetOnlyFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 0 true true true true).run assetOnlyState
  let assetOnlyCancel :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run assetOnlyState
  let repairShareState := { shareOnlyState with sender := repairOwner }
  let repairedShareOnly :=
    (YoAsyncRedemptionEscrow.requestRedeem repairShares receiver repairOwner repairGross 0
      true true true true).run repairShareState
  let repairAssetState := { assetOnlyState with sender := repairOwner }
  let repairedAssetOnly :=
    (YoAsyncRedemptionEscrow.requestRedeem repairShares receiver repairOwner repairGross 0
      true true true true).run repairAssetState
  ∃ repairedShareState' repairedAssetState',
    queued = ContractResult.success 0 q ∧
    shareOnly = ContractResult.success () shareOnlyState ∧
    assetOnly = ContractResult.success () assetOnlyState ∧
    pendingSharesOf shareOnlyState receiver = queuedShares ∧
    pendingAssetsOf shareOnlyState receiver = 0 ∧
    totalPendingAssetsOf shareOnlyState = 0 ∧
    pendingSharesOf assetOnlyState receiver = 0 ∧
    pendingAssetsOf assetOnlyState receiver = queuedGross ∧
    totalPendingAssetsOf assetOnlyState = queuedGross ∧
    shareOnlyFulfill = ContractResult.revert "InvalidAssetsAmount" shareOnlyState ∧
    shareOnlyCancel = ContractResult.revert "InvalidAssetsAmount" shareOnlyState ∧
    assetOnlyFulfill = ContractResult.revert "InvalidSharesAmount" assetOnlyState ∧
    assetOnlyCancel = ContractResult.revert "InvalidSharesAmount" assetOnlyState ∧
    repairedShareOnly = ContractResult.success 0 repairedShareState' ∧
    repairedAssetOnly = ContractResult.success 0 repairedAssetState' ∧
    pendingSharesOf repairedShareState' receiver = add queuedShares repairShares ∧
    pendingAssetsOf repairedShareState' receiver = repairGross ∧
    pendingSharesOf repairedAssetState' receiver = repairShares ∧
    pendingAssetsOf repairedAssetState' receiver = add queuedGross repairGross

/-- A complete nonzero settlement rejects immediate replay, while a later
    queued request recreates the pair and permits identical fulfillment again. -/
def full_clear_requeue_replay_spec
    (receiver requestOwner : Address) (shares grossAssets : Uint256)
    (s : ContractState) : Prop :=
  let settlement :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s
  let cleared := settlement.snd
  let immediateReplay :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run cleared
  let queueState := { cleared with sender := requestOwner }
  let requeue :=
    (YoAsyncRedemptionEscrow.requestRedeem shares receiver requestOwner grossAssets 0
      true true true true).run queueState
  let repopulated := requeue.snd
  let replayAfterRequeue :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run repopulated
  let final := replayAfterRequeue.snd
  settlement = ContractResult.success () cleared ∧
  pendingSharesOf cleared receiver = 0 ∧
  pendingAssetsOf cleared receiver = 0 ∧
  immediateReplay = ContractResult.revert "InvalidSharesAmount" cleared ∧
  requeue = ContractResult.success 0 repopulated ∧
  pendingSharesOf repopulated receiver = shares ∧
  pendingAssetsOf repopulated receiver = grossAssets ∧
  replayAfterRequeue = ContractResult.success () final ∧
  pendingSharesOf final receiver = 0 ∧
  pendingAssetsOf final receiver = 0

/-- Revert cases are constructed so their named guard/boundary is reached:
    authority call, pause inside `_update`, receiver transfer, and conditional
    second fee transfer. Every failure is observed at `Contract.run`. -/
def lifecycle_rollback_spec
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState) : Prop :=
  let authFailedFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets false false true true).run s
  let authFailedCancel :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets false false).run s
  let pausedState := pausedStateOf s
  let pausedFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run pausedState
  let pausedCancel :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver shares grossAssets true true).run pausedState
  let receiverTransferFailed :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true false true).run s
  let feeTransferFailed :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true false).run s
  authFailedFulfill = ContractResult.revert "AuthorityCanCallReverted" s ∧
  authFailedCancel = ContractResult.revert "AuthorityCanCallReverted" s ∧
  pausedFulfill = ContractResult.revert "EnforcedPause" pausedState ∧
  pausedCancel = ContractResult.revert "EnforcedPause" pausedState ∧
  receiverTransferFailed = ContractResult.revert "SafeERC20FailedOperation" s ∧
  feeTransferFailed = ContractResult.revert "SafeERC20FailedOperation" s

/-- Queue a concrete positive pair, change the current source fee through its
    owner-authorized setters, then fulfill from both fee-recipient branches.
    `receiver == feeRecipient` is covered without claiming external balances. -/
def fee_aliasing_spec
    (receiver owner : Address) (newFee : Uint256) (s : ContractState) : Prop :=
  let queued :=
    (YoAsyncRedemptionEscrow.requestRedeem 100 receiver owner 200 0 true true true true).run s
  let q := queued.snd
  let feeUpdated :=
    (YoAsyncRedemptionEscrow.updateWithdrawFee newFee true false).run q
  let feeState := feeUpdated.snd
  let zeroRecipient :=
    (YoAsyncRedemptionEscrow.updateFeeRecipient zeroAddress true false).run feeState
  let zeroRecipientState := zeroRecipient.snd
  let aliasRecipient :=
    (YoAsyncRedemptionEscrow.updateFeeRecipient receiver true false).run feeState
  let aliasRecipientState := aliasRecipient.snd
  let zeroRecipientFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true false).run zeroRecipientState
  let aliasFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true true).run aliasRecipientState
  let aliasFeeFailure :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 200 true false true false).run aliasRecipientState
  ∃ zeroFulfilled aliasFulfilled,
    queued = ContractResult.success 0 q ∧
    feeUpdated = ContractResult.success () feeState ∧
    zeroRecipient = ContractResult.success () zeroRecipientState ∧
    aliasRecipient = ContractResult.success () aliasRecipientState ∧
    feeOnWithdrawOf feeState = newFee ∧
    feeOnWithdrawOf zeroRecipientState = newFee ∧
    feeOnWithdrawOf aliasRecipientState = newFee ∧
    feeRecipientOf zeroRecipientState = zeroAddress ∧
    feeRecipientOf aliasRecipientState = receiver ∧
    feeAmountOf zeroRecipientState 200 = feeAmountWith 200 newFee ∧
    feeAmountOf aliasRecipientState 200 = feeAmountWith 200 newFee ∧
    zeroRecipientFulfill = ContractResult.success () zeroFulfilled ∧
    aliasFulfill = ContractResult.success () aliasFulfilled ∧
    pendingAssetsOf zeroFulfilled receiver = 0 ∧
    pendingAssetsOf aliasFulfilled receiver = 0 ∧
    aliasFeeFailure = ContractResult.revert "SafeERC20FailedOperation" aliasRecipientState

/-- Candidate G source-reachability coverage from a positive queued `(100,200)`
    pair: all six zero-component shapes and the accepted positive,
    non-proportional `(1,199)` fulfillment. -/
def candidate_g_source_reachable_spec (receiver owner : Address) (s : ContractState) : Prop :=
  let queued :=
    (YoAsyncRedemptionEscrow.requestRedeem 100 receiver owner 200 0 true true true true).run s
  let q := queued.snd
  let fulfill00 :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 0 true true true true).run q
  let cancel00 :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 0 true true).run q
  let fulfill0Full :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 0 200 true true true true).run q
  let fulfillFull0 :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 100 0 true true true true).run q
  let cancel0Full :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 0 200 true true).run q
  let cancelFull0 :=
    (YoAsyncRedemptionEscrow.cancelRedeem receiver 100 0 true true).run q
  let nonProportional :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver 1 199 true true true true).run q
  let fulfill00State := fulfill00.snd
  let cancel00State := cancel00.snd
  let fulfill0FullState := fulfill0Full.snd
  let fulfillFull0State := fulfillFull0.snd
  let cancel0FullState := cancel0Full.snd
  let cancelFull0State := cancelFull0.snd
  let nonProportionalState := nonProportional.snd
  queued = ContractResult.success 0 q ∧
  fulfill00 = ContractResult.success () fulfill00State ∧
  cancel00 = ContractResult.success () cancel00State ∧
  evmObservableStorageEq q fulfill00State ∧
  evmObservableStorageEq q cancel00State ∧
  fulfill0Full = ContractResult.success () fulfill0FullState ∧
  pendingSharesOf fulfill0FullState receiver = 100 ∧
  pendingAssetsOf fulfill0FullState receiver = 0 ∧
  totalPendingAssetsOf fulfill0FullState = 0 ∧
  fulfillFull0 = ContractResult.success () fulfillFull0State ∧
  pendingSharesOf fulfillFull0State receiver = 0 ∧
  pendingAssetsOf fulfillFull0State receiver = 200 ∧
  totalPendingAssetsOf fulfillFull0State = 200 ∧
  cancel0Full = ContractResult.success () cancel0FullState ∧
  pendingSharesOf cancel0FullState receiver = 100 ∧
  pendingAssetsOf cancel0FullState receiver = 0 ∧
  totalPendingAssetsOf cancel0FullState = 0 ∧
  cancelFull0 = ContractResult.success () cancelFull0State ∧
  pendingSharesOf cancelFull0State receiver = 0 ∧
  pendingAssetsOf cancelFull0State receiver = 200 ∧
  totalPendingAssetsOf cancelFull0State = 200 ∧
  nonProportional = ContractResult.success () nonProportionalState ∧
  pendingSharesOf nonProportionalState receiver = 99 ∧
  pendingAssetsOf nonProportionalState receiver = 1 ∧
  totalPendingAssetsOf nonProportionalState = 1

/-- With a nonzero authority, a successful `false` result falls back to the
    stored owner. A reverting authority call still blocks that same owner. -/
def owner_fallback_authorization_spec
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState) : Prop :=
  let ownerState := { s with sender := ownerOf s }
  let fallbackFulfill :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true false true true).run ownerState
  let fallbackState := fallbackFulfill.snd
  let blockedOwner :=
    (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets false false true true).run ownerState
  fallbackFulfill = ContractResult.success () fallbackState ∧
  pendingSharesOf fallbackState receiver = sub (pendingSharesOf ownerState receiver) shares ∧
  pendingAssetsOf fallbackState receiver = sub (pendingAssetsOf ownerState receiver) grossAssets ∧
  blockedOwner = ContractResult.revert "AuthorityCanCallReverted" ownerState

/-- Public `redeem` retains its wrapper pause guard and otherwise delegates to
    `requestRedeem` with the same successful queued transition. -/
def redeem_wrapper_spec
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (s : ContractState) : Prop :=
  let redeemResult :=
    (YoAsyncRedemptionEscrow.redeem shares receiver owner grossAssets externalUnderlyingBalance
      true true true true).run s
  let directRequest :=
    (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets externalUnderlyingBalance
      true true true true).run s
  let redeemedState := redeemResult.snd
  let pausedState := pausedStateOf s
  let pausedRedeem :=
    (YoAsyncRedemptionEscrow.redeem shares receiver owner grossAssets externalUnderlyingBalance
      true true true true).run pausedState
  redeemResult = ContractResult.success 0 redeemedState ∧
  directRequest = ContractResult.success 0 redeemedState ∧
  pendingSharesOf redeemedState receiver = add (pendingSharesOf s receiver) shares ∧
  pendingAssetsOf redeemedState receiver = add (pendingAssetsOf s receiver) grossAssets ∧
  totalPendingAssetsOf redeemedState = add (totalPendingAssetsOf s) grossAssets ∧
  pausedRedeem = ContractResult.revert "EnforcedPause" pausedState

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
