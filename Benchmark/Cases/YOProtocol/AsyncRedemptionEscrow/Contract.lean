/-
Source-faithful lifecycle slice for YO Protocol async redemption escrow.

Real simplifications and explicit environmental assumptions:

* `super.previewRedeem(shares)` / the YO oracle are represented by the
  `grossAssets` input to `requestRedeem`.  This preserves the gross value that
  the source records, but deliberately does not verify oracle pricing.
* `IERC20(asset()).balanceOf(address(this))` is represented by the
  `externalUnderlyingBalance` input.  The model uses it only for the source's
  instant-versus-queued branch; it does not model the external token's storage.
* `authority.canCall` is represented by selector-specific
  `authorityCallSucceeds` and `authorityAllows` inputs.  This exposes its
  revert boundary and result without embedding the external authority contract.
* Oracle preview, underlying `balanceOf`, authority, and SafeERC20 calls retain
  explicit success/failure inputs.  These inputs are trusted external
  outcome/revert abstractions at the ECM boundary: executable
  `Contracts.safeTransfer` is `pure ()`, so they are not executable token
  semantics.  External token balances, optional-return data, and callbacks are
  not local storage.  The environmental assumption is broader than lifecycle
  reentry: no authority or token callback may mutate *any* modeled vault state
  while one of these calls is in flight (`reentrancy_trusted`).
* Events, allowances (the modeled `_withdraw` callers equal the share owners),
  deposits, mints, unrelated ERC-4626 views, and administration are omitted.
  In particular, lifecycle claims exclude privileged `manage` calls between
  transitions and behavior after a proxy implementation upgrade.

Faithfully represented, rather than simplified: receiver-keyed pending shares
and gross assets, pooled vault shares, supply, pause checks inside share
movement, source guard order, independent fulfillment/cancellation components,
checked Solidity-0.8 pending arithmetic, OpenZeppelin ERC-20 unchecked
movement arithmetic under its well-formed-state invariant, current fee-on-total
rounding, and the zero/nonzero fee-recipient branch.

Upstream: yoprotocol/core-v2@7b023145cc99bc424e57ffa554584c609a1ecb30:
`src/YoVault.sol` (the pinned Base yoUSD implementation inherits this logic).
-/

import Contracts.Common
import Verity.Stdlib.Math

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Contracts

/-- `YoVault.DENOMINATOR`, used by `_feeOnTotal`. -/
def feeDenominator : Uint256 := 1000000000000000000

/-- `YoVault.MAX_FEE`, used by `updateWithdrawFee`. -/
def maxFee : Uint256 := 100000000000000000

verity_contract YoAsyncRedemptionEscrow where
  storage
    -- `YoVault.totalPendingAssets`: gross underlying-asset units.
    totalPendingAssets : Uint256 := slot 0
    -- `YoVault.feeOnWithdraw` and `YoVault.feeRecipient`.
    feeOnWithdraw : Uint256 := slot 1
    feeRecipient : Address := slot 2
    -- `PausableUpgradeable.paused()`: zero means unpaused.
    paused : Uint256 := slot 3
    -- ERC-20 yoVault share accounting.
    totalSupply : Uint256 := slot 4
    shareBalances : Address → Uint256 := slot 5
    -- The two members of `_pendingRedeem[receiver]`, split but keyed alike.
    pendingShares : Address → Uint256 := slot 6
    pendingAssets : Address → Uint256 := slot 7
    -- `AuthUpgradeable` storage.
    owner : Address := slot 8
    authority : Address := slot 9
    -- Identity only: the external underlying token is not local storage.
    underlyingToken : Address := slot 10

  -- `AuthUpgradeable.isAuthorized`.  When authority is nonzero, its call
  -- success is checked before any owner comparison, exactly as Solidity's
  -- `(auth != 0 && auth.canCall(...)) || user == owner` evaluation does.
  function internal isAuthorized
      (authorityCallSucceeds : Bool, authorityAllows : Bool) : Bool := do
    let auth ← getStorageAddr authority
    let sender ← msgSender
    if auth != zeroAddress then
      require authorityCallSucceeds "AuthorityCanCallReverted"
      if authorityAllows then
        return true
      else
        let storedOwner ← getStorageAddr owner
        return sender == storedOwner
    else
      let storedOwner ← getStorageAddr owner
      return sender == storedOwner

  -- Source `_getAvailableBalance`: underlying balance minus gross pending,
  -- clamped to zero.  `externalUnderlyingBalance` is the external `balanceOf`
  -- observation captured at this call boundary.
  function internal _getAvailableBalance
      (externalUnderlyingBalance : Uint256) : Uint256 := do
    let pending ← getStorage totalPendingAssets
    if externalUnderlyingBalance > pending then
      return sub externalUnderlyingBalance pending
    else
      return 0

  -- OpenZeppelin ERC-20 `_update`, including YoVault's override pause guard.
  -- This intentionally uses modular `sub`/`add` after the balance check: OZ
  -- relies on the ERC-20 well-formed-state invariant (`sum balances = supply`)
  -- to justify its unchecked supply subtraction and recipient addition.  The
  -- public theorem interfaces state the local well-formedness consequences
  -- needed by their concrete movements; no source-absent supply guard or
  -- checked recipient addition is introduced here.
  function internal _update (fromAddr : Address, toAddr : Address, shares : Uint256) : Unit := do
    let pausedFlag ← getStorage paused
    require (pausedFlag == 0) "EnforcedPause"
    -- The only callers in this lifecycle slice are `_transfer` and `_burn`,
    -- which have already checked `fromAddr != 0`; minting is out of scope.
    let fromBalance ← getMapping shareBalances fromAddr
    require (fromBalance >= shares) "ERC20InsufficientBalance"
    if toAddr == zeroAddress then
      let supply ← getStorage totalSupply
      setMapping shareBalances fromAddr (sub fromBalance shares)
      setStorage totalSupply (sub supply shares)
    else
      let toBalance ← getMapping shareBalances toAddr
      setMapping shareBalances fromAddr (sub fromBalance shares)
      setMapping shareBalances toAddr (add toBalance shares)

  -- Value-equivalent source `_update` self-transfer path. OZ first subtracts
  -- and then adds back to the same slot; this Verity representation preserves
  -- its externally observable result and guard order without changing only the
  -- verifier's `knownAddresses` bookkeeping.
  function internal _updateSelf (account : Address, shares : Uint256) : Unit := do
    let pausedFlag ← getStorage paused
    require (pausedFlag == 0) "EnforcedPause"
    let balance ← getMapping shareBalances account
    require (balance >= shares) "ERC20InsufficientBalance"
    pure ()

  -- ERC-20 `_transfer`: OZ validates both addresses *before* dispatching to
  -- `_update`, so a zero-address error precedes YoVault's pause guard.
  function internal _transfer (fromAddr : Address, toAddr : Address, shares : Uint256) : Unit := do
    require (fromAddr != zeroAddress) "ERC20InvalidSender"
    require (toAddr != zeroAddress) "ERC20InvalidReceiver"
    if fromAddr == toAddr then
      _updateSelf fromAddr shares
    else
      _update fromAddr toAddr shares

  -- ERC-20 `_burn`: OZ validates `account` before dispatching to `_update`,
  -- then `_update` reaches YoVault's pause guard and uses unchecked supply
  -- arithmetic under the ERC-20 invariant.
  function internal _burn (fromAddr : Address, shares : Uint256) : Unit := do
    require (fromAddr != zeroAddress) "ERC20InvalidSender"
    _update fromAddr zeroAddress shares

  -- YO's `_withdraw` override.  It distinguishes the gross pending unit,
  -- current-fee amount, and net receiver-transfer unit.  A failed modeled
  -- SafeERC20 transfer reverts, so `Contract.run` exposes whole-call rollback.
  function internal _withdraw
      (receiver : Address, owner : Address, grossAssets : Uint256, shares : Uint256,
       receiverTransferSucceeds : Bool, feeTransferSucceeds : Bool) : Unit := do
    let withdrawFee ← getStorage feeOnWithdraw
    let feeDivisor ← requireSomeUint (safeAdd withdrawFee 1000000000000000000)
      "Panic(0x11): arithmetic overflow"
    let feeAmount := mulDiv512Up grossAssets withdrawFee feeDivisor
    let netAssets ← requireSomeUint (safeSub grossAssets feeAmount)
      "Panic(0x11): arithmetic underflow"
    let recipient ← getStorageAddr feeRecipient
    let asset ← getStorageAddr underlyingToken

    -- `super._withdraw`: burn first, then send the fee-exclusive asset amount.
    _burn owner shares
    require receiverTransferSucceeds "SafeERC20FailedOperation"
    safeTransfer asset receiver netAssets

    if feeAmount > 0 && recipient != zeroAddress then
      require feeTransferSucceeds "SafeERC20FailedOperation"
      safeTransfer asset recipient feeAmount
    else
      pure ()

  -- `YoVault.requestRedeem`, preserving its instant/queued branch distinction.
  -- `grossAssets` is the explicit `super.previewRedeem`/oracle boundary.
  function reentrancy_trusted requestRedeem
      (shares : Uint256, receiver : Address, owner : Address, grossAssets : Uint256,
       externalUnderlyingBalance : Uint256,
       previewSucceeds : Bool, balanceReadSucceeds : Bool,
       receiverTransferSucceeds : Bool, feeTransferSucceeds : Bool) : Uint256 := do
    let pausedFlag ← getStorage paused
    require (pausedFlag == 0) "EnforcedPause"
    let sender ← msgSender
    let ownerBalance ← getMapping shareBalances owner
    require (receiver != zeroAddress) "ZeroReceiver"
    require (shares > 0) "SharesAmountZero"
    require (owner == sender) "NotSharesOwner"
    require (ownerBalance >= shares) "InsufficientShares"

    -- `super.previewRedeem` may call YO's oracle; the supplied gross value is
    -- usable only when that external preview succeeds. `_getAvailableBalance`
    -- likewise consumes a successful, well-formed underlying `balanceOf` read.
    require previewSucceeds "PreviewRedeemFailed"
    require balanceReadSucceeds "UnderlyingBalanceReadFailed"
    let available ← _getAvailableBalance externalUnderlyingBalance
    if available >= grossAssets then
      _withdraw receiver owner grossAssets shares receiverTransferSucceeds feeTransferSucceeds
      return grossAssets
    else
      let vault ← Verity.contractAddress
      _transfer owner vault shares
      let oldPendingTotal ← getStorage totalPendingAssets
      let oldPendingShares ← getMapping pendingShares receiver
      let oldPendingAssets ← getMapping pendingAssets receiver
      let nextPendingTotal ← requireSomeUint (safeAdd oldPendingTotal grossAssets)
        "Panic(0x11): arithmetic overflow"
      let nextPendingShares ← requireSomeUint (safeAdd oldPendingShares shares)
        "Panic(0x11): arithmetic overflow"
      let nextPendingAssets ← requireSomeUint (safeAdd oldPendingAssets grossAssets)
        "Panic(0x11): arithmetic overflow"
      setStorage totalPendingAssets nextPendingTotal
      setMapping pendingShares receiver nextPendingShares
      setMapping pendingAssets receiver nextPendingAssets
      return 0

  -- Public ERC-4626 `redeem` wrapper.  Source applies `whenNotPaused` here and
  -- then calls `requestRedeem`, whose own modifier performs the second pause
  -- check.  Keeping both checks preserves the selected public surface.
  function reentrancy_trusted redeem
      (shares : Uint256, receiver : Address, owner : Address, grossAssets : Uint256,
       externalUnderlyingBalance : Uint256,
       previewSucceeds : Bool, balanceReadSucceeds : Bool,
       receiverTransferSucceeds : Bool, feeTransferSucceeds : Bool) : Uint256 := do
    let pausedFlag ← getStorage paused
    require (pausedFlag == 0) "EnforcedPause"
    let requestId ← requestRedeem shares receiver owner grossAssets externalUnderlyingBalance
      previewSucceeds balanceReadSucceeds receiverTransferSucceeds feeTransferSucceeds
    return requestId

  -- `YoVault.fulfillRedeem`.  The share and gross-asset guards deliberately
  -- remain independent: zero arguments and non-proportional components are
  -- source-permitted whenever the corresponding stored component is nonzero.
  function reentrancy_trusted fulfillRedeem
      (receiver : Address, shares : Uint256, grossAssets : Uint256,
       authorityCallSucceeds : Bool, authorityAllows : Bool,
       receiverTransferSucceeds : Bool, feeTransferSucceeds : Bool) : Unit := do
    let authorized ← isAuthorized authorityCallSucceeds authorityAllows
    require authorized "Unauthorized"
    let storedShares ← getMapping pendingShares receiver
    let storedAssets ← getMapping pendingAssets receiver
    require (storedShares != 0 && shares <= storedShares) "InvalidSharesAmount"
    require (storedAssets != 0 && grossAssets <= storedAssets) "InvalidAssetsAmount"
    let oldPendingTotal ← getStorage totalPendingAssets
    require (oldPendingTotal >= grossAssets) "Panic(0x11): arithmetic underflow"

    setMapping pendingShares receiver (sub storedShares shares)
    setMapping pendingAssets receiver (sub storedAssets grossAssets)
    setStorage totalPendingAssets (sub oldPendingTotal grossAssets)
    let vault ← Verity.contractAddress
    _withdraw receiver vault grossAssets shares receiverTransferSucceeds feeTransferSucceeds

  -- `YoVault.cancelRedeem`, including return to `receiver` rather than to a
  -- historical request owner.
  function reentrancy_trusted cancelRedeem
      (receiver : Address, shares : Uint256, grossAssets : Uint256,
       authorityCallSucceeds : Bool, authorityAllows : Bool) : Unit := do
    let authorized ← isAuthorized authorityCallSucceeds authorityAllows
    require authorized "Unauthorized"
    let storedShares ← getMapping pendingShares receiver
    let storedAssets ← getMapping pendingAssets receiver
    require (storedShares != 0 && shares <= storedShares) "InvalidSharesAmount"
    require (storedAssets != 0 && grossAssets <= storedAssets) "InvalidAssetsAmount"
    let oldPendingTotal ← getStorage totalPendingAssets
    require (oldPendingTotal >= grossAssets) "Panic(0x11): arithmetic underflow"

    setMapping pendingShares receiver (sub storedShares shares)
    setMapping pendingAssets receiver (sub storedAssets grossAssets)
    setStorage totalPendingAssets (sub oldPendingTotal grossAssets)
    let vault ← Verity.contractAddress
    _transfer vault receiver shares

  -- The two source fee configuration methods are included solely to express a
  -- source-faithful queue-then-fee-change-then-fulfill trace. They retain the
  -- `requiresAuth` order but do not model authority internals or events.
  function internal updateWithdrawFee
      (newFee : Uint256, authorityCallSucceeds : Bool, authorityAllows : Bool) : Unit := do
    let authorized ← isAuthorized authorityCallSucceeds authorityAllows
    require authorized "Unauthorized"
    require (newFee < 100000000000000000) "InvalidFee"
    setStorage feeOnWithdraw newFee

  function internal updateFeeRecipient
      (newRecipient : Address, authorityCallSucceeds : Bool, authorityAllows : Bool) : Unit := do
    let authorized ← isAuthorized authorityCallSucceeds authorityAllows
    require authorized "Unauthorized"
    setStorageAddr feeRecipient newRecipient

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
