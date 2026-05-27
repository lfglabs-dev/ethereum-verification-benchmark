import Contracts.Common

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity model of the 1delta OneDeltaComposerEthereum caller-address
  propagation surface.

  Upstream:
  - Verified deployed source:
    https://www.codeslaw.app/contracts/ethereum/0x97648606fcc22bd96f87345ac83bd6cfcdf0acba
  - contracts/1delta/composer/BaseComposer.sol
  - contracts/1delta/composer/transfers/Transfers.sol
  - contracts/1delta/composer/transfers/AssetTransfers.sol
  - contracts/1delta/composer/swappers/callbacks/V3Callbacker.sol

  In scope:
  - `deltaCompose(bytes)` captures the outer `msg.sender`.
  - `_deltaComposeInternal` receives the explicit `callerAddress`.
  - `_transfers` dispatches the modeled transfer command ids.
  - `_transferFrom` records ERC20 `transferFrom(callerAddress, to, amount)`.
  - `_permit2TransferFrom` records Permit2
    `transferFrom(callerAddress, to, amount, token)`.
  - Flash-loan and swap callback continuations forward the same
    `callerAddress`.
  - `V3Callbacker.clSwapCallback` with `calldataLength == 0` directly pays
    the pool with ERC20 `transferFrom(callerAddress, caller(), amountToPay)`.

  Simplifications:
  - Packed calldata parsing and loop offsets are represented by already-decoded
    command ids. This is a semantic abstraction of the dispatcher loop, not a
    byte-for-byte parser translation.
  - External ERC20 and Permit2 calls are represented by event-log storage slots
    recording whether the pull occurred and the `from` word supplied to the
    call.
  - Token, receiver, amount, and balance fallback behavior are omitted because
    they do not affect which `from` address is passed to pull user funds.
  - Callback authentication is outside this invariant. The modeled callbacks
    take the already-validated outer caller address that the Solidity callback
    paths forward into `_deltaComposeInternal`.
-/

def TRANSFER_FROM : Uint256 := 0
def PERMIT2_TRANSFER_FROM : Uint256 := 4

verity_contract OneDeltaComposer where
  storage
    outerCallerWord : Uint256 := slot 0
    erc20TransferFromWord : Uint256 := slot 1
    permit2TransferFromWord : Uint256 := slot 2
    flashCallbackCallerWord : Uint256 := slot 3
    swapCallbackCallerWord : Uint256 := slot 4
    v3CallbackTransferFromWord : Uint256 := slot 5
    erc20TransferFromOccurred : Uint256 := slot 6
    permit2TransferFromOccurred : Uint256 := slot 7
    v3CallbackTransferFromOccurred : Uint256 := slot 8

  /- BaseComposer.deltaCompose(bytes): capture msg.sender and enter the
     internal dispatcher. The dispatcher body is modeled by path-specific
     entrypoints below because the benchmark starts from decoded commands. -/
  function deltaCompose () : Unit := do
    let callerAddress ← msgSender
    setStorage outerCallerWord (addressToWord callerAddress)

  /- BaseComposer._deltaComposeInternal(address callerAddress, ...):
     modeled as the decoded transfer-command slice of the packed loop. -/
  function _deltaComposeInternal_transferFrom (callerAddress : Address) : Unit := do
    setStorage outerCallerWord (addressToWord callerAddress)
    setStorage erc20TransferFromOccurred 1
    setStorage erc20TransferFromWord (addressToWord callerAddress)

  function _deltaComposeInternal_permit2TransferFrom (callerAddress : Address) : Unit := do
    setStorage outerCallerWord (addressToWord callerAddress)
    setStorage permit2TransferFromOccurred 1
    setStorage permit2TransferFromWord (addressToWord callerAddress)

  function _deltaComposeInternal_invalidTransfer (callerAddress : Address) : Unit := do
    setStorage outerCallerWord (addressToWord callerAddress)
    require false "InvalidOperation"

  /- Transfers._transfers(currentOffset, callerAddress). -/
  function _transfers_transferFrom (callerAddress : Address) : Unit := do
    setStorage erc20TransferFromOccurred 1
    setStorage erc20TransferFromWord (addressToWord callerAddress)

  function _transfers_permit2TransferFrom (callerAddress : Address) : Unit := do
    setStorage permit2TransferFromOccurred 1
    setStorage permit2TransferFromWord (addressToWord callerAddress)

  function _transfers_invalid (callerAddress : Address) : Unit := do
    setStorage outerCallerWord (addressToWord callerAddress)
    require false "InvalidOperation"

  /- AssetTransfers._transferFrom(currentOffset, callerAddress). -/
  function _transferFrom (callerAddress : Address) : Unit := do
    setStorage erc20TransferFromOccurred 1
    setStorage erc20TransferFromWord (addressToWord callerAddress)

  /- AssetTransfers._permit2TransferFrom(currentOffset, callerAddress). -/
  function _permit2TransferFrom (callerAddress : Address) : Unit := do
    setStorage permit2TransferFromOccurred 1
    setStorage permit2TransferFromWord (addressToWord callerAddress)

  /- Validated flash-loan callback continuation. -/
  function flashLoanCallbackTransferFrom (callerAddress : Address) : Unit := do
    setStorage flashCallbackCallerWord (addressToWord callerAddress)
    setStorage erc20TransferFromOccurred 1
    setStorage erc20TransferFromWord (addressToWord callerAddress)

  /- Validated swap callback continuation. -/
  function swapCallbackPermit2TransferFrom (callerAddress : Address) : Unit := do
    setStorage swapCallbackCallerWord (addressToWord callerAddress)
    setStorage permit2TransferFromOccurred 1
    setStorage permit2TransferFromWord (addressToWord callerAddress)

  /- V3Callbacker.clSwapCallback(..., calldataLength = 0). -/
  function v3SwapCallbackDirectTransferFrom (callerAddress : Address) : Unit := do
    setStorage swapCallbackCallerWord (addressToWord callerAddress)
    setStorage v3CallbackTransferFromOccurred 1
    setStorage v3CallbackTransferFromWord (addressToWord callerAddress)

  /- Fixed all-path harness used only for the aggregate theorem. -/
  function allModeledPullsHarness () : Unit := do
    let callerAddress ← msgSender
    setStorage outerCallerWord (addressToWord callerAddress)
    setStorage erc20TransferFromOccurred 1
    setStorage erc20TransferFromWord (addressToWord callerAddress)
    setStorage permit2TransferFromOccurred 1
    setStorage permit2TransferFromWord (addressToWord callerAddress)
    setStorage flashCallbackCallerWord (addressToWord callerAddress)
    setStorage swapCallbackCallerWord (addressToWord callerAddress)
    setStorage v3CallbackTransferFromOccurred 1
    setStorage v3CallbackTransferFromWord (addressToWord callerAddress)

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
