import Contracts.Common

namespace Benchmark.Cases.Velora.BridgeStaking

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of Velora BridgeStaking.

  Upstream: https://github.com/VeloraDEX/velora-miro-contracts
  Commit:   bfb5f8093bc6f6db0f0840b83d22e803c2811fcb
  File:     contracts/BridgeStaking.sol

  Target invariant:
  - `allocatedTokens[token] <= tokenBalance[token]` for both VLR and WETH.
  - Proves owner's `withdrawUnallocatedTokens` can never consume allocated funds.

  Simplifications
  ---------------
  - Storage is a flattened semantic representation, not BridgeStaking's EVM
    storage layout: token balances and allocations are scalar slots, and each
    Staking struct field is a separate keyed mapping. Entry balances include the
    Across delivery and faithfully represent `balanceOf(address(this))`.
  - External-call results are narrow, unconstrained callback inputs. The seVLR
    `depositResult` input uses 1 for success and every other value for Solidity's
    catch/rescue path. Boolean `vlrTransferSuccess`, `wethTransferSuccess`, and
    `transferSuccess` inputs model each SafeTransferLib call: false reverts the
    entire modeled call to its incoming state; true debits exactly the requested
    amount. No linked external is invoked or verified. On deposit success,
    allocations
    and balances decrease by the exact requested VLR/WETH amounts. This relies
    on standard ERC-20 semantics: successful transfers debit exactly the
    requested amount.
  - Public-boundary checks are outside this accounting transition: Solidity's
    onlySpokePool and whenNotPaused checks are scope exclusions; `isVlr` ranges
    only over the two whitelisted tokens. Rescue authorization and withdrawal
    ownership are likewise caller-boundary exclusions in their modeled bodies.
  - keccak256 key abstracted as opaque Uint256 argument.
  - Events omitted (no accounting effect).
  - The Solidity `beneficiary != address(0)` record-existence sentinel is
    modeled explicitly. The beneficiary decoded by the callback is an input.
  - Every Solidity-checked uint256 add/sub uses `addPanic`/`subPanic`, whose
    internal Verity `require` reverts on overflow/underflow. `Contract.run`
    restores the original pre-call state on every such revert.
  - No transfer fees, rebases, seizures, donations, or other balance changes
    occur during the atomic call. `depositResult != 1` selects Solidity's
    catch-and-rescue behavior; failed SafeTransferLib results atomically revert.
-/

verity_contract Staking where
  storage
    /- BridgeStaking's VLR token balance (token.getBalance()). -/
    vlrBalance : Uint256 := slot 0
    /- BridgeStaking's WETH token balance (token.getBalance()). -/
    wethBalance : Uint256 := slot 1
    /- `allocatedTokens[VLR]`. -/
    allocatedVLR : Uint256 := slot 2
    /- `allocatedTokens[WETH]`. -/
    allocatedWETH : Uint256 := slot 3

    /- Flattened `stakingData[key].vlrAmount`. -/
    stakingVlrAmount : Uint256 → Uint256 := slot 4
    /- Flattened `stakingData[key].wethAmount`. -/
    stakingWethAmount : Uint256 → Uint256 := slot 5
    /- Flattened `stakingData[key].beneficiary`. -/
    stakingBeneficiary : Uint256 → Uint256 := slot 6
    /- Flattened `stakingData[key].vlrReceived` (0 or 1). -/
    stakingVlrReceived : Uint256 → Uint256 := slot 7
    /- Flattened `stakingData[key].wethReceived` (0 or 1). -/
    stakingWethReceived : Uint256 → Uint256 := slot 8

  /- Internal source-faithful accounting helper for the VLR receipt branch. -/
  function creditVlrReceipt (key : Uint256, receivedAmount : Uint256) : Unit := do
    let currentAllocVLR ← getStorage allocatedVLR
    let creditedVLR ← addPanic currentAllocVLR receivedAmount
    setStorage allocatedVLR creditedVLR
    setMappingUint stakingVlrReceived key 1

  /- Internal source-faithful accounting helper for the WETH receipt branch. -/
  function creditWethReceipt (key : Uint256, receivedAmount : Uint256) : Unit := do
    let currentAllocWETH ← getStorage allocatedWETH
    let creditedWETH ← addPanic currentAllocWETH receivedAmount
    setStorage allocatedWETH creditedWETH
    setMappingUint stakingWethReceived key 1

  /- Internal source-faithful `_stake` accounting tail. It preserves the exact
     success/catch flag behavior and exact allocation/balance debits. -/
  function settleIfComplete (key : Uint256, depositResult : Uint256,
      vlrTransferSuccess : Bool, wethTransferSuccess : Bool) : Unit := do
    let vlrRecv ← getMappingUint stakingVlrReceived key
    let wethRecv ← getMappingUint stakingWethReceived key
    let bothReceived := vlrRecv == 1 && wethRecv == 1
    if bothReceived then
      let sVlrAmount ← getMappingUint stakingVlrAmount key
      let sWethAmount ← getMappingUint stakingWethAmount key
      let aVLR ← getStorage allocatedVLR
      let aWETH ← getStorage allocatedWETH
      let bVLR ← getStorage vlrBalance
      let bWETH ← getStorage wethBalance
      let nextAVLR ← subPanic aVLR sVlrAmount
      let nextBVLR ← subPanic bVLR sVlrAmount
      let nextAWETH ← subPanic aWETH sWethAmount
      let nextBWETH ← subPanic bWETH sWethAmount
      if depositResult == 1 then
        setStorage allocatedVLR nextAVLR
        setStorage vlrBalance nextBVLR
        setStorage allocatedWETH nextAWETH
        setStorage wethBalance nextBWETH
      else
        setMappingUint stakingVlrReceived key 0
        setStorage allocatedVLR nextAVLR
        require vlrTransferSuccess "VlrTransferFailed"
        setStorage vlrBalance nextBVLR
        setMappingUint stakingWethReceived key 0
        setStorage allocatedWETH nextAWETH
        require wethTransferSuccess "WethTransferFailed"
        setStorage wethBalance nextBWETH
    else
      pure ()

  /- Internal source-faithful composition of receipt credit and `_stake`. -/
  function processValidatedReceipt (key : Uint256, isVlr : Bool, receivedAmount : Uint256,
      depositResult : Uint256, vlrTransferSuccess : Bool,
      wethTransferSuccess : Bool) : Unit := do
    if isVlr then
      creditVlrReceipt key receivedAmount
    else
      creditWethReceipt key receivedAmount
    settleIfComplete key depositResult vlrTransferSuccess wethTransferSuccess

  /- Internal source-faithful record initialization and validation prefix. It
     preserves the beneficiary sentinel, stored-record amount check, and flags. -/
  function prepareRecord (key : Uint256, vlrAmount : Uint256, wethAmount : Uint256, beneficiary : Address, isVlr : Bool, receivedAmount : Uint256) : Unit := do
    let existingBeneficiary ← getMappingUintAddr stakingBeneficiary key
    if existingBeneficiary == zeroAddress then
      setMappingUint stakingVlrAmount key vlrAmount
      setMappingUint stakingWethAmount key wethAmount
      setMappingUintAddr stakingBeneficiary key beneficiary
    else
      pure ()
    let vlrRecv ← getMappingUint stakingVlrReceived key
    let wethRecv ← getMappingUint stakingWethReceived key
    let bothReceived := vlrRecv == 1 && wethRecv == 1
    if bothReceived then
      require false "AlreadyExecuted"
    else
      pure ()
    let storedVlrAmount ← getMappingUint stakingVlrAmount key
    let storedWethAmount ← getMappingUint stakingWethAmount key
    let selectedStoredAmount := ite isVlr storedVlrAmount storedWethAmount
    require (receivedAmount == selectedStoredAmount) "AmountMismatch"
    let alreadyReceived := ite isVlr vlrRecv wethRecv
    require (alreadyReceived == 0) "TokensAlreadyReceived"

  /- Models `handleV3AcrossMessage`.
     `isVlr = true` selects VLR accounting; false selects WETH.
     `beneficiary` is decoded from the callback message.
     `depositResult` is an unconstrained branch abstraction: 1 selects deposit
     success; any other value selects catch/rescue. -/
  function handleV3AcrossMessage (key : Uint256, vlrAmount : Uint256, wethAmount : Uint256,
      _minBptAmount : Uint256, beneficiary : Address, isVlr : Bool,
      receivedAmount : Uint256, depositResult : Uint256,
      vlrTransferSuccess : Bool, wethTransferSuccess : Bool) : Unit := do
    -- Read all relevant state
    let currentVlrBalance ← getStorage vlrBalance
    let currentWethBalance ← getStorage wethBalance
    let currentAllocVLR ← getStorage allocatedVLR
    let currentAllocWETH ← getStorage allocatedWETH

    -- Select token-specific values
    let currentBalance := ite isVlr currentVlrBalance currentWethBalance
    let currentAllocated := ite isVlr currentAllocVLR currentAllocWETH

    -- Solidity evaluates this checked addition before the comparison.
    let requiredBalance ← addPanic currentAllocated receivedAmount
    require (currentBalance >= requiredBalance) "InsufficientReceivedAmount"

    -- Preserve exact sentinel initialization, stored-amount checks, and flags.
    prepareRecord key vlrAmount wethAmount beneficiary isVlr receivedAmount

    -- Credit the selected allocation/flag, then run the exact `_stake` tail.
    processValidatedReceipt key isVlr receivedAmount depositResult
      vlrTransferSuccess wethTransferSuccess

  /- Models `rescuePendingFunds(updatedMessage)`.
     Beneficiary-or-owner authorization is a public-boundary scope exclusion. -/
  function rescuePendingFunds (key : Uint256, vlrTransferSuccess : Bool,
      wethTransferSuccess : Bool) : Unit := do
    let sVlrAmount ← getMappingUint stakingVlrAmount key
    let sWethAmount ← getMappingUint stakingWethAmount key
    let beneficiary ← getMappingUintAddr stakingBeneficiary key
    let vlrRecv ← getMappingUint stakingVlrReceived key
    let wethRecv ← getMappingUint stakingWethReceived key
    require (beneficiary != zeroAddress) "StakingNotStarted"
    let bothReceived := vlrRecv == 1 && wethRecv == 1
    if bothReceived then
      require false "StakingAlreadyExecuted"
    else
      pure ()

    let aVLR ← getStorage allocatedVLR
    let bVLR ← getStorage vlrBalance

    -- Rescue VLR if received
    if vlrRecv == 1 then
      let nextAVLR ← subPanic aVLR sVlrAmount
      let nextBVLR ← subPanic bVLR sVlrAmount
      setMappingUint stakingVlrReceived key 0
      setStorage allocatedVLR nextAVLR
      require vlrTransferSuccess "VlrTransferFailed"
      setStorage vlrBalance nextBVLR
    else
      pure ()

    -- Rescue WETH if received
    let aWETH2 ← getStorage allocatedWETH
    let bWETH2 ← getStorage wethBalance
    let wethRecv2 ← getMappingUint stakingWethReceived key
    if wethRecv2 == 1 then
      let nextAWETH ← subPanic aWETH2 sWethAmount
      let nextBWETH ← subPanic bWETH2 sWethAmount
      setMappingUint stakingWethReceived key 0
      setStorage allocatedWETH nextAWETH
      require wethTransferSuccess "WethTransferFailed"
      setStorage wethBalance nextBWETH
    else
      pure ()

  /- Models the VLR/WETH accounting slice of `withdrawUnallocatedTokens(token, to)`.
     Solidity accepts arbitrary token addresses; `isVlr` selects which of the two
     invariant-tracked tokens this benchmark analyzes. Owner authorization is a
     public-boundary scope exclusion. -/
  function withdrawUnallocatedTokens (isVlr : Bool, transferSuccess : Bool) : Unit := do
    let currentVlrBalance ← getStorage vlrBalance
    let currentWethBalance ← getStorage wethBalance
    let currentAllocVLR ← getStorage allocatedVLR
    let currentAllocWETH ← getStorage allocatedWETH

    let currentBalance := ite isVlr currentVlrBalance currentWethBalance
    let currentAllocated := ite isVlr currentAllocVLR currentAllocWETH
    let unallocated ← subPanic currentBalance currentAllocated
    require (unallocated > 0) "InsufficientUnallocatedBalance"
    require transferSuccess "TransferFailed"
    if isVlr then
      let remainingVLR ← subPanic currentVlrBalance unallocated
      setStorage vlrBalance remainingVLR
    else
      let remainingWETH ← subPanic currentWethBalance unallocated
      setStorage wethBalance remainingWETH

end Benchmark.Cases.Velora.BridgeStaking
