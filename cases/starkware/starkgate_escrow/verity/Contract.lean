import Contracts.Common

namespace Benchmark.Cases.Starkware.StarkgateEscrow

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity model of the StarkGate L1 bridge accounting for the escrow
  lower-bound invariant.

  Source: https://github.com/starknet-io/starkgate-contracts
  Commit: 07e11c39119a10d5742735be5b1d51894ebf5311
  Contract: StarknetTokenBridge.sol (base), StarknetEthBridge.sol (ETH override)

  What was simplified | Why
  - `IERC20(token).balanceOf(address(this))` or `address(this).balance` is
    represented by ghost slot `assetBalance` | external token/ETH storage is
    outside the contract, but the escrow invariant depends on it.
  - `cumulativeDeposits` and `cumulativeWithdrawals` are ghost aggregate
    counters that track total tokens flowing in via deposits and out via
    withdrawals/reclaims | the real contract does not store these counters, but
    they capture the accounting bookkeeping needed to state the invariant.
  - `Transfers.transferIn` is modeled as `setStorage assetBalance (add ...)`
    and `Transfers.transferOut` as `setStorage assetBalance (sub ...)` |
    the proof target is the accounting inequality, not the ERC20 transfer
    mechanism.
  - `messagingContract().sendMessageToL2` is abstracted as a no-op gate |
    cross-domain message dispatch does not change the L1 escrow balance.
  - `messagingContract().consumeMessageFromL2` is abstracted as a gate
    hypothesis: it succeeds on the modeled withdrawal path and reverts otherwise
    | L2 message consumption state is external to L1 accounting.
  - `messagingContract().cancelL1ToL2Message` is abstracted as a gate
    hypothesis on reclaim | the cancellation mechanism does not change the
    escrow balance directly; only the subsequent transferOut does.
  - Deposit max-balance check (`currentBalance + amount <= getMaxTotalBalance`)
    is modeled as a hypothesis, not an internal constraint | the invariant holds
    regardless of the cap.
  - Fee logic on ETH deposits (`msg.value - amount` credited as fee) is
    abstracted: deposit increases `assetBalance` by `amount` and
    `cumulativeDeposits` by `amount`; the fee excess is a donation-equivalent
    that only increases the balance further, strengthening the lower bound.
  - `tokenSettings` mapping, `TokenStatus` enum, withdrawal-limit logic,
    `onlyManager`/`onlyServicingToken` modifiers, and deployment status checks
    are not needed for the accounting invariant | they gate access but do not
    affect the balance arithmetic once the modeled path is selected.
  - Single-token abstraction: all deposits and withdrawals are scalar amounts
    without per-token routing | the invariant holds per-token in the real
    contract, and modeling one token slice preserves the accounting logic.
-/

verity_contract StarkgateBridge where
  storage
    -- Ghost: L1 escrow balance of the bridged token (IERC20.balanceOf or address(this).balance).
    assetBalance : Uint256 := slot 0
    -- Ghost: cumulative total of all accepted deposits.
    cumulativeDeposits : Uint256 := slot 1
    -- Ghost: cumulative total of all withdrawals and reclaims (outflows).
    cumulativeWithdrawals : Uint256 := slot 2

  -- src: StarknetTokenBridge.sol deposit/depositWithMessage -> acceptDeposit -> Transfers.transferIn.
  -- Increases escrow balance and cumulative deposits by `amount`.
  function deposit (amount : Uint256) : Unit := do
    require (amount > 0) "ZERO_DEPOSIT"
    let assetBalance_ ← getStorage assetBalance
    setStorage assetBalance (add assetBalance_ amount)
    let cumulativeDeposits_ ← getStorage cumulativeDeposits
    setStorage cumulativeDeposits (add cumulativeDeposits_ amount)

  -- src: StarknetTokenBridge.sol withdraw -> consumeMessage -> transferOutFunds.
  -- Decreases escrow balance by `amount`, increases cumulative withdrawals.
  -- consumeMessageFromL2 is abstracted as a gate (always succeeds on the modeled path).
  function withdraw (amount : Uint256) : Unit := do
    let assetBalance_ ← getStorage assetBalance
    require (amount <= assetBalance_) "INSUFFICIENT_BALANCE"
    setStorage assetBalance (sub assetBalance_ amount)
    let cumulativeWithdrawals_ ← getStorage cumulativeWithdrawals
    setStorage cumulativeWithdrawals (add cumulativeWithdrawals_ amount)

  -- src: StarknetTokenBridge.sol depositReclaim/depositWithMessageReclaim -> cancelL1ToL2Message -> transferOutFunds.
  -- Returns previously-deposited funds to the depositor.
  -- Decreases escrow balance by `amount`, increases cumulative withdrawals (refunds net out).
  -- cancelL1ToL2Message is abstracted as a gate (always succeeds on the modeled path).
  function depositReclaim (amount : Uint256) : Unit := do
    let assetBalance_ ← getStorage assetBalance
    require (amount <= assetBalance_) "INSUFFICIENT_BALANCE"
    setStorage assetBalance (sub assetBalance_ amount)
    let cumulativeWithdrawals_ ← getStorage cumulativeWithdrawals
    setStorage cumulativeWithdrawals (add cumulativeWithdrawals_ amount)

end Benchmark.Cases.Starkware.StarkgateEscrow
