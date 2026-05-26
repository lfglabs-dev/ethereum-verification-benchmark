import Contracts.Common

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of the Rootstock Flyover / Liquidity Bridge Contract peg-out
  quote lifecycle.

  Upstream: rsksmart/liquidity-bridge-contract
  Commit:   88a6d1ad64aeb3ad24e01042f4211ad8649784b9
  File:     src/PegOutContract.sol
  In scope: depositPegOut, refundPegOut, refundUserPegOut, _increaseBalance.

  Target invariant
  ----------------
  For each peg-out quote, the Rootstock-side deposited amount can be settled at
  most once. The amount assigned to the user, the LP, or the internal fallback
  balances is exactly the stored quote amount on a successful settlement, and
  any collateral slash call is explicitly separated as quote penalty accounting.

  Simplifications
  ----------------
  What was simplified:
  - `bytes32 quoteHash` is represented by an `Address` key.
  Why:
  - This case intentionally uses the same address-keyed mapping shape as the
    surrounding benchmark corpus. The proof needs stable per-quote identity,
    not cryptographic hash arithmetic.

  What was simplified:
  - `Quotes.PegOutQuote` is flattened to the fields that affect Rootstock-side
    quote conservation: `value`, `callFee`, `gasFee`, and `penaltyFee`.
  Why:
  - The omitted fields feed quote validation, Bitcoin destination checks, and
    deadlines. They do not alter the conserved RBTC amount once a quote is
    accepted.

  What was simplified:
  - Signature validation, provider registration, Bitcoin transaction parsing,
    and bridge confirmation checks are modeled as preconditions to the public
    lifecycle functions.
  Why:
  - They gate success in Solidity. The conservation theorem is about successful
    lifecycle transitions, so the model keeps those gates without reimplementing
    external cryptographic and bridge APIs. The LP penalty branch itself is
    computed from the quote deposit timestamp, Bitcoin confirmation timestamp,
    transfer-time allowance, BTC block time, expiry timestamp, and expiry block.

  What was simplified:
  - External `.call{value: amount}` success is modeled by `transferSucceeds`
    for quote settlement and `changeRefundSucceeds` for deposit overpayment
    refunds. Fallback balances are keyed by the recipient address just like
    Solidity `_balances`.
  Why:
  - Solidity either transfers the quote amount or credits `_balances` through
    `_increaseBalance`. The invariant covers both branches.

  What was simplified:
  - `slashPegOutCollateral` is represented by the local `slashCallAmount`
    witness rather than by CollateralManagement storage.
  Why:
  - The call is external to `PegOutContract`. This benchmark proves that the
    quote lifecycle reaches the slash-call branch with the expected penalty
    input; it does not prove the external collateral contract's internal state.

  What was simplified:
  - Solidity 0.8 checked additions are modeled by explicit no-overflow
    `require` guards before the corresponding `Uint256` additions.
  Why:
  - Bare Verity `Uint256` arithmetic is modular, while the source contract uses
    checked arithmetic for `value + callFee + gasFee`. These guards restrict the
    model to the same successful arithmetic paths as Solidity 0.8.
-/

def completedFlag : Uint256 := 1

verity_contract PegOutLifecycle where
  storage
    quoteAmount : Address → Uint256 := slot 0
    quotePenalty : Address → Uint256 := slot 1
    quoteCompleted : Address → Uint256 := slot 2
    lpPaid : Address → Uint256 := slot 3
    userPaid : Address → Uint256 := slot 4
    internalBalance : Address → Uint256 := slot 5
    slashCallAmount : Address → Uint256 := slot 6
    quoteRegistered : Address → Uint256 := slot 7
    quoteDepositTimestamp : Address → Uint256 := slot 8

  function depositPegOut
      (quoteHash : Address,
       value : Uint256, callFee : Uint256, gasFee : Uint256,
       penaltyFee : Uint256, msgValue : Uint256,
       dustThreshold : Uint256, changeRefundSucceeds : Bool,
       blockTimestamp : Uint256) : Unit := do
    let oldRegistered ← getMapping quoteRegistered quoteHash
    let oldCompleted ← getMapping quoteCompleted quoteHash
    let valueAndCallFee := add value callFee
    require (valueAndCallFee >= value)
      "RequiredAmountOverflow"
    let requiredAmount := add valueAndCallFee gasFee
    require (requiredAmount >= valueAndCallFee)
      "RequiredAmountOverflow"

    require (oldCompleted == 0) "QuoteAlreadyCompleted"
    require (oldRegistered == 0) "QuoteAlreadyRegistered"
    require (requiredAmount <= msgValue) "InsufficientAmount"

    let change := sub msgValue requiredAmount
    if change >= dustThreshold then
      require changeRefundSucceeds "ChangeRefundFailed"
    else
      pure ()

    setMapping quoteAmount quoteHash requiredAmount
    setMapping quotePenalty quoteHash penaltyFee
    setMapping quoteRegistered quoteHash 1
    setMapping quoteDepositTimestamp quoteHash blockTimestamp

  function refundPegOut
      (quoteHash : Address, lpRskAddress : Address,
       transferSucceeds : Bool,
       transferTime : Uint256, btcBlockTime : Uint256,
       firstConfirmationTimestamp : Uint256,
       expireDate : Uint256, currentTimestamp : Uint256,
       expireBlock : Uint256, currentBlock : Uint256) : Unit := do
    let registered ← getMapping quoteRegistered quoteHash
    let amount ← getMapping quoteAmount quoteHash
    let penalty ← getMapping quotePenalty quoteHash
    let depositTimestamp ← getMapping quoteDepositTimestamp quoteHash
    let oldCompleted ← getMapping quoteCompleted quoteHash
    let transferDeadline := add depositTimestamp transferTime
    require (transferDeadline >= depositTimestamp) "PenaltyTimeOverflow"
    let expectedConfirmation := add transferDeadline btcBlockTime
    require (expectedConfirmation >= transferDeadline) "PenaltyTimeOverflow"
    let shouldPenalize :=
      (firstConfirmationTimestamp > expectedConfirmation) ||
        (currentTimestamp > expireDate) ||
        (currentBlock > expireBlock)

    require (oldCompleted == 0) "QuoteAlreadyCompleted"
    require (registered == 1) "QuoteNotFound"

    setMapping quoteAmount quoteHash 0
    setMapping quoteRegistered quoteHash 0
    setMapping quoteCompleted quoteHash 1

    if shouldPenalize then
      setMapping slashCallAmount quoteHash penalty
    else
      pure ()

    if transferSucceeds then
      setMapping lpPaid quoteHash amount
    else
      let oldBalance ← getMapping internalBalance lpRskAddress
      let newBalance := add oldBalance amount
      require (newBalance >= oldBalance) "BalanceOverflow"
      setMapping internalBalance lpRskAddress newBalance

  function refundUserPegOut
      (quoteHash : Address, rskRefundAddress : Address,
       transferSucceeds : Bool) : Unit := do
    let registered ← getMapping quoteRegistered quoteHash
    let amount ← getMapping quoteAmount quoteHash
    let penalty ← getMapping quotePenalty quoteHash

    require (registered == 1) "QuoteNotFound"

    setMapping quoteAmount quoteHash 0
    setMapping quoteRegistered quoteHash 0
    setMapping quoteCompleted quoteHash 1
    setMapping slashCallAmount quoteHash penalty

    if transferSucceeds then
      setMapping userPaid quoteHash amount
    else
      let oldBalance ← getMapping internalBalance rskRefundAddress
      let newBalance := add oldBalance amount
      require (newBalance >= oldBalance) "BalanceOverflow"
      setMapping internalBalance rskRefundAddress newBalance

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
