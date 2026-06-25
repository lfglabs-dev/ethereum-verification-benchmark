import Contracts.Common

namespace Benchmark.Cases.Pareto.RedemptionBacking

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity model of Pareto USP `ParetoDollarQueue.depositFunds` for the
  closed-epoch redemption backing guard.

  What was simplified | Why
  - `getUnlentBalanceScaled()` is represented by ghost slot `idleCollateralScaled` |
    the Solidity view loops over external ERC20 balances, but this proof targets the
    queue-level scaled total after a successful manager deposit.
  - `epochPending[epochNumber]` and `epochPending[epochNumber - 1]` are represented
    by scalar slots `currentEpochPending` and `previousEpochPending` | the theorem
    only needs the current epoch excluded from closed-epoch reserves and the optional
    previous-epoch reset performed by `depositFunds`.
  - Yield-source calls, caps, method allowlists, and token decimals are represented
    by the scalar `depositedScaled` input | those checks determine whether the call
    succeeds, while the invariant is the final reserve guard over scaled balances.
  - `isParetoDollarCollateralized()` is represented by `collateralizedFlag != 0` |
    full external NAV correctness depends on Credit Vault `virtualPrice` and pending
    withdrawal accounting, which are documented assumptions for this case.

  The modeled source guard is:

    `getUnlentBalanceScaled() + totCreditVaultsRequestedScaled
       >= totReservedWithdrawals - epochPending[epochNumber]`

  This captures the reviewed first theorem: manager deposits cannot complete after
  spending collateral needed for already closed redemption epochs.
-/

verity_contract ParetoDollarQueue where
  storage
    idleCollateralScaled : Uint256 := slot 0
    totCreditVaultsRequestedScaled : Uint256 := slot 1
    totReservedWithdrawals : Uint256 := slot 2
    currentEpochPending : Uint256 := slot 3
    previousEpochPending : Uint256 := slot 4
    collateralizedFlag : Uint256 := slot 5

  -- src: ParetoDollarQueue.sol depositFunds — post-call reserve check and optional
  -- previous closed-epoch readiness reset.
  function depositFunds (depositedScaled : Uint256) : Unit := do
    let collateralizedFlag_ ← getStorage collateralizedFlag
    require (collateralizedFlag_ != 0) "not-collateralized"

    let idlePre_ ← getStorage idleCollateralScaled
    require (depositedScaled <= idlePre_) "insufficient-idle"
    let idleAfter_ := sub idlePre_ depositedScaled
    setStorage idleCollateralScaled idleAfter_

    let requested_ ← getStorage totCreditVaultsRequestedScaled
    let reserved_ ← getStorage totReservedWithdrawals
    let currentPending_ ← getStorage currentEpochPending
    require (currentPending_ <= reserved_) "reserved-underflow"
    require (sub reserved_ currentPending_ <= add idleAfter_ requested_) "insufficient-backing"

    let previousPending_ ← getStorage previousEpochPending
    if previousPending_ <= idleAfter_ then
      setStorage previousEpochPending 0
    else
      setStorage previousEpochPending previousPending_

  -- src: ParetoDollarQueue.sol requestRedeem — current epoch claims increase both
  -- current pending requests and total burned-but-unclaimed USP. Per-user
  -- `userWithdrawalsEpochs` entries are intentionally aggregated away in this
  -- slice; successful Solidity checked additions are represented by later proof
  -- hypotheses when this transition is used.
  function requestRedeem (amount : Uint256) : Unit := do
    let currentPending_ ← getStorage currentEpochPending
    let reserved_ ← getStorage totReservedWithdrawals
    setStorage currentEpochPending (add currentPending_ amount)
    setStorage totReservedWithdrawals (add reserved_ amount)

end Benchmark.Cases.Pareto.RedemptionBacking
