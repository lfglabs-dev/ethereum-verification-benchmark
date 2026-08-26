/-
Source-faithful control-flow slice for Aera Finance V3
`PriceAndFeeCalculatorV2` anchor/drift updates.

Pinned upstream:
`aera-finance/aera-contracts-public@f0ebc15985b2f19d1e599b604370fdbaeb314180`
`v3/src/core/PriceAndFeeCalculatorV2.sol`.

Simplifications:
* `_validatePriceUpdate`, `_isUpdateDelayExceeded`, and `_shouldPauseAnchor`
  inputs are explicit booleans. Their date arithmetic is not part of this
  secondary case.
* `_isPriceWithinAnchorBand` is preserved with EVM-word multiplication. Proof
  hypotheses make the source's uint128/uint16 no-overflow typing explicit before
  interpreting those word products as natural-number inequalities.
* Fee accrual and total-supply reads are summarized by `accrualSucceeds`.
  Successful active anchor updates still reset `accrualLag` to zero, and paused
  accumulation uses explicit modulo 2^32 to preserve the source `uint32` field.
  Revert atomicity remains executable.
-/

import Contracts.Common

namespace Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

verity_contract AeraPriceAndFeeCalculatorV2 where
  storage
    paused : Uint256 := slot 0
    pauseOnBadAnchorUpdate : Uint256 := slot 1
    anchorPrice : Uint256 := slot 2
    anchorTimestamp : Uint256 := slot 3
    driftPrice : Uint256 := slot 4
    driftTimestamp : Uint256 := slot 5
    minPriceToleranceRatio : Uint256 := slot 6
    maxPriceToleranceRatio : Uint256 := slot 7
    accrualLag : Uint256 := slot 8

  function internal _isPriceWithinAnchorBand
      (anchor : Uint256, candidate : Uint256) : Bool := do
    let minRatio ← getStorage minPriceToleranceRatio
    let maxRatio ← getStorage maxPriceToleranceRatio
    if candidate > anchor then
      return mul candidate 10000 <= mul anchor maxRatio
    else
      return mul candidate 10000 >= mul anchor minRatio

  function setDriftPrice
      (price : Uint256, timestamp : Uint256,
       validUpdate : Bool, delayWithinLimit : Bool) : Unit := do
    let paused_ ← getStorage paused
    require (paused_ == 0) "VaultPaused"
    require validUpdate "InvalidPriceUpdate"
    require delayWithinLimit "MaxUpdateDelayExceeded"
    let anchor ← getStorage anchorPrice
    require (anchor != 0) "VaultNotInitialized"
    let withinBand ← _isPriceWithinAnchorBand anchor price
    require withinBand "DriftOutsideAnchorBand"
    setStorage driftPrice price
    setStorage driftTimestamp timestamp

  function setAnchorPrice
      (price : Uint256, timestamp : Uint256,
       validUpdate : Bool, shouldPause : Bool,
       accrualSucceeds : Bool) : Unit := do
    require validUpdate "InvalidPriceUpdate"
    let paused_ ← getStorage paused
    let oldAnchorTimestamp ← getStorage anchorTimestamp
    if paused_ == 0 then
      if shouldPause then
        let pauseMode ← getStorage pauseOnBadAnchorUpdate
        require (pauseMode != 0) "BadAnchorPriceUpdate"
        setStorage paused 1
        setStorage accrualLag (sub timestamp oldAnchorTimestamp)
      else
        require accrualSucceeds "FeeAccrualFailed"
        setStorage accrualLag 0
    else
      let oldLag ← getStorage accrualLag
      setStorage accrualLag
        (mod (add oldLag (sub timestamp oldAnchorTimestamp)) 4294967296)
    setStorage anchorPrice price
    setStorage anchorTimestamp timestamp

end Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift
