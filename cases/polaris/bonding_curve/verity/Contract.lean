import Contracts.Common

namespace Benchmark.Cases.Polaris.BondingCurve

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Verity model of Polaris `BaseBondingCurve`.

  Upstream: https://github.com/Polaris-Finance/bonding-curve
  Commit:   540c4ba5d0b86c0f42399d214f02120f3f8719b0
  Files:    src/BaseBondingCurve.sol
            src/PRBBondingCurve.sol
            src/ABDKBondingCurve.sol

  In scope:
  - `init`
  - `buy`
  - `sell`
  - `floorSellAndBurn`
  - the reserve-ratio accounting helpers these transitions rely on.

  Target invariant:
  - `virtualBalance` equals the rounded reserve function at `virtualSupply`.
  - `floorBalance` equals the rounded reserve function at `floorSupply`.

  Simplifications:
  - `_getBalanceFromReserveRatio(supply)` is modeled through its source-shaped
    outer arithmetic:
      `(A * curvePow(supply, B_PLUS_1) + DECIMAL_PRECISION - 1) / B_PLUS_1`.
    `curvePow` is an opaque boundary for the virtual `pow` implementation in
    `PRBBondingCurve.sol` / `ABDKBondingCurve.sol`. Verity does not currently
    expose a faithful PRB `SD59x18.pow` or ABDK `64x64 exp_2(log_2(...))`
    fixed-point model. The broad helper-output precondition is intentionally
    gone; executable transitions receive only the raw pow result and compute
    the helper's multiplication and decimal-precision rounding division
    themselves.
  - ERC20 per-account balances, allowances, permit, and events are omitted.
    Aggregate `totalSupply` is modeled because it determines `virtualSupply`.
  - Reserve-token transfers are omitted. The selected invariant concerns the
    on-chain virtual reserve variables that the Solidity invariant checks.
  - Access-control addresses are represented by Boolean successful-path inputs
    where they affect the selected state transition. Address identity itself is
    omitted.
  - Solidity checked arithmetic is surfaced as explicit theorem hypotheses.
-/

def decimalPrecision : Uint256 := 1000000000000000000

/-- Opaque boundary for the concrete PRB/ABDK fixed-point pow implementation. -/
opaque curvePow : Uint256 -> Uint256 -> Uint256

/--
  Source-shaped final division from `_getBalanceFromReserveRatio`:
  `(left + DECIMAL_PRECISION - 1) / B_PLUS_1`.
-/
def reserveRatioBalanceFromLeft (left bPlusOne : Uint256) : Uint256 :=
  div (sub (add left decimalPrecision) 1) bPlusOne

/-- Mirrors `_getReserveRatioLeftFormula`: `A * pow(_supply, B_PLUS_1)`. -/
def reserveRatioLeftFormula
    (alpha bPlusOne supply : Uint256) : Uint256 :=
  mul alpha (curvePow supply bPlusOne)

/-- Mirrors `_getBalanceFromReserveRatio` modulo the opaque pow implementation. -/
def getBalanceFromReserveRatio
    (alpha bPlusOne supply : Uint256) : Uint256 :=
  let left := mul alpha (curvePow supply bPlusOne)
  reserveRatioBalanceFromLeft left bPlusOne

verity_contract BaseBondingCurve where
  storage
    virtualBalance : Uint256 := slot 0
    floorSupply : Uint256 := slot 1
    floorBalance : Uint256 := slot 2
    totalSupply : Uint256 := slot 3
    feePercentage : Uint256 := slot 4
    initialized : Uint256 := slot 5
    alpha : Uint256 := slot 6
    bPlusOne : Uint256 := slot 7

  function init
      (virtualSupply_ : Uint256, floorSupply_ : Uint256,
        computedVirtualPow : Uint256, computedFloorPow : Uint256) : Unit := do
    require (floorSupply_ != 0) "Floor must be nonzero"
    require (floorSupply_ <= virtualSupply_) "Floor cannot be above current state"
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne
    let initialVirtualLeft := mul alpha_ computedVirtualPow
    let computedVirtualBalance :=
      div (sub (add initialVirtualLeft 1000000000000000000) 1) bPlusOne_
    let initialFloorLeft := mul alpha_ computedFloorPow
    let computedFloorBalance :=
      div (sub (add initialFloorLeft 1000000000000000000) 1) bPlusOne_

    setStorage virtualBalance computedVirtualBalance
    setStorage floorSupply floorSupply_
    setStorage floorBalance computedFloorBalance
    setStorage totalSupply (sub virtualSupply_ floorSupply_)
    setStorage initialized 1

  function buy
      (_isFeeRouter : Bool, bcTokenAmount : Uint256, buyFeeAmount : Uint256,
        computedNewVirtualPow : Uint256) : Unit := do
    let initialized_ ← getStorage initialized
    require (initialized_ == 1) "BC not initialized yet"
    require (bcTokenAmount != 0) "BC: Zero amount"

    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne

    let totalMinted := add bcTokenAmount buyFeeAmount
    let _newVirtualSupply := add (add floorSupply_ totalSupply_) totalMinted
    let newVirtualLeft := mul alpha_ computedNewVirtualPow
    let computedNewVirtualBalance :=
      div (sub (add newVirtualLeft 1000000000000000000) 1) bPlusOne_

    setStorage virtualBalance computedNewVirtualBalance
    setStorage totalSupply (add totalSupply_ totalMinted)

  function sell (bcTokenAmount : Uint256, computedNewVirtualPow : Uint256) : Unit := do
    let feePercentage_ ← getStorage feePercentage
    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne

    let feeAmount := div (mul bcTokenAmount feePercentage_) 1000000000000000000
    let netAmount := sub bcTokenAmount feeAmount
    require (netAmount != 0) "BC: Zero amount"
    let oldVirtualSupply := add floorSupply_ totalSupply_
    require (netAmount <= oldVirtualSupply) "BC: Amount greater than supply"
    require (netAmount <= totalSupply_) "BC: Burn amount exceeds supply"
    let _newVirtualSupply := sub oldVirtualSupply netAmount
    let newVirtualLeft := mul alpha_ computedNewVirtualPow
    let computedNewVirtualBalance :=
      div (sub (add newVirtualLeft 1000000000000000000) 1) bPlusOne_

    setStorage virtualBalance computedNewVirtualBalance
    setStorage totalSupply (sub totalSupply_ netAmount)

  function floorSellAndBurn
      (authorizedFeeRouter : Bool, bcTokenAmount : Uint256,
        computedNewFloorPow : Uint256) : Unit := do
    require authorizedFeeRouter "Caller is not fee router"
    require (bcTokenAmount != 0) "BC: Zero amount"
    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne
    let oldVirtualSupply := add floorSupply_ totalSupply_
    let newFloorSupply := add floorSupply_ bcTokenAmount
    require (newFloorSupply <= oldVirtualSupply) "Floor cannot surpass virtual state"
    require (bcTokenAmount <= totalSupply_) "BC: Burn amount exceeds supply"
    let newFloorLeft := mul alpha_ computedNewFloorPow
    let computedNewFloorBalance :=
      div (sub (add newFloorLeft 1000000000000000000) 1) bPlusOne_

    setStorage floorSupply newFloorSupply
    setStorage floorBalance computedNewFloorBalance
    setStorage totalSupply (sub totalSupply_ bcTokenAmount)

end Benchmark.Cases.Polaris.BondingCurve
