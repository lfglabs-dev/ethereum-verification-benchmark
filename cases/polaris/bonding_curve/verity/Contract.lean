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
  - `_getBalanceFromReserveRatio(supply)` is modeled directly through its
    source-shaped outer arithmetic:
      `(A * curvePow(supply, B_PLUS_1) + DECIMAL_PRECISION - 1) / B_PLUS_1`.
    `curvePow` is the linked-external boundary for the virtual `pow`
    implementation in `PRBBondingCurve.sol` / `ABDKBondingCurve.sol`. Verity
    does not currently expose a faithful PRB `SD59x18.pow` or ABDK `64x64
    exp_2(log_2(...))` fixed-point model. The broad helper-output and raw-pow
    input preconditions are intentionally gone; executable transitions call the
    linked external boundary and compute the Polaris-owned multiplication and
    decimal-precision rounding division themselves.
  - ERC20 per-account balances, allowances, permit, and events are omitted.
    Aggregate `totalSupply` is modeled because it determines `virtualSupply`.
  - Reserve-token transfers are omitted. The selected invariant concerns the
    on-chain virtual reserve variables that the Solidity invariant checks.
  - Access-control addresses are represented by Boolean successful-path inputs
    where they affect the selected state transition. Address identity itself is
    omitted.
  - `initialized` is a Boolean storage abstraction for the source condition
    `initializerAccount == address(0)` after `init` deletes the initializer.
  - Buy/sell slippage checks are omitted because they do not write the reserve
    checkpoints. This widens the successful path for preservation. The buy
    nonzero guard and burn-supply guards model checks reached through source
    helper/ERC20 paths, so those theorem statements cover the nonzero,
    successful execution slice.
  - Solidity checked arithmetic is surfaced as explicit theorem hypotheses.
-/

def decimalPrecision : Uint256 := 1000000000000000000

/-- Linked-external boundary for the concrete PRB/ABDK fixed-point pow implementation. -/
def curvePow (supply bPlusOne : Uint256) : Uint256 :=
  Contracts.externalCallWords "curvePow" [supply, bPlusOne]

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

/-- Mirrors `_getBalanceFromReserveRatio` modulo the linked pow boundary. -/
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

  linked_externals
    external curvePow(Uint256, Uint256) -> (Uint256)

  function allow_post_interaction_writes init
      (virtualSupply_ : Uint256, floorSupply_ : Uint256) : Unit := do
    require (floorSupply_ != 0) "Floor cannot be zero"
    require (floorSupply_ <= virtualSupply_) "Floor cannot be above current state"
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne
    let initialVirtualPow := externalCall "curvePow" [virtualSupply_, bPlusOne_]
    let initialVirtualLeft := mul alpha_ initialVirtualPow
    let computedVirtualBalance :=
      div (sub (add initialVirtualLeft 1000000000000000000) 1) bPlusOne_
    let initialFloorPow := externalCall "curvePow" [floorSupply_, bPlusOne_]
    let initialFloorLeft := mul alpha_ initialFloorPow
    let computedFloorBalance :=
      div (sub (add initialFloorLeft 1000000000000000000) 1) bPlusOne_

    setStorage virtualBalance computedVirtualBalance
    setStorage floorSupply floorSupply_
    setStorage floorBalance computedFloorBalance
    setStorage totalSupply (sub virtualSupply_ floorSupply_)
    setStorage initialized 1

  function allow_post_interaction_writes buy
      (_isFeeRouter : Bool, bcTokenAmount : Uint256, buyFeeAmount : Uint256) : Unit := do
    let initialized_ ← getStorage initialized
    require (initialized_ == 1) "BC not initialized yet"
    require (bcTokenAmount != 0) "BC: Zero amount"

    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne

    let totalMinted := add bcTokenAmount buyFeeAmount
    let newVirtualSupply := add (add floorSupply_ totalSupply_) totalMinted
    let newVirtualPow := externalCall "curvePow" [newVirtualSupply, bPlusOne_]
    let newVirtualLeft := mul alpha_ newVirtualPow
    let computedNewVirtualBalance :=
      div (sub (add newVirtualLeft 1000000000000000000) 1) bPlusOne_

    setStorage virtualBalance computedNewVirtualBalance
    setStorage totalSupply (add totalSupply_ totalMinted)

  function allow_post_interaction_writes sell (bcTokenAmount : Uint256) : Unit := do
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
    let newVirtualSupply := sub oldVirtualSupply netAmount
    let newVirtualPow := externalCall "curvePow" [newVirtualSupply, bPlusOne_]
    let newVirtualLeft := mul alpha_ newVirtualPow
    let computedNewVirtualBalance :=
      div (sub (add newVirtualLeft 1000000000000000000) 1) bPlusOne_

    setStorage virtualBalance computedNewVirtualBalance
    setStorage totalSupply (sub totalSupply_ netAmount)

  function allow_post_interaction_writes floorSellAndBurn
      (authorizedFeeRouter : Bool, bcTokenAmount : Uint256) : Unit := do
    require authorizedFeeRouter "BC: Not allowed"
    require (bcTokenAmount != 0) "BC: Zero amount"
    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply
    let alpha_ ← getStorage alpha
    let bPlusOne_ ← getStorage bPlusOne
    let oldVirtualSupply := add floorSupply_ totalSupply_
    let newFloorSupply := add floorSupply_ bcTokenAmount
    require (newFloorSupply <= oldVirtualSupply) "Floor cannot surpass virtual state"
    require (bcTokenAmount <= totalSupply_) "BC: Burn amount exceeds supply"
    let newFloorPow := externalCall "curvePow" [newFloorSupply, bPlusOne_]
    let newFloorLeft := mul alpha_ newFloorPow
    let computedNewFloorBalance :=
      div (sub (add newFloorLeft 1000000000000000000) 1) bPlusOne_

    setStorage floorSupply newFloorSupply
    setStorage floorBalance computedNewFloorBalance
    setStorage totalSupply (sub totalSupply_ bcTokenAmount)

end Benchmark.Cases.Polaris.BondingCurve
