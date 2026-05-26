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
  - `curveBalance supply` abstracts `_getBalanceFromReserveRatio(supply)`,
    i.e. `ceil(A * pow(supply, B + 1) / (B + 1))`. Verity does not currently
    expose a faithful PRB/ABDK fixed-point exponentiation model. The executable
    transitions receive the Solidity helper's computed result as an input,
    while proof hypotheses use a labeled trusted-helper predicate rather than a
    direct post-reserve equality premise.
  - ERC20 per-account balances, allowances, permit, and events are omitted.
    Aggregate `totalSupply` is modeled because it determines `virtualSupply`.
  - Reserve-token transfers are omitted. The selected invariant concerns the
    on-chain virtual reserve variables that the Solidity invariant checks.
  - Access-control addresses are represented by Boolean successful-path inputs
    where they affect the selected state transition. Address identity itself is
    omitted.
  - Solidity checked arithmetic is surfaced as explicit theorem hypotheses.
-/

opaque curveBalance : Uint256 -> Uint256

def decimalPrecision : Uint256 := 1000000000000000000

verity_contract BaseBondingCurve where
  storage
    virtualBalance : Uint256 := slot 0
    floorSupply : Uint256 := slot 1
    floorBalance : Uint256 := slot 2
    totalSupply : Uint256 := slot 3
    feePercentage : Uint256 := slot 4
    initialized : Uint256 := slot 5

  function init
      (virtualSupply_ : Uint256, floorSupply_ : Uint256,
        computedVirtualBalance : Uint256, computedFloorBalance : Uint256) : Unit := do
    require (floorSupply_ != 0) "Floor must be nonzero"
    require (floorSupply_ <= virtualSupply_) "Floor cannot be above current state"

    setStorage virtualBalance computedVirtualBalance
    setStorage floorSupply floorSupply_
    setStorage floorBalance computedFloorBalance
    setStorage totalSupply (sub virtualSupply_ floorSupply_)
    setStorage initialized 1

  function buy
      (_isFeeRouter : Bool, bcTokenAmount : Uint256, buyFeeAmount : Uint256,
        computedNewVirtualBalance : Uint256) : Unit := do
    let initialized_ ← getStorage initialized
    require (initialized_ == 1) "BC not initialized yet"
    require (bcTokenAmount != 0) "BC: Zero amount"

    let totalSupply_ ← getStorage totalSupply

    let totalMinted := add bcTokenAmount buyFeeAmount

    setStorage virtualBalance computedNewVirtualBalance
    setStorage totalSupply (add totalSupply_ totalMinted)

  function sell (bcTokenAmount : Uint256, computedNewVirtualBalance : Uint256) : Unit := do
    let feePercentage_ ← getStorage feePercentage
    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply

    let feeAmount := div (mul bcTokenAmount feePercentage_) 1000000000000000000
    let netAmount := sub bcTokenAmount feeAmount
    require (netAmount != 0) "BC: Zero amount"
    let oldVirtualSupply := add floorSupply_ totalSupply_
    require (netAmount <= oldVirtualSupply) "BC: Amount greater than supply"
    require (netAmount <= totalSupply_) "BC: Burn amount exceeds supply"

    setStorage virtualBalance computedNewVirtualBalance
    setStorage totalSupply (sub totalSupply_ netAmount)

  function floorSellAndBurn
      (authorizedFeeRouter : Bool, bcTokenAmount : Uint256, computedNewFloorBalance : Uint256) :
      Unit := do
    require authorizedFeeRouter "Caller is not fee router"
    require (bcTokenAmount != 0) "BC: Zero amount"
    let floorSupply_ ← getStorage floorSupply
    let totalSupply_ ← getStorage totalSupply
    let oldVirtualSupply := add floorSupply_ totalSupply_
    let newFloorSupply := add floorSupply_ bcTokenAmount
    require (newFloorSupply <= oldVirtualSupply) "Floor cannot surpass virtual state"
    require (bcTokenAmount <= totalSupply_) "BC: Burn amount exceeds supply"

    setStorage floorSupply newFloorSupply
    setStorage floorBalance computedNewFloorBalance
    setStorage totalSupply (sub totalSupply_ bcTokenAmount)

end Benchmark.Cases.Polaris.BondingCurve
