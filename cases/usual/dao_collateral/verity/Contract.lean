import Contracts.Common

set_option linter.dupNamespace false

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity model of Usual `src/daoCollateral/DaoCollateral.sol`.

  Targeted deployed implementation:
  - Proxy: https://etherscan.io/address/0xde6e1F680C4816446C8D515989E2358636A38b04
  - Active implementation: 0x0eEc861D49f15F585D6Bb4301FC4f89BCe22AF4e

  Simplifications and rationale:
  - Registry, token mapping, access-control, permits, nonce/intents, pause flags,
    reentrancy guards, events, and SwapperEngine paths are omitted. They gate who
    may call or route functions but do not change direct swap/redeem arithmetic.
  - ERC20 transfers and USD0 mint/burn calls are represented as updates to
    `ghostTreasuryCollateral` and `ghostUsd0Supply`, avoiding USD0 token correctness.
  - Oracle reads and token decimals are explicit parameters (`price`,
    `tokenUnit`). The swap quote is computed inside the model from those values.
    `tokenUnit` is required to be one of the Solidity `10 ** decimals` values
    for supported collateral decimals `0..18`; larger decimal counts would take
    a different normalization branch and are outside this direct-market
    benchmark.
  - `Math.mulDiv(..., Floor)` is modeled by Uint256 `div` after `mul`. Overflow
    preconditions are theorem hypotheses instead of modeled Solidity reverts.
  - CBR is modeled only in redeem return calculation, where it changes the
    collateral debited from treasury.
-/

def SCALAR_ONE : Uint256 := 1000000000000000000
def SCALAR_TEN_KWEI : Uint256 := 10000

def supportedTokenUnit (tokenUnit : Uint256) : Bool :=
  tokenUnit == 1 ||
  tokenUnit == 10 ||
  tokenUnit == 100 ||
  tokenUnit == 1000 ||
  tokenUnit == 10000 ||
  tokenUnit == 100000 ||
  tokenUnit == 1000000 ||
  tokenUnit == 10000000 ||
  tokenUnit == 100000000 ||
  tokenUnit == 1000000000 ||
  tokenUnit == 10000000000 ||
  tokenUnit == 100000000000 ||
  tokenUnit == 1000000000000 ||
  tokenUnit == 10000000000000 ||
  tokenUnit == 100000000000000 ||
  tokenUnit == 1000000000000000 ||
  tokenUnit == 10000000000000000 ||
  tokenUnit == 100000000000000000 ||
  tokenUnit == SCALAR_ONE

def floorMulDiv (x y denominator : Uint256) : Uint256 :=
  div (mul x y) denominator

def redeemFeeAmount (stableAmount redeemFee tokenUnit : Uint256) : Uint256 :=
  let rawFee := floorMulDiv stableAmount redeemFee SCALAR_TEN_KWEI
  if tokenUnit < SCALAR_ONE then
    mul (div rawFee (div SCALAR_ONE tokenUnit)) (div SCALAR_ONE tokenUnit)
  else
    rawFee

def tokenAmountForUsd (wadStableAmount price tokenUnit : Uint256) : Uint256 :=
  floorMulDiv wadStableAmount tokenUnit price

def cbrAdjustedTokenAmount
    (baseAmount cbrCoef : Uint256) (isCBROn : Bool) : Uint256 :=
  if isCBROn then floorMulDiv baseAmount cbrCoef SCALAR_ONE else baseAmount

verity_contract DaoCollateral where
  storage
    ghostUsd0Supply : Uint256 := slot 0
    ghostTreasuryCollateral : Address → Uint256 := slot 1
    redeemFeeBps : Uint256 := slot 2
    cbrOn : Uint256 := slot 3
    cbrCoefficient : Uint256 := slot 4

  function swapDirect
      (rwaToken : Address, amount : Uint256, minAmountOut : Uint256, price : Uint256, tokenUnit : Uint256) : Unit := do
    require (amount != 0) "AmountIsZero"
    require (amount <= 340282366920938463463374607431768211455) "AmountTooHigh"
    require (tokenUnit != 0) "InvalidTokenDecimals"
    require
      (tokenUnit == 1 ||
      tokenUnit == 10 ||
      tokenUnit == 100 ||
      tokenUnit == 1000 ||
      tokenUnit == 10000 ||
      tokenUnit == 100000 ||
      tokenUnit == 1000000 ||
      tokenUnit == 10000000 ||
      tokenUnit == 100000000 ||
      tokenUnit == 1000000000 ||
      tokenUnit == 10000000000 ||
      tokenUnit == 100000000000 ||
      tokenUnit == 1000000000000 ||
      tokenUnit == 10000000000000 ||
      tokenUnit == 100000000000000 ||
      tokenUnit == 1000000000000000 ||
      tokenUnit == 10000000000000000 ||
      tokenUnit == 100000000000000000 ||
      tokenUnit == 1000000000000000000)
      "UnsupportedTokenDecimals"
    let wadQuoteInUSD := div (mul amount price) tokenUnit
    require (wadQuoteInUSD != 0) "AmountTooLow"
    require (wadQuoteInUSD >= minAmountOut) "AmountTooLow"

    let supply ← getStorage ghostUsd0Supply
    setStorage ghostUsd0Supply (add supply wadQuoteInUSD)

    let collateral ← getMapping ghostTreasuryCollateral rwaToken
    setMapping ghostTreasuryCollateral rwaToken (add collateral amount)

  function redeemDirect
      (rwaToken : Address, stableAmount : Uint256, minAmountOut : Uint256, price : Uint256, tokenUnit : Uint256) : Uint256 := do
    require (stableAmount != 0) "AmountIsZero"
    require (price != 0) "InvalidOraclePrice"
    require (tokenUnit != 0) "InvalidTokenDecimals"
    require
      (tokenUnit == 1 ||
      tokenUnit == 10 ||
      tokenUnit == 100 ||
      tokenUnit == 1000 ||
      tokenUnit == 10000 ||
      tokenUnit == 100000 ||
      tokenUnit == 1000000 ||
      tokenUnit == 10000000 ||
      tokenUnit == 100000000 ||
      tokenUnit == 1000000000 ||
      tokenUnit == 10000000000 ||
      tokenUnit == 100000000000 ||
      tokenUnit == 1000000000000 ||
      tokenUnit == 10000000000000 ||
      tokenUnit == 100000000000000 ||
      tokenUnit == 1000000000000000 ||
      tokenUnit == 10000000000000000 ||
      tokenUnit == 100000000000000000 ||
      tokenUnit == 1000000000000000000)
      "UnsupportedTokenDecimals"

    let feeBps ← getStorage redeemFeeBps
    let cbrCoef ← getStorage cbrCoefficient
    let rawFee := div (mul stableAmount feeBps) 10000
    let feeScale := div 1000000000000000000 tokenUnit
    let fee := ite (tokenUnit < 1000000000000000000) (mul (div rawFee feeScale) feeScale) rawFee
    let burnedStable := sub stableAmount fee

    let cbrFlag ← getStorage cbrOn
    let cbrActive := cbrFlag != 0

    let baseReturned := div (mul burnedStable tokenUnit) price
    let returnedCollateral :=
      ite cbrActive (div (mul baseReturned cbrCoef) 1000000000000000000) baseReturned
    require (returnedCollateral != 0) "AmountTooLow"
    require (returnedCollateral >= minAmountOut) "AmountTooLow"

    let supply ← getStorage ghostUsd0Supply
    let feeMinted := ite cbrActive 0 fee
    setStorage ghostUsd0Supply (sub (add supply feeMinted) stableAmount)

    let collateral ← getMapping ghostTreasuryCollateral rwaToken
    setMapping ghostTreasuryCollateral rwaToken (sub collateral returnedCollateral)

    return returnedCollateral

def mulDoesNotWrap (x y : Uint256) : Prop :=
  x.val * y.val < Verity.Core.Uint256.modulus

def addDoesNotWrap (x y : Uint256) : Prop :=
  x.val + y.val < Verity.Core.Uint256.modulus

def daoConfigBounds (redeemFee cbrCoef : Uint256) : Prop :=
  redeemFee <= SCALAR_TEN_KWEI ∧ cbrCoef <= SCALAR_ONE

end Benchmark.Cases.Usual.DaoCollateral
