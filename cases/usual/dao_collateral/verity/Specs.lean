import Verity.Specs.Common
import Benchmark.Cases.Usual.DaoCollateral.Contract

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

def ghostUsd0SupplyOf (s : ContractState) : Uint256 :=
  s.storage 0

def ghostTreasuryCollateralOf (s : ContractState) (rwaToken : Address) : Uint256 :=
  s.storageMap 1 rwaToken

def redeemFeeBpsOf (s : ContractState) : Uint256 :=
  s.storage 2

def isCBROnState (s : ContractState) : Bool :=
  s.storage 3 != 0

def cbrCoefOf (s : ContractState) : Uint256 :=
  s.storage 4

def expectedFeeUsd0
    (stableAmount redeemFee tokenUnit : Uint256) : Uint256 :=
  let rawFee := div (mul stableAmount redeemFee) SCALAR_TEN_KWEI
  if tokenUnit < SCALAR_ONE then
    let scale := div SCALAR_ONE tokenUnit
    mul (div rawFee scale) scale
  else
    rawFee

def expectedReturnedCollateral
    (stableAmount price tokenUnit redeemFee cbrCoef : Uint256)
    (cbrActive : Bool) : Uint256 :=
  let fee := expectedFeeUsd0 stableAmount redeemFee tokenUnit
  let netBurned := sub stableAmount fee
  let baseReturned := div (mul netBurned tokenUnit) price
  if cbrActive then div (mul baseReturned cbrCoef) SCALAR_ONE else baseReturned

def expectedSwapUsdQuote
    (collateralAmount price tokenUnit : Uint256) : Uint256 :=
  div (mul collateralAmount price) tokenUnit

def successfulSwapArithmetic
    (rwaToken : Address) (amount price tokenUnit : Uint256)
    (s : ContractState) : Prop :=
  let wadQuoteInUSD := expectedSwapUsdQuote amount price tokenUnit
  supportedTokenUnit tokenUnit = true ∧
  tokenUnit != 0 ∧
  amount <= 340282366920938463463374607431768211455 ∧
  wadQuoteInUSD ≠ 0 ∧
  mulDoesNotWrap amount price ∧
  addDoesNotWrap (ghostUsd0SupplyOf s) wadQuoteInUSD ∧
  addDoesNotWrap (ghostTreasuryCollateralOf s rwaToken) amount

def feeUsd0 (stableAmount tokenUnit : Uint256) (s : ContractState) : Uint256 :=
  redeemFeeAmount stableAmount (redeemFeeBpsOf s) tokenUnit

def netBurnedUsd0 (stableAmount tokenUnit : Uint256) (s : ContractState) : Uint256 :=
  sub stableAmount (feeUsd0 stableAmount tokenUnit s)

def returnedCollateralFor
    (stableAmount price tokenUnit : Uint256) (s : ContractState) : Uint256 :=
  cbrAdjustedTokenAmount
    (tokenAmountForUsd (netBurnedUsd0 stableAmount tokenUnit s) price tokenUnit)
    (cbrCoefOf s)
    (isCBROnState s)

def feeMintedUsd0 (stableAmount tokenUnit : Uint256) (s : ContractState) : Uint256 :=
  if isCBROnState s then 0 else feeUsd0 stableAmount tokenUnit s

def collateralValueUsd (collateralAmount price tokenUnit : Uint256) : Uint256 :=
  floorMulDiv collateralAmount price tokenUnit

def swap_conservation_spec
    (rwaToken : Address) (amount price tokenUnit : Uint256) (s s' : ContractState) : Prop :=
  let wadQuoteInUSD := expectedSwapUsdQuote amount price tokenUnit
  ghostUsd0SupplyOf s' = add (ghostUsd0SupplyOf s) wadQuoteInUSD ∧
  ghostTreasuryCollateralOf s' rwaToken = add (ghostTreasuryCollateralOf s rwaToken) amount

def swap_value_conservation_spec
    (rwaToken : Address) (amount price tokenUnit : Uint256)
    (s s' : ContractState) : Prop :=
  ghostUsd0SupplyOf s' = add (ghostUsd0SupplyOf s) (expectedSwapUsdQuote amount price tokenUnit) ∧
  ghostTreasuryCollateralOf s' rwaToken = add (ghostTreasuryCollateralOf s rwaToken) amount

def successfulRedeemArithmetic
    (rwaToken : Address) (stableAmount price tokenUnit : Uint256)
    (s : ContractState) : Prop :=
  let fee := expectedFeeUsd0 stableAmount (redeemFeeBpsOf s) tokenUnit
  let netBurned := sub stableAmount fee
  let baseReturned := div (mul netBurned tokenUnit) price
  let returnedCollateral :=
    expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
      (cbrCoefOf s) (isCBROnState s)
  let feeMinted := if isCBROnState s then 0 else fee
  supportedTokenUnit tokenUnit = true ∧
  daoConfigBounds (redeemFeeBpsOf s) (cbrCoefOf s) ∧
  mulDoesNotWrap stableAmount (redeemFeeBpsOf s) ∧
  fee <= stableAmount ∧
  mulDoesNotWrap netBurned tokenUnit ∧
  (isCBROnState s → mulDoesNotWrap baseReturned (cbrCoefOf s)) ∧
  addDoesNotWrap (ghostUsd0SupplyOf s) feeMinted ∧
  stableAmount <= add (ghostUsd0SupplyOf s) feeMinted ∧
  returnedCollateral <= ghostTreasuryCollateralOf s rwaToken

def redeem_conservation_spec
    (rwaToken : Address) (stableAmount price tokenUnit : Uint256)
    (s s' : ContractState) : Prop :=
  let feeMinted := feeMintedUsd0 stableAmount tokenUnit s
  let returnedCollateral :=
    expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
      (cbrCoefOf s) (isCBROnState s)
  ghostUsd0SupplyOf s' = sub (add (ghostUsd0SupplyOf s) feeMinted) stableAmount ∧
  ghostTreasuryCollateralOf s' rwaToken =
    sub (ghostTreasuryCollateralOf s rwaToken) returnedCollateral

def redeem_return_formula_spec
    (returned stableAmount price tokenUnit : Uint256) (s : ContractState) : Prop :=
  returned =
    expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
      (cbrCoefOf s) (isCBROnState s)

def redeem_fee_formula_spec
    (stableAmount tokenUnit : Uint256) (s : ContractState) : Prop :=
  feeUsd0 stableAmount tokenUnit s =
    expectedFeeUsd0 stableAmount (redeemFeeBpsOf s) tokenUnit

end Benchmark.Cases.Usual.DaoCollateral
