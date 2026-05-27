import Benchmark.Cases.Usual.DaoCollateral.Specs
import Verity.Proofs.Stdlib.Automation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

theorem swap_conservation
    (rwaToken : Address) (amount minAmountOut price tokenUnit : Uint256) (s : ContractState)
    (hAmount : amount != 0)
    (hMin : expectedSwapUsdQuote amount price tokenUnit >= minAmountOut)
    (hArithmetic : successfulSwapArithmetic rwaToken amount price tokenUnit s) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount minAmountOut price tokenUnit).run s).snd
    swap_conservation_spec rwaToken amount price tokenUnit s s' := by
  rcases hArithmetic with
    ⟨hSupportedUnit, hTokenUnit, hAmountMax, hQuoteNonzero, hMul, hSupplyAdd,
      hCollateralAdd⟩
  simp [supportedTokenUnit, SCALAR_ONE] at hSupportedUnit
  have hQuoteNonzero' : div (mul amount price) tokenUnit ≠ 0 := by
    simpa [expectedSwapUsdQuote] using hQuoteNonzero
  have hMin' : div (mul amount price) tokenUnit ≥ minAmountOut := by
    simpa [expectedSwapUsdQuote] using hMin
  simp [swap_conservation_spec, expectedSwapUsdQuote, ghostUsd0SupplyOf, ghostTreasuryCollateralOf,
    DaoCollateral.swapDirect, hAmount, hAmountMax, hTokenUnit, hSupportedUnit,
    hQuoteNonzero', hMin', hSupplyAdd, hCollateralAdd, addDoesNotWrap,
    DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
    Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
    getStorage, setStorage, getMapping, setMapping]

theorem swap_value_conservation
    (rwaToken : Address) (amount minAmountOut price tokenUnit : Uint256)
    (s : ContractState)
    (hAmount : amount != 0)
    (hMin : expectedSwapUsdQuote amount price tokenUnit >= minAmountOut)
    (hArithmetic : successfulSwapArithmetic rwaToken amount price tokenUnit s) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount minAmountOut price tokenUnit).run s).snd
    swap_value_conservation_spec rwaToken amount price tokenUnit s s' := by
  rcases hArithmetic with
    ⟨hSupportedUnit, hTokenUnit, hAmountMax, hQuoteNonzero, hMul, hSupplyAdd,
      hCollateralAdd⟩
  simp [supportedTokenUnit, SCALAR_ONE] at hSupportedUnit
  have hQuoteNonzero'' : div (mul amount price) tokenUnit ≠ 0 := by
    simpa [expectedSwapUsdQuote] using hQuoteNonzero
  have hMin'' : div (mul amount price) tokenUnit ≥ minAmountOut := by
    simpa [expectedSwapUsdQuote] using hMin
  simp [swap_value_conservation_spec, expectedSwapUsdQuote,
    DaoCollateral.swapDirect, hAmount, hAmountMax, hTokenUnit, hSupportedUnit,
    hQuoteNonzero'', hMin'',
    hSupplyAdd, hCollateralAdd, addDoesNotWrap,
    ghostUsd0SupplyOf, ghostTreasuryCollateralOf,
    DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
    Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
    getStorage, setStorage, getMapping, setMapping]

theorem redeem_fee_formula
    (stableAmount tokenUnit : Uint256) (s : ContractState) :
    redeem_fee_formula_spec stableAmount tokenUnit s := by
  simp [redeem_fee_formula_spec, feeUsd0, redeemFeeBpsOf, redeemFeeAmount,
    expectedFeeUsd0, floorMulDiv]

theorem redeem_return_formula
    (stableAmount minAmountOut price tokenUnit : Uint256) (rwaToken : Address)
    (s : ContractState)
    (hAmount : stableAmount != 0)
    (hPrice : price != 0)
    (hTokenUnit : tokenUnit != 0)
    (hReturnedNonzero :
      expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
        (cbrCoefOf s) (isCBROnState s) ≠ 0)
    (hMin :
      minAmountOut.val ≤
        (expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
          (cbrCoefOf s) (isCBROnState s)).val)
    (hArithmetic :
      successfulRedeemArithmetic rwaToken stableAmount price tokenUnit s) :
    let result := (DaoCollateral.redeemDirect rwaToken stableAmount minAmountOut price tokenUnit).run s
    redeem_return_formula_spec result.fst stableAmount price tokenUnit s := by
  by_cases hCbr : s.storage 3 = 0
  · rcases hArithmetic with
      ⟨hSupportedUnit, hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe,
        hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      supportedTokenUnit, hCbr] at hSupportedUnit hConfig hFeeLe hNetMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hSupportedUnit,
      hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]
  · rcases hArithmetic with
      ⟨hSupportedUnit, hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe,
        hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      supportedTokenUnit, hCbr] at hSupportedUnit hConfig hFeeLe hNetMul hCbrMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hSupportedUnit,
      hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]

theorem redeem_conservation
    (rwaToken : Address) (stableAmount minAmountOut price tokenUnit : Uint256)
    (s : ContractState)
    (hAmount : stableAmount != 0)
    (hPrice : price != 0)
    (hTokenUnit : tokenUnit != 0)
    (hReturnedNonzero :
      expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
        (cbrCoefOf s) (isCBROnState s) ≠ 0)
    (hMin :
      minAmountOut.val ≤
        (expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
          (cbrCoefOf s) (isCBROnState s)).val)
    (hArithmetic :
      successfulRedeemArithmetic rwaToken stableAmount price tokenUnit s) :
    let s' := ((DaoCollateral.redeemDirect rwaToken stableAmount minAmountOut price tokenUnit).run s).snd
    redeem_conservation_spec rwaToken stableAmount price tokenUnit s s' := by
  by_cases hCbr : s.storage 3 = 0
  · rcases hArithmetic with
      ⟨hSupportedUnit, hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe,
        hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      supportedTokenUnit, hCbr] at hSupportedUnit hConfig hFeeLe hNetMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hSupportedUnit,
      hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]
  · rcases hArithmetic with
      ⟨hSupportedUnit, hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe,
        hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      supportedTokenUnit, hCbr] at hSupportedUnit hConfig hFeeLe hNetMul hCbrMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hSupportedUnit,
      hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]

end Benchmark.Cases.Usual.DaoCollateral
