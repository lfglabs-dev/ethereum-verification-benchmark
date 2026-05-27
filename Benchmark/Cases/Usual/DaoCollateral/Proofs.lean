import Benchmark.Cases.Usual.DaoCollateral.Specs
import Verity.Proofs.Stdlib.Automation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

theorem swap_conservation
    (rwaToken : Address) (amount wadQuoteInUSD minAmountOut : Uint256) (s : ContractState)
    (hAmount : amount != 0)
    (hAmountMax : amount <= 340282366920938463463374607431768211455)
    (hQuoteNonzero : wadQuoteInUSD != 0)
    (hMin : wadQuoteInUSD >= minAmountOut)
    (hArithmetic :
      addDoesNotWrap (usd0SupplyOf s) wadQuoteInUSD ∧
      addDoesNotWrap (treasuryCollateralOf s rwaToken) amount) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount wadQuoteInUSD minAmountOut).run s).snd
    swap_conservation_spec rwaToken amount wadQuoteInUSD s s' := by
  simp [swap_conservation_spec, usd0SupplyOf, treasuryCollateralOf,
    DaoCollateral.swapDirect, hAmount, hAmountMax, hQuoteNonzero, hMin, hArithmetic,
    addDoesNotWrap,
    DaoCollateral.usd0Supply, DaoCollateral.treasuryCollateral,
    Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
    getStorage, setStorage, getMapping, setMapping]

theorem swap_value_conservation
    (rwaToken : Address) (amount wadQuoteInUSD minAmountOut price tokenUnit : Uint256)
    (s : ContractState)
    (hAmount : amount != 0)
    (hMin : wadQuoteInUSD >= minAmountOut)
    (hArithmetic : successfulSwapArithmetic rwaToken amount wadQuoteInUSD price tokenUnit s) :
    let s' := ((DaoCollateral.swapDirect rwaToken amount wadQuoteInUSD minAmountOut).run s).snd
    swap_value_conservation_spec rwaToken amount wadQuoteInUSD price tokenUnit s s' := by
  rcases hArithmetic with
    ⟨hTokenUnit, hAmountMax, hQuoteNonzero, hMul, hQuote, hSupplyAdd, hCollateralAdd⟩
  have hQuoteNonzero' : expectedSwapUsdQuote amount price tokenUnit ≠ 0 := by
    intro h
    apply hQuoteNonzero
    rw [hQuote]
    exact h
  have hMin' : expectedSwapUsdQuote amount price tokenUnit ≥ minAmountOut := by
    rw [← hQuote]
    exact hMin
  have hQuoteNonzero'' : div (mul amount price) tokenUnit ≠ 0 := by
    simpa [expectedSwapUsdQuote] using hQuoteNonzero'
  have hMin'' : div (mul amount price) tokenUnit ≥ minAmountOut := by
    simpa [expectedSwapUsdQuote] using hMin'
  simp [swap_value_conservation_spec, expectedSwapUsdQuote, hQuote,
    DaoCollateral.swapDirect, hAmount, hAmountMax, hQuoteNonzero'', hMin'',
    hSupplyAdd, hCollateralAdd, addDoesNotWrap,
    usd0SupplyOf, treasuryCollateralOf,
    DaoCollateral.usd0Supply, DaoCollateral.treasuryCollateral,
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
      ⟨hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe, hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      hCbr] at hConfig hFeeLe hNetMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.usd0Supply, DaoCollateral.treasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]
  · rcases hArithmetic with
      ⟨hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe, hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      hCbr] at hConfig hFeeLe hNetMul hCbrMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_return_formula_spec,
      redeemFeeBpsOf, cbrCoefOf, isCBROnState, expectedReturnedCollateral,
      expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.usd0Supply, DaoCollateral.treasuryCollateral,
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
      ⟨hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe, hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      hCbr] at hConfig hFeeLe hNetMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, usd0SupplyOf, treasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, usd0SupplyOf, treasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.usd0Supply, DaoCollateral.treasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]
  · rcases hArithmetic with
      ⟨hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe, hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      hCbr] at hConfig hFeeLe hNetMul hCbrMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, usd0SupplyOf, treasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr] at hReturnedNonzero hMin
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, usd0SupplyOf, treasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.usd0Supply, DaoCollateral.treasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping]

end Benchmark.Cases.Usual.DaoCollateral
