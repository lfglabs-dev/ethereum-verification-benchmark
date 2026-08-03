import Benchmark.Cases.Usual.DaoCollateral.Specs
import Verity.Proofs.Stdlib.Automation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

@[simp] private theorem getStorage_apply_raw (sl : StorageSlot Uint256)
    (s : ContractState) :
    getStorage sl s = ContractResult.success (s.readSlot sl.slot) s := rfl

@[simp] private theorem setStorage_apply_raw (sl : StorageSlot Uint256)
    (value : Uint256) (s : ContractState) :
    setStorage sl value s = ContractResult.success () (s.writeSlot sl.slot value) := rfl

@[simp] private theorem getMapping_apply_raw (sl : StorageSlot (Address → Uint256))
    (key : Address) (s : ContractState) :
    getMapping sl key s = ContractResult.success (s.readMap sl.slot key) s := rfl

@[simp] private theorem setMapping_apply_raw (sl : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (s : ContractState) :
    setMapping sl key value s = ContractResult.success ()
      { s.writeMap sl.slot key value with
        knownAddresses := fun «slot» =>
          if «slot» == sl.slot then (s.knownAddresses «slot»).insert key
          else s.knownAddresses «slot» } := rfl

@[simp] private theorem bind_getStorage_raw {α : Type} (sl : StorageSlot Uint256)
    (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind (getStorage sl) f s = f (s.readSlot sl.slot) s := rfl
@[simp] private theorem bind_setStorage_raw {α : Type} (sl : StorageSlot Uint256)
    (value : Uint256) (f : Unit → Contract α) (s : ContractState) :
    Verity.bind (setStorage sl value) f s = f () (s.writeSlot sl.slot value) := rfl
@[simp] private theorem bind_getMapping_raw {α : Type}
    (sl : StorageSlot (Address → Uint256)) (key : Address)
    (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind (getMapping sl key) f s = f (s.readMap sl.slot key) s := rfl
@[simp] private theorem bind_setMapping_raw {α : Type}
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256)
    (f : Unit → Contract α) (s : ContractState) :
    Verity.bind (setMapping sl key value) f s = f ()
      { s.writeMap sl.slot key value with
        knownAddresses := fun «slot» =>
          if «slot» == sl.slot then (s.knownAddresses «slot»).insert key
          else s.knownAddresses «slot» } := rfl

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
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping,
      ContractState.writeSlot, ContractState.writeMap]
    all_goals try unfold Verity.bind
    all_goals simp_all [Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      ContractResult.snd, setStorage, setMapping, ContractState.writeSlot,
      ContractState.writeMap]
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
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping,
      ContractState.writeSlot, ContractState.writeMap]
    all_goals try unfold Verity.bind
    all_goals simp_all [Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      ContractResult.snd, setStorage, setMapping, ContractState.writeSlot,
      ContractState.writeMap]

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
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping,
      ContractState.writeSlot, ContractState.writeMap]
    all_goals try unfold Verity.bind
    all_goals simp_all [Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      ContractResult.snd, setStorage, setMapping, ContractState.writeSlot,
      ContractState.writeMap]
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
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping,
      ContractState.writeSlot, ContractState.writeMap]
    all_goals try unfold Verity.bind
    all_goals simp_all [Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      ContractResult.snd, setStorage, setMapping, ContractState.writeSlot,
      ContractState.writeMap]

end Benchmark.Cases.Usual.DaoCollateral
