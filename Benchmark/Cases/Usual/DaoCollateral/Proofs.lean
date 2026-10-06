import Benchmark.Cases.Usual.DaoCollateral.Specs
import Verity.Proofs.Stdlib.Automation

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

@[simp] private theorem readSlot_eq_storage (s : ContractState) (slotIdx : Nat) :
    s.readSlot slotIdx = s.storage slotIdx := rfl
@[simp] private theorem readAddrSlot_eq_storageAddr (s : ContractState) (slotIdx : Nat) :
    s.readAddrSlot slotIdx = s.storageAddr slotIdx := rfl
@[simp] private theorem readMap_eq_storageMap (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.readMap slotIdx k = s.storageMap slotIdx k := rfl
@[simp] private theorem readMapUint_eq_storageMapUint (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.readMapUint slotIdx k = s.storageMapUint slotIdx k := rfl
@[simp] private theorem readMap2_eq_storageMap2 (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.readMap2 slotIdx k1 k2 = s.storageMap2 slotIdx k1 k2 := rfl
@[simp] private theorem readTransient_eq_transientStorage (s : ContractState) (slotIdx : Nat) :
    s.readTransient slotIdx = s.transientStorage slotIdx := rfl
@[simp] private theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl
@[simp] private theorem storageAddr_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageAddr =
      s.storageAddr := rfl
@[simp] private theorem storageMap_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      s.storageMap := rfl
@[simp] private theorem storageMapUint_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapUint =
      s.storageMapUint := rfl
@[simp] private theorem storageMap2_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap2 =
      s.storageMap2 := rfl
@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] private theorem storageAddr_writeAddrSlot (s : ContractState) (slotIdx : Nat) (value : Address) (slotIdx' : Nat) :
    (s.writeAddrSlot slotIdx value).storageAddr slotIdx' =
      if slotIdx' == slotIdx then value else s.storageAddr slotIdx' := by
  by_cases h : slotIdx' = slotIdx
  · subst h; simp
  · simp [ContractState.storageAddr_writeAddrSlot_other s h value, h]
@[simp] private theorem storageMap_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256)
    (slotIdx' : Nat) (key' : Address) :
    (s.writeMap slotIdx key value).storageMap slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMap slotIdx' key' := by
  simp [ContractState.storageMap, ContractState.writeMap]
@[simp] private theorem storageMapUint_writeMapUint (s : ContractState) (slotIdx : Nat) (key value : Uint256)
    (slotIdx' : Nat) (key' : Uint256) :
    (s.writeMapUint slotIdx key value).storageMapUint slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMapUint slotIdx' key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint]
@[simp] private theorem storage_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storage = s.storage := by
  funext wordSlot; simp [ContractState.storage, ContractState.writeMap2]
@[simp] private theorem storageAddr_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageAddr = s.storageAddr := by
  funext addrSlot; simp [ContractState.storageAddr, ContractState.writeMap2]
@[simp] private theorem storageMap_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap = s.storageMap := by
  funext mapSlot mapKey; simp [ContractState.storageMap, ContractState.writeMap2]
@[simp] private theorem storageMapUint_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey; simp [ContractState.storageMapUint, ContractState.writeMap2]
@[simp] private theorem storageMap2_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256)
    (slotIdx' : Nat) (key1' key2' : Address) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap2 slotIdx' key1' key2' =
      if slotIdx' == slotIdx && key1' == key1 && key2' == key2 then value else s.storageMap2 slotIdx' key1' key2' := by
  simp [ContractState.storageMap2, ContractState.writeMap2, and_assoc]
@[simp] private theorem storageWords_slot_eq (s : ContractState) (slotIdx : Nat) :
    s.storageWords (.slot slotIdx) = s.storage slotIdx := rfl
@[simp] private theorem storageWords_map_eq (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.storageWords (.map slotIdx k) = s.storageMap slotIdx k := rfl
@[simp] private theorem storageWords_mapUint_eq (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.storageWords (.mapUint slotIdx k) = s.storageMapUint slotIdx k := rfl
@[simp] private theorem storageWords_map2_eq (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.storageWords (.map2 slotIdx k1 k2) = s.storageMap2 slotIdx k1 k2 := rfl
@[simp] private theorem storage_mk
    (sw : StorageKey → Uint256) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk sw sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      fun slotIdx => sw (.slot slotIdx) := rfl
@[simp] private theorem storageMap_mk
    (sw : StorageKey → Uint256) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk sw sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      fun slotIdx k => sw (.map slotIdx k) := rfl


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
    all_goals simp_all [Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      ContractResult.snd, setStorage, setMapping, ContractState.writeSlot,
      ContractState.writeMap]
    all_goals grind
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
    all_goals simp_all [Verity.bind, Bind.bind, Contract.run, ContractResult.fst,
      ContractResult.snd, setStorage, setMapping, ContractState.writeSlot,
      ContractState.writeMap]
    all_goals grind

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
      supportedTokenUnit, add, sub, mul, div, hCbr] at hSupportedUnit hConfig hFeeLe hNetMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, add, sub, mul, div, hCbr] at hReturnedNonzero hMin
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, add, sub, mul, div, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hSupportedUnit,
      hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping,
      ContractState.writeSlot, ContractState.writeMap]
  · rcases hArithmetic with
      ⟨hSupportedUnit, hConfig, hFeeMul, hFeeLe, hNetMul, hCbrMul, hSupplyAdd, hSupplyLe,
        hCollateralLe⟩
    simp [successfulRedeemArithmetic, redeemFeeBpsOf, cbrCoefOf, isCBROnState,
      expectedReturnedCollateral, expectedFeeUsd0, SCALAR_ONE, SCALAR_TEN_KWEI,
      supportedTokenUnit, add, sub, mul, div, hCbr] at hSupportedUnit hConfig hFeeLe hNetMul hCbrMul hSupplyAdd hSupplyLe hCollateralLe
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, add, sub, mul, div, hCbr] at hReturnedNonzero hMin
    simp [redeem_conservation_spec, feeMintedUsd0,
      feeUsd0, ghostUsd0SupplyOf, ghostTreasuryCollateralOf, redeemFeeBpsOf,
      cbrCoefOf, isCBROnState, expectedReturnedCollateral, expectedFeeUsd0,
      redeemFeeAmount, floorMulDiv, SCALAR_ONE, SCALAR_TEN_KWEI, add, sub, mul, div, hCbr,
      DaoCollateral.redeemDirect, hAmount, hPrice, hTokenUnit, hSupportedUnit,
      hReturnedNonzero, hMin,
      hConfig, hFeeLe, hSupplyAdd, hSupplyLe, hCollateralLe, addDoesNotWrap,
      daoConfigBounds,
      DaoCollateral.ghostUsd0Supply, DaoCollateral.ghostTreasuryCollateral,
      DaoCollateral.redeemFeeBps, DaoCollateral.cbrOn, DaoCollateral.cbrCoefficient,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      Verity.pure, Pure.pure, getStorage, setStorage, getMapping, setMapping,
      ContractState.writeSlot, ContractState.writeMap]

end Benchmark.Cases.Usual.DaoCollateral
