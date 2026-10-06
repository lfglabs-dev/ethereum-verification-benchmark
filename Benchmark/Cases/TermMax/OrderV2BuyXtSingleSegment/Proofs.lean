import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

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
@[simp] private theorem address_ofNat_storageWords_addr (s : ContractState) (slotIdx : Nat) :
    Verity.Core.Address.ofNat (s.storageWords (.addr slotIdx)).val = s.storageAddr slotIdx := rfl


private theorem uint256_zero_sub_eq_modulus_sub (x : Uint256) :
    sub 0 x = Verity.Core.Uint256.ofNat (Verity.Core.Uint256.modulus - x.val) := by
  cases x with
  | mk val hlt =>
      by_cases h0 : val = 0
      · subst h0
        simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat]
      · simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat, h0]

private theorem uint256_zero_sub_toUint256_int256 (cutOffset : Int256) :
    sub 0 (Verity.Core.Int256.toUint256 cutOffset) = Verity.Core.Int256.toUint256 (-cutOffset) := by
  rw [uint256_zero_sub_eq_modulus_sub]
  change Verity.Core.Uint256.ofNat (Verity.Core.Uint256.modulus - cutOffset.word.val) =
    (Verity.Core.Int256.ofUint256
      (Verity.Core.Uint256.ofNat (Verity.Core.Int256.modulus - cutOffset.word.val))).word
  rfl

private theorem buyXt_success
    (daysToMaturity debtTokenAmtIn minTokenOut : Uint256)
    (borrowTakerFeeRatio lendMakerFeeRatio : Uint256)
    (cutLiqSquare : Uint256) (cutOffset : Int256)
    (s : ContractState)
    (hNoCross :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity (s.storage 0) debtTokenAmtIn
          borrowTakerFeeRatio cutLiqSquare cutOffset
        <= s.storage 0)
    (hMinOut :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (s.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn
        >= minTokenOut) :
    (TermMaxOrderV2BuyXtSingleSegment.buyXt
      debtTokenAmtIn minTokenOut daysToMaturity
      borrowTakerFeeRatio lendMakerFeeRatio cutLiqSquare cutOffset).run s =
      ContractResult.success
        (add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (s.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn,
         sub debtTokenAmtIn
           (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
             (add 100000000 borrowTakerFeeRatio)),
         sub debtTokenAmtIn
           (sub debtTokenAmtIn
             (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
               (add 100000000 borrowTakerFeeRatio))),
         singleSegmentBuyXtTokenAmtOut
           daysToMaturity (s.storage 0) debtTokenAmtIn
           borrowTakerFeeRatio cutLiqSquare cutOffset)
        s := by
  by_cases hNeg : cutOffset < 0
  · simp [TermMaxOrderV2BuyXtSingleSegment.buyXt,
      TermMaxOrderV2BuyXtSingleSegment.buyToken,
      TermMaxOrderV2BuyXtSingleSegment.buyXtStep,
      TermMaxOrderV2BuyXtSingleSegment.buyXtCurve,
      TermMaxOrderV2BuyXtSingleSegment.cutsReverseIter,
      TermMaxOrderV2BuyXtSingleSegment.calcIntervalProps,
      singleSegmentBuyXtTokenAmtOut,
      singleSegmentScaledLiqSquare,
      plusInt256,
      Contracts.requireCustomError,
      Contracts.revertCustomError,
      Verity.bind,
      Bind.bind,
      Verity.pure,
      Pure.pure,
      Contract.run,
      getStorage,
      TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve,
      hNeg,
      uint256_zero_sub_toUint256_int256] at *
    rw [if_pos hNoCross]
    simp [Verity.pure]
    rw [if_pos hMinOut]
    simp [Verity.pure]
  · simp [TermMaxOrderV2BuyXtSingleSegment.buyXt,
      TermMaxOrderV2BuyXtSingleSegment.buyToken,
      TermMaxOrderV2BuyXtSingleSegment.buyXtStep,
      TermMaxOrderV2BuyXtSingleSegment.buyXtCurve,
      TermMaxOrderV2BuyXtSingleSegment.cutsReverseIter,
      TermMaxOrderV2BuyXtSingleSegment.calcIntervalProps,
      singleSegmentBuyXtTokenAmtOut,
      singleSegmentScaledLiqSquare,
      plusInt256,
      Contracts.requireCustomError,
      Contracts.revertCustomError,
      Verity.bind,
      Bind.bind,
      Verity.pure,
      Pure.pure,
      Contract.run,
      getStorage,
      TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve,
      hNeg] at *
    rw [if_pos hNoCross]
    simp [Verity.pure]
    rw [if_pos hMinOut]
    simp [Verity.pure]

@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]

@[simp] private theorem storage_setLock (slotIdx : Nat) (val : Uint256) (s : ContractState) :
    (Verity.Core.NonReentrantGuard.setLock slotIdx val s).storage = s.storage := by
  funext wordSlot
  simp [Verity.Core.NonReentrantGuard.setLock, ContractState.storage, ContractState.writeTransient]

/--
Executing the single-segment exact-input `debtToken -> XT` pricing path
updates `virtualXtReserve` (storage slot 0) by exactly the curve-computed
XT output amount.
-/
theorem swapDebtTokenToXt_updates_virtual_xt_reserve
    (daysToMaturity debtTokenAmtIn minTokenOut : Uint256)
    (borrowTakerFeeRatio lendMakerFeeRatio : Uint256)
    (cutLiqSquare : Uint256) (cutOffset : Int256)
    (s : ContractState)
    (hNonZeroInput : debtTokenAmtIn != 0)
    (hLockOpen : s.transientStorage 1 = 0)
    (hVXtNonZero : plusInt256 (s.storage 0) cutOffset != 0)
    (hNoCross :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity (s.storage 0) debtTokenAmtIn
          borrowTakerFeeRatio cutLiqSquare cutOffset
        <= s.storage 0)
    (hMinOut :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (s.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn
        >= minTokenOut) :
    let s' := ((
      TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment
        debtTokenAmtIn minTokenOut daysToMaturity
        borrowTakerFeeRatio lendMakerFeeRatio
        cutLiqSquare cutOffset
      ).run s).snd
    swapDebtTokenToXt_updates_virtual_xt_reserve_spec
      daysToMaturity debtTokenAmtIn
      borrowTakerFeeRatio cutLiqSquare cutOffset
      s s' := by
  let _ := hNonZeroInput
  let _ := hVXtNonZero
  unfold swapDebtTokenToXt_updates_virtual_xt_reserve_spec
  unfold TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment
    TermMaxOrderV2BuyXtSingleSegment.swapAndUpdateReserves
  let sLocked := Verity.Core.NonReentrantGuard.setLock 1 1 s
  have hNoCross' :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity (sLocked.storage 0) debtTokenAmtIn
          borrowTakerFeeRatio cutLiqSquare cutOffset
        <= sLocked.storage 0 := by
    simpa [sLocked] using hNoCross
  have hMinOut' :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (sLocked.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn
        >= minTokenOut := by
    simpa [sLocked] using hMinOut
  have hBuyXt :=
    buyXt_success
      daysToMaturity debtTokenAmtIn minTokenOut
      borrowTakerFeeRatio lendMakerFeeRatio
      cutLiqSquare cutOffset sLocked hNoCross' hMinOut'
  simp [Verity.Core.NonReentrantGuard.guarded, hLockOpen, Verity.bind, Bind.bind, Contract.run]
  cases hCall :
      TermMaxOrderV2BuyXtSingleSegment.buyXt
        debtTokenAmtIn minTokenOut daysToMaturity
        borrowTakerFeeRatio lendMakerFeeRatio
        cutLiqSquare cutOffset sLocked
  case success res s1 =>
    have hEq :
        ContractResult.success res s1 =
          ContractResult.success
            (add
              (singleSegmentBuyXtTokenAmtOut
                daysToMaturity (sLocked.storage 0) debtTokenAmtIn
                borrowTakerFeeRatio cutLiqSquare cutOffset)
              debtTokenAmtIn,
             sub debtTokenAmtIn
               (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                 (add 100000000 borrowTakerFeeRatio)),
             sub debtTokenAmtIn
               (sub debtTokenAmtIn
                 (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                   (add 100000000 borrowTakerFeeRatio))),
             singleSegmentBuyXtTokenAmtOut
               daysToMaturity (sLocked.storage 0) debtTokenAmtIn
               borrowTakerFeeRatio cutLiqSquare cutOffset)
            sLocked := by
      simpa [Contract.run, hCall] using hBuyXt
    injection hEq with hRes hState
    subst hRes hState
    simp [sLocked, getStorage, setStorage, Verity.pure, Pure.pure, ContractResult.snd,
      TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve]
  case _ msg s1 =>
    have hImpossible :
        ContractResult.revert msg s1 =
          ContractResult.success
            (add
              (singleSegmentBuyXtTokenAmtOut
                daysToMaturity (sLocked.storage 0) debtTokenAmtIn
                borrowTakerFeeRatio cutLiqSquare cutOffset)
              debtTokenAmtIn,
             sub debtTokenAmtIn
               (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                 (add 100000000 borrowTakerFeeRatio)),
             sub debtTokenAmtIn
               (sub debtTokenAmtIn
                 (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                   (add 100000000 borrowTakerFeeRatio))),
             singleSegmentBuyXtTokenAmtOut
               daysToMaturity (sLocked.storage 0) debtTokenAmtIn
               borrowTakerFeeRatio cutLiqSquare cutOffset)
            sLocked := by
      simp [Contract.run, hCall] at hBuyXt
    cases hImpossible

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
