import Benchmark.Cases.Polaris.BondingCurve.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Polaris.BondingCurve

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

open Verity
open Verity.EVM.Uint256

@[simp] private theorem getStorage_apply_raw (sl : StorageSlot Uint256)
    (s : ContractState) :
    getStorage sl s = ContractResult.success (s.readSlot sl.slot) s := rfl

@[simp] private theorem setStorage_apply_raw (sl : StorageSlot Uint256)
    (value : Uint256) (s : ContractState) :
    setStorage sl value s = ContractResult.success () (s.writeSlot sl.slot value) := rfl

@[simp] private theorem bind_getStorage_raw {α : Type} (sl : StorageSlot Uint256)
    (f : Uint256 → Contract α) (s : ContractState) :
    Verity.bind (getStorage sl) f s = f (s.storage sl.slot) s := rfl

@[simp] private theorem bind_setStorage_raw {α : Type} (sl : StorageSlot Uint256)
    (value : Uint256) (f : Unit → Contract α) (s : ContractState) :
    Verity.bind (setStorage sl value) f s = f () (s.writeSlot sl.slot value) := rfl

@[simp] private theorem bind_require_true_raw {α : Type} (message : String)
    (f : PUnit → Contract α) (s : ContractState) :
    Verity.bind (Verity.require true message) f s = f PUnit.unit s := rfl

@[simp] private theorem readSlot_eq_storage (s : ContractState) (slotIdx : Nat) :
    s.readSlot slotIdx = s.storage slotIdx := rfl

@[simp] private theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl

@[simp] private theorem storage_mk_storageWords_apply
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) (slotIdx : Nat) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage slotIdx =
      s.storage slotIdx := rfl

@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]

@[simp] private theorem externalResult_uint256_fromWords_singleton (w : Uint256) :
    (Contracts.ExternalResult.fromWords [w] : Uint256) = w := rfl

private def curvePowPostState (args : List Uint256) (siteId : Nat) (s : ContractState) : ContractState :=
  (Contracts.externalCallContractWordsResolved (α := Uint256) "curvePow" args Contracts.ExecutableCallContext.stub 1 siteId s).snd

@[simp] private theorem externalCallContractWordsResolved_curvePow_stub
    {α : Type} [inst : Contracts.ExternalResult α]
    (args : List Uint256) (siteId : Nat) (s : ContractState) :
    Contracts.externalCallContractWordsResolved (α := α) "curvePow" args Contracts.ExecutableCallContext.stub 1 siteId s =
      ContractResult.success (inst.fromWords [Contracts.externalCallWords "curvePow" args])
        (curvePowPostState args siteId s) := rfl

@[simp] private theorem bind_externalCallContractWordsResolved_curvePow_stub {α β : Type}
    [inst : Contracts.ExternalResult α]
    (args : List Uint256) (siteId : Nat) (f : α → Contract β) (s : ContractState) :
    Verity.bind (Contracts.externalCallContractWordsResolved (α := α) "curvePow" args Contracts.ExecutableCallContext.stub 1 siteId) f s =
      f (inst.fromWords [Contracts.externalCallWords "curvePow" args])
        (curvePowPostState args siteId s) := rfl

@[simp] private theorem storage_curvePowPostState
    (args : List Uint256) (siteId : Nat) (s : ContractState) (slotIdx : Nat) :
    (curvePowPostState args siteId s).storage slotIdx = s.storage slotIdx := rfl

private theorem virtualBalanceSlot : BaseBondingCurve.virtualBalance.slot = 0 := rfl
private theorem floorSupplySlot : BaseBondingCurve.floorSupply.slot = 1 := rfl
private theorem floorBalanceSlot : BaseBondingCurve.floorBalance.slot = 2 := rfl
private theorem totalSupplySlot : BaseBondingCurve.totalSupply.slot = 3 := rfl
private theorem feePercentageSlot : BaseBondingCurve.feePercentage.slot = 4 := rfl
private theorem initializedSlot : BaseBondingCurve.initialized.slot = 5 := rfl
private theorem alphaSlot : BaseBondingCurve.alpha.slot = 6 := rfl
private theorem bPlusOneSlot : BaseBondingCurve.bPlusOne.slot = 7 := rfl

attribute [local simp] virtualBalanceSlot floorSupplySlot floorBalanceSlot totalSupplySlot
  feePercentageSlot initializedSlot alphaSlot bPlusOneSlot

private theorem virtual_supply_after_sell_net_burn
    (floor total net : Uint256)
    (hOldSupplyNoOverflow : floor.val + total.val < Verity.Core.Uint256.modulus)
    (hNetValLeTotalSupply : net.val <= total.val) :
    add floor (sub total net) = sub (add floor total) net := by
  apply Verity.Core.Uint256.ext
  have hSubVal : (sub total net).val = total.val - net.val := by
    rw [Verity.EVM.Uint256.sub_eq_of_le hNetValLeTotalSupply]
  have hLeftNoOverflow : floor.val + (sub total net).val < Verity.Core.Uint256.modulus := by
    rw [hSubVal]
    omega
  have hNetLeOldSupply : net.val <= (add floor total).val := by
    rw [Verity.EVM.Uint256.add_eq_of_lt hOldSupplyNoOverflow]
    omega
  rw [Verity.EVM.Uint256.add_eq_of_lt hLeftNoOverflow]
  rw [hSubVal]
  rw [Verity.EVM.Uint256.sub_eq_of_le hNetLeOldSupply]
  rw [Verity.EVM.Uint256.add_eq_of_lt hOldSupplyNoOverflow]
  omega

private theorem virtual_supply_after_floor_fee_burn
    (floor total burn : Uint256)
    (hOldSupplyNoOverflow : floor.val + total.val < Verity.Core.Uint256.modulus)
    (hNewFloorNoOverflow : floor.val + burn.val < Verity.Core.Uint256.modulus)
    (hBurnValLeTotalSupply : burn.val <= total.val) :
    add (add floor burn) (sub total burn) = add floor total := by
  apply Verity.Core.Uint256.ext
  have hNewFloorVal : (add floor burn).val = floor.val + burn.val := by
    rw [Verity.EVM.Uint256.add_eq_of_lt hNewFloorNoOverflow]
  have hSubVal : (sub total burn).val = total.val - burn.val := by
    rw [Verity.EVM.Uint256.sub_eq_of_le hBurnValLeTotalSupply]
  have hRightNoOverflow :
      (add floor burn).val + (sub total burn).val < Verity.Core.Uint256.modulus := by
    rw [hNewFloorVal]
    rw [hSubVal]
    omega
  rw [Verity.EVM.Uint256.add_eq_of_lt hRightNoOverflow]
  rw [hNewFloorVal]
  rw [hSubVal]
  rw [Verity.EVM.Uint256.add_eq_of_lt hOldSupplyNoOverflow]
  omega

private theorem virtual_supply_after_init
    (virtual_ floor : Uint256)
    (hFloorValLeVirtual : floor.val <= virtual_.val) :
    add floor (sub virtual_ floor) = virtual_ := by
  apply Verity.Core.Uint256.ext
  have hSubVal : (sub virtual_ floor).val = virtual_.val - floor.val := by
    rw [Verity.EVM.Uint256.sub_eq_of_le hFloorValLeVirtual]
  have hAddNoOverflow :
      floor.val + (sub virtual_ floor).val < Verity.Core.Uint256.modulus := by
    rw [hSubVal]
    have hSumEq : floor.val + (virtual_.val - floor.val) = virtual_.val := by
      exact Nat.add_sub_of_le hFloorValLeVirtual
    rw [hSumEq]
    exact virtual_.isLt
  rw [Verity.EVM.Uint256.add_eq_of_lt hAddNoOverflow]
  rw [hSubVal]
  omega

private theorem virtual_supply_after_buy_mint
    (floor total minted : Uint256)
    (hOldSupplyNoOverflow : floor.val + total.val < Verity.Core.Uint256.modulus)
    (hSupplyMintNoOverflow :
      (add floor total).val + minted.val < Verity.Core.Uint256.modulus)
    (hTotalSupplyMintNoOverflow :
      total.val + minted.val < Verity.Core.Uint256.modulus) :
    add floor (add total minted) = add (add floor total) minted := by
  apply Verity.Core.Uint256.ext
  have hOldSupplyVal : (add floor total).val = floor.val + total.val := by
    rw [Verity.EVM.Uint256.add_eq_of_lt hOldSupplyNoOverflow]
  have hTotalMintVal : (add total minted).val = total.val + minted.val := by
    rw [Verity.EVM.Uint256.add_eq_of_lt hTotalSupplyMintNoOverflow]
  have hLeftNoOverflow :
      floor.val + (add total minted).val < Verity.Core.Uint256.modulus := by
    rw [hTotalMintVal]
    omega
  rw [Verity.EVM.Uint256.add_eq_of_lt hLeftNoOverflow]
  rw [hTotalMintVal]
  rw [Verity.EVM.Uint256.add_eq_of_lt hSupplyMintNoOverflow]
  rw [hOldSupplyVal]
  omega

private theorem init_slot_writes
    (virtualSupply_ floorSupply_ : Uint256)
    (s : ContractState)
    (hFloorNonZero : floorSupply_ != 0)
    (hFloorLeVirtual : floorSupply_ <= virtualSupply_) :
    let s' :=
      ((BaseBondingCurve.init virtualSupply_ floorSupply_).run s).snd
    virtualBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s) virtualSupply_ ∧
    floorSupplyOf s' = floorSupply_ ∧
    floorBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s) floorSupply_ ∧
    totalSupplyOf s' = sub virtualSupply_ floorSupply_ ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hFloorLeVirtualBool : decide (floorSupply_ <= virtualSupply_) = true :=
    decide_eq_true hFloorLeVirtual
  have hStorage (slotIdx : Nat) :
      (((BaseBondingCurve.init virtualSupply_ floorSupply_).run s).snd).storage slotIdx =
        if slotIdx == 5 then 1
        else if slotIdx == 3 then sub virtualSupply_ floorSupply_
        else if slotIdx == 2 then
          div (sub (add (mul (s.storage 6) (Contracts.externalCallWords "curvePow" [floorSupply_, s.storage 7])) 1000000000000000000) 1) (s.storage 7)
        else if slotIdx == 1 then floorSupply_
        else if slotIdx == 0 then
          div (sub (add (mul (s.storage 6) (Contracts.externalCallWords "curvePow" [virtualSupply_, s.storage 7])) 1000000000000000000) 1) (s.storage 7)
        else s.storage slotIdx := by
    dsimp only [BaseBondingCurve.init, BaseBondingCurveExec.init, Contract.run, Bind.bind]
    rw [hFloorNonZero, bind_require_true_raw,
      hFloorLeVirtualBool, bind_require_true_raw,
      bind_getStorage_raw, bind_getStorage_raw,
      bind_externalCallContractWordsResolved_curvePow_stub,
      bind_externalCallContractWordsResolved_curvePow_stub,
      bind_setStorage_raw, bind_setStorage_raw, bind_setStorage_raw,
      bind_setStorage_raw, setStorage_apply_raw]
    dsimp only [ContractResult.snd,
      virtualBalanceSlot, floorSupplySlot, floorBalanceSlot, totalSupplySlot,
      initializedSlot, alphaSlot, bPlusOneSlot]
    simp only [readSlot_eq_storage, externalResult_uint256_fromWords_singleton,
      storage_writeSlot, storage_curvePowPostState]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [virtualBalanceOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision, curvePow, alphaOf, bPlusOneOf] using hStorage 0
  · simpa [floorSupplyOf] using hStorage 1
  · simpa [floorBalanceOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision, curvePow, alphaOf, bPlusOneOf] using hStorage 2
  · simpa [totalSupplyOf] using hStorage 3
  · simpa [alphaOf] using hStorage 6
  · simpa [bPlusOneOf] using hStorage 7

private theorem buy_slot_writes
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount : Uint256)
    (s : ContractState)
    (hInitialized : initializedOf s = 1)
    (hAmountNonZero : bcTokenAmount != 0) :
    let s' :=
      ((BaseBondingCurve.buy
        isFeeRouter bcTokenAmount buyFeeAmount).run s).snd
    virtualBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s)
        (add (add (floorSupplyOf s) (totalSupplyOf s))
          (add bcTokenAmount buyFeeAmount)) ∧
    floorSupplyOf s' = floorSupplyOf s ∧
    floorBalanceOf s' = floorBalanceOf s ∧
    totalSupplyOf s' = add (totalSupplyOf s) (add bcTokenAmount buyFeeAmount) ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hInitialized' : s.storage 5 = 1 := by
    simpa [initializedOf] using hInitialized
  have hStorage (slotIdx : Nat) :
      (((BaseBondingCurve.buy isFeeRouter bcTokenAmount buyFeeAmount).run s).snd).storage slotIdx =
        if slotIdx == 3 then add (s.storage 3) (add bcTokenAmount buyFeeAmount)
        else if slotIdx == 0 then
          div (sub (add (mul (s.storage 6) (Contracts.externalCallWords "curvePow"
            [add (add (s.storage 1) (s.storage 3)) (add bcTokenAmount buyFeeAmount), s.storage 7])) 1000000000000000000) 1) (s.storage 7)
        else s.storage slotIdx := by
    dsimp only [BaseBondingCurve.buy, BaseBondingCurveExec.buy, Contract.run, Bind.bind]
    rw [bind_getStorage_raw, initializedSlot, hInitialized',
      beq_self_eq_true, bind_require_true_raw, hAmountNonZero, bind_require_true_raw,
      bind_getStorage_raw, bind_getStorage_raw, bind_getStorage_raw, bind_getStorage_raw,
      bind_externalCallContractWordsResolved_curvePow_stub,
      bind_setStorage_raw, setStorage_apply_raw]
    dsimp only [ContractResult.snd,
      virtualBalanceSlot, floorSupplySlot, totalSupplySlot, alphaSlot, bPlusOneSlot]
    simp only [readSlot_eq_storage, externalResult_uint256_fromWords_singleton,
      storage_writeSlot, storage_curvePowPostState]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [virtualBalanceOf, floorSupplyOf, totalSupplyOf, alphaOf, bPlusOneOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision, curvePow] using hStorage 0
  · simpa [floorSupplyOf] using hStorage 1
  · simpa [floorBalanceOf] using hStorage 2
  · simpa [totalSupplyOf] using hStorage 3
  · simpa [alphaOf] using hStorage 6
  · simpa [bPlusOneOf] using hStorage 7

private theorem sell_slot_writes
    (bcTokenAmount : Uint256) (s : ContractState)
    (hNetAmountNonZero : sellNetBurnAmount bcTokenAmount s != 0)
    (hNetLeOldSupply : sellNetBurnAmount bcTokenAmount s <= virtualSupplyOf s)
    (hNetLeTotalSupply : sellNetBurnAmount bcTokenAmount s <= totalSupplyOf s) :
    let s' := ((BaseBondingCurve.sell bcTokenAmount).run s).snd
    virtualBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s)
        (sellVirtualSupplyAfter bcTokenAmount s) ∧
    floorSupplyOf s' = floorSupplyOf s ∧
    floorBalanceOf s' = floorBalanceOf s ∧
    totalSupplyOf s' = sub (totalSupplyOf s) (sellNetBurnAmount bcTokenAmount s) ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hNetNonZero' :
      (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000) != 0) = true := by
    simpa [sellNetBurnAmount, sellFeeAmount, feePercentageOf, decimalPrecision] using hNetAmountNonZero
  have hNetLeOldSupplyBool :
      decide (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000) <=
        add (s.storage 1) (s.storage 3)) = true := by
    apply decide_eq_true
    simpa [sellNetBurnAmount, sellFeeAmount, feePercentageOf, virtualSupplyOf,
      floorSupplyOf, totalSupplyOf, decimalPrecision] using hNetLeOldSupply
  have hNetLeTotalSupplyBool :
      decide (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000) <=
        s.storage 3) = true := by
    apply decide_eq_true
    simpa [sellNetBurnAmount, sellFeeAmount, feePercentageOf, totalSupplyOf,
      decimalPrecision] using hNetLeTotalSupply
  have hStorage (slotIdx : Nat) :
      (((BaseBondingCurve.sell bcTokenAmount).run s).snd).storage slotIdx =
        if slotIdx == 3 then
          sub (s.storage 3) (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000))
        else if slotIdx == 0 then
          div (sub (add (mul (s.storage 6) (Contracts.externalCallWords "curvePow"
            [sub (add (s.storage 1) (s.storage 3)) (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000)), s.storage 7])) 1000000000000000000) 1) (s.storage 7)
        else s.storage slotIdx := by
    dsimp only [BaseBondingCurve.sell, BaseBondingCurveExec.sell, Contract.run, Bind.bind]
    rw [bind_getStorage_raw, bind_getStorage_raw, bind_getStorage_raw,
      bind_getStorage_raw, bind_getStorage_raw,
      feePercentageSlot, floorSupplySlot, totalSupplySlot, alphaSlot, bPlusOneSlot,
      hNetNonZero', bind_require_true_raw,
      hNetLeOldSupplyBool, bind_require_true_raw,
      hNetLeTotalSupplyBool, bind_require_true_raw,
      bind_externalCallContractWordsResolved_curvePow_stub,
      bind_setStorage_raw, setStorage_apply_raw]
    dsimp only [ContractResult.snd, virtualBalanceSlot, totalSupplySlot]
    simp only [readSlot_eq_storage, externalResult_uint256_fromWords_singleton,
      storage_writeSlot, storage_curvePowPostState]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [virtualBalanceOf, sellVirtualSupplyAfter, virtualSupplyOf, floorSupplyOf, totalSupplyOf, sellNetBurnAmount, sellFeeAmount, feePercentageOf, alphaOf, bPlusOneOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision, curvePow] using hStorage 0
  · simpa [floorSupplyOf] using hStorage 1
  · simpa [floorBalanceOf] using hStorage 2
  · simpa [totalSupplyOf, sellNetBurnAmount, sellFeeAmount, feePercentageOf, decimalPrecision] using hStorage 3
  · simpa [alphaOf] using hStorage 6
  · simpa [bPlusOneOf] using hStorage 7

private theorem floor_sell_and_burn_slot_writes
    (authorizedFeeRouter : Bool) (bcTokenAmount : Uint256)
    (s : ContractState)
    (hAuthorized : authorizedFeeRouter = true)
    (hAmountNonZero : bcTokenAmount != 0)
    (hNewFloorLeOldSupply :
      floorSupplyAfterFeeBurn bcTokenAmount s <= virtualSupplyOf s)
    (hBurnLeTotalSupply : bcTokenAmount <= totalSupplyOf s) :
    let s' :=
      ((BaseBondingCurve.floorSellAndBurn
        authorizedFeeRouter bcTokenAmount).run s).snd
    virtualBalanceOf s' = virtualBalanceOf s ∧
    floorSupplyOf s' = floorSupplyAfterFeeBurn bcTokenAmount s ∧
    floorBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s)
        (floorSupplyAfterFeeBurn bcTokenAmount s) ∧
    totalSupplyOf s' = totalSupplyAfterFeeBurn bcTokenAmount s ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hNewFloorLeOldSupplyBool :
      decide (add (s.storage 1) bcTokenAmount <= add (s.storage 1) (s.storage 3)) = true := by
    apply decide_eq_true
    simpa [floorSupplyAfterFeeBurn, virtualSupplyOf, floorSupplyOf, totalSupplyOf]
      using hNewFloorLeOldSupply
  have hBurnLeTotalSupplyBool :
      decide (bcTokenAmount <= s.storage 3) = true := by
    apply decide_eq_true
    simpa [totalSupplyOf] using hBurnLeTotalSupply
  have hStorage (slotIdx : Nat) :
      (((BaseBondingCurve.floorSellAndBurn authorizedFeeRouter bcTokenAmount).run s).snd).storage slotIdx =
        if slotIdx == 3 then sub (s.storage 3) bcTokenAmount
        else if slotIdx == 2 then
          div (sub (add (mul (s.storage 6) (Contracts.externalCallWords "curvePow"
            [add (s.storage 1) bcTokenAmount, s.storage 7])) 1000000000000000000) 1) (s.storage 7)
        else if slotIdx == 1 then add (s.storage 1) bcTokenAmount
        else s.storage slotIdx := by
    dsimp only [BaseBondingCurve.floorSellAndBurn, BaseBondingCurveExec.floorSellAndBurn,
      Contract.run, Bind.bind]
    rw [hAuthorized, bind_require_true_raw,
      hAmountNonZero, bind_require_true_raw,
      bind_getStorage_raw, bind_getStorage_raw, bind_getStorage_raw, bind_getStorage_raw,
      floorSupplySlot, totalSupplySlot, alphaSlot, bPlusOneSlot,
      hNewFloorLeOldSupplyBool, bind_require_true_raw,
      hBurnLeTotalSupplyBool, bind_require_true_raw,
      bind_externalCallContractWordsResolved_curvePow_stub,
      bind_setStorage_raw, bind_setStorage_raw, setStorage_apply_raw]
    dsimp only [ContractResult.snd, floorSupplySlot, floorBalanceSlot, totalSupplySlot]
    simp only [readSlot_eq_storage, externalResult_uint256_fromWords_singleton,
      storage_writeSlot, storage_curvePowPostState]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [virtualBalanceOf] using hStorage 0
  · simpa [floorSupplyOf, floorSupplyAfterFeeBurn] using hStorage 1
  · simpa [floorBalanceOf, floorSupplyAfterFeeBurn, floorSupplyOf, alphaOf, bPlusOneOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision, curvePow] using hStorage 2
  · simpa [totalSupplyOf, totalSupplyAfterFeeBurn] using hStorage 3
  · simpa [alphaOf] using hStorage 6
  · simpa [bPlusOneOf] using hStorage 7

/--
  Successful initialization establishes zero reserve-ratio deviation.

  The executable model computes and writes the two helper balances to the current and
  floor reserve slots, and the local arithmetic lemma proves the post-state
  virtual supply is the requested virtual supply. If `floorSupply_ != 0`,
  `floorSupply_ <= virtualSupply_`, and Solidity checked arithmetic succeeds,
  then `init` writes:
  - `virtualBalance = getBalanceFromReserveRatio A B_PLUS_1 virtualSupply_`
  - `floorBalance = getBalanceFromReserveRatio A B_PLUS_1 floorSupply_`
  - `totalSupply = virtualSupply_ - floorSupply_`

  This is exactly the source sequence in `BaseBondingCurve.init`, with only the
  imported PRB/ABDK fixed-point exponentiation abstracted by `curvePow`.
-/
theorem init_reserve_ratio_zero
    (virtualSupply_ floorSupply_ : Uint256)
    (s : ContractState)
    (hFloorNonZero : floorSupply_ != 0)
    (hFloorLeVirtual : floorSupply_ <= virtualSupply_) :
    let s' :=
      ((BaseBondingCurve.init virtualSupply_ floorSupply_).run s).snd
    init_reserve_ratio_zero_spec s s' := by
  dsimp [init_reserve_ratio_zero_spec]
  let s' := ((BaseBondingCurve.init virtualSupply_ floorSupply_).run s).snd
  change reserveRatioDeviationZero s'
  dsimp [reserveRatioDeviationZero, currentReserveRatioDeviationZero,
    floorReserveRatioDeviationZero]
  have hFloorLeVirtualVal : floorSupply_.val <= virtualSupply_.val := by
    simpa [Verity.Core.Uint256.le_def] using hFloorLeVirtual
  have hw := init_slot_writes
    virtualSupply_ floorSupply_ s hFloorNonZero hFloorLeVirtual
  rcases hw with
    ⟨hVirtualBalance, hFloorSupply, hFloorBalance, hTotalSupply, hAlpha, hBPlusOne⟩
  constructor
  · rw [hVirtualBalance]
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    congr 1
    dsimp [virtualSupplyOf]
    rw [hFloorSupply, hTotalSupply]
    exact (virtual_supply_after_init virtualSupply_ floorSupply_
      hFloorLeVirtualVal).symm
  · rw [hFloorBalance, hFloorSupply]
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]

/--
  Successful `buy` preserves zero reserve-ratio deviation.

  On the initialized successful path, with the nonzero amount guard satisfied
  and no overflow in the source-level supply additions, `buy` increases
  aggregate pETH supply by the requested net amount plus the pETH fee and
  writes `virtualBalance` to the curve balance of the resulting
  `virtualSupply`. `floorSupply` and `floorBalance` are unchanged.

  The caller branch is carried by the supplied `buyFeeAmount` hypothesis. The
  storage-alignment invariant itself only needs the resulting minted amount.
-/
theorem buy_preserves_reserve_ratio_zero
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount : Uint256)
    (s : ContractState)
    (hInitialized : initializedOf s = 1)
    (hAmountNonZero : bcTokenAmount != 0)
    (_hFeeAmount :
      buyFeeAmount =
        if isFeeRouter then
          0
        else
          div (mul bcTokenAmount (feePercentageOf s)) (sub decimalPrecision (feePercentageOf s)))
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (_hMintNoOverflow :
      bcTokenAmount.val + buyFeeAmount.val < Verity.Core.Uint256.modulus)
    (hSupplyMintNoOverflow :
      (add (floorSupplyOf s) (totalSupplyOf s)).val +
        (add bcTokenAmount buyFeeAmount).val <
          Verity.Core.Uint256.modulus)
    (hTotalSupplyMintNoOverflow :
      (totalSupplyOf s).val +
        (add bcTokenAmount buyFeeAmount).val <
          Verity.Core.Uint256.modulus) :
    let s' :=
      ((BaseBondingCurve.buy
        isFeeRouter bcTokenAmount buyFeeAmount).run s).snd
    buy_preserves_reserve_ratio_zero_spec s s' := by
  dsimp [buy_preserves_reserve_ratio_zero_spec]
  intro hInv
  let s' := ((BaseBondingCurve.buy isFeeRouter bcTokenAmount buyFeeAmount).run s).snd
  change reserveRatioDeviationZero s'
  rcases hInv with ⟨_hCurrent, hFloor⟩
  dsimp [reserveRatioDeviationZero, currentReserveRatioDeviationZero,
    floorReserveRatioDeviationZero]
  have hw := buy_slot_writes
    isFeeRouter bcTokenAmount buyFeeAmount s hInitialized hAmountNonZero
  rcases hw with
    ⟨hVirtualBalance, hFloorSupply, hFloorBalance, hTotalSupply, hAlpha, hBPlusOne⟩
  constructor
  · rw [hVirtualBalance]
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    congr 1
    dsimp [virtualSupplyOf]
    rw [hFloorSupply, hTotalSupply]
    exact (virtual_supply_after_buy_mint
      (floorSupplyOf s) (totalSupplyOf s) (add bcTokenAmount buyFeeAmount)
      hOldSupplyNoOverflow hSupplyMintNoOverflow
      hTotalSupplyMintNoOverflow).symm
  · rw [hFloorBalance, hFloorSupply]
    dsimp [floorReserveRatioDeviationZero, curveBalanceAt] at hFloor
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    exact hFloor

/-!
  Trusted assumptions retained below:
  - bounded Uint256 arithmetic for the source-level checked operations.

  `curvePow` remains the linked external boundary for the imported PRB/ABDK
  fixed-point pow implementation used by `_getBalanceFromReserveRatio`; it is
  no longer a per-transition assumption or supplied witness.
-/

/--
  Successful `sell` preserves current and floor reserve-ratio alignment.

  The theorem no longer assumes the post-reserve equality. The executable model
  writes `virtualBalance` to the modeled helper result for the post-sell virtual
  supply, and the arithmetic lemma `virtual_supply_after_sell_net_burn` proves
  that the stored post-state supply is the same full supply point.
-/
theorem sell_preserves_reserve_ratio_zero
    (bcTokenAmount : Uint256) (s : ContractState)
    (hNetAmountNonZero : sellNetBurnAmount bcTokenAmount s != 0)
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hNetLeOldSupply : sellNetBurnAmount bcTokenAmount s <= virtualSupplyOf s)
    (hNetLeTotalSupply : sellNetBurnAmount bcTokenAmount s <= totalSupplyOf s)
    (hNetValLeTotalSupply :
      (sellNetBurnAmount bcTokenAmount s).val <= (totalSupplyOf s).val) :
    let s' := ((BaseBondingCurve.sell bcTokenAmount).run s).snd
    sell_preserves_reserve_ratio_zero_spec s s' := by
  dsimp [sell_preserves_reserve_ratio_zero_spec]
  intro hInv
  let s' := ((BaseBondingCurve.sell bcTokenAmount).run s).snd
  change reserveRatioDeviationZero s'
  rcases hInv with ⟨hCurrent, hFloor⟩
  dsimp [reserveRatioDeviationZero,
    currentReserveRatioDeviationZero, floorReserveRatioDeviationZero]
  have hw := sell_slot_writes bcTokenAmount s
    hNetAmountNonZero hNetLeOldSupply hNetLeTotalSupply
  rcases hw with
    ⟨hVirtualBalance, hFloorSupply, hFloorBalance, hTotalSupply, hAlpha, hBPlusOne⟩
  constructor
  · dsimp [virtualSupplyOf]
    rw [hVirtualBalance]
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    congr 1
    dsimp [sellVirtualSupplyAfter, virtualSupplyOf]
    rw [hFloorSupply, hTotalSupply]
    exact (virtual_supply_after_sell_net_burn
      (floorSupplyOf s) (totalSupplyOf s) (sellNetBurnAmount bcTokenAmount s)
      hOldSupplyNoOverflow hNetValLeTotalSupply).symm
  · rw [hFloorBalance, hFloorSupply]
    dsimp [floorReserveRatioDeviationZero, curveBalanceAt] at hFloor
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    exact hFloor

/--
  Successful `floorSellAndBurn` preserves both reserve-ratio equations.

  This is the source transition that makes fee burns explicit: aggregate
  `totalSupply` decreases by the burned fee-router pETH, `floorSupply`
  increases by the same amount, and `floorBalance` is written to the curve at
  the new floor supply. The current virtual supply is unchanged after the full
  supply change, which is proved by `virtual_supply_after_floor_fee_burn`.
-/
theorem floorSellAndBurn_preserves_reserve_ratio_zero
    (authorizedFeeRouter : Bool) (bcTokenAmount : Uint256)
    (s : ContractState)
    (hAuthorized : authorizedFeeRouter = true)
    (hAmountNonZero : bcTokenAmount != 0)
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hNewFloorNoOverflow :
      (floorSupplyOf s).val + bcTokenAmount.val < Verity.Core.Uint256.modulus)
    (hNewFloorLeOldSupply :
      floorSupplyAfterFeeBurn bcTokenAmount s <= virtualSupplyOf s)
    (hBurnLeTotalSupply : bcTokenAmount <= totalSupplyOf s)
    (hBurnValLeTotalSupply : bcTokenAmount.val <= (totalSupplyOf s).val) :
    let s' :=
      ((BaseBondingCurve.floorSellAndBurn
        authorizedFeeRouter bcTokenAmount).run s).snd
    floorSellAndBurn_preserves_reserve_ratio_zero_spec s s' := by
  dsimp [floorSellAndBurn_preserves_reserve_ratio_zero_spec]
  intro hInv
  let s' :=
    ((BaseBondingCurve.floorSellAndBurn
      authorizedFeeRouter bcTokenAmount).run s).snd
  change reserveRatioDeviationZero s'
  rcases hInv with ⟨hCurrent, _hFloor⟩
  dsimp [reserveRatioDeviationZero, currentReserveRatioDeviationZero,
    floorReserveRatioDeviationZero]
  have hw := floor_sell_and_burn_slot_writes
    authorizedFeeRouter bcTokenAmount s
    hAuthorized hAmountNonZero hNewFloorLeOldSupply hBurnLeTotalSupply
  rcases hw with
    ⟨hVirtualBalance, hFloorSupply, hFloorBalance, hTotalSupply, hAlpha, hBPlusOne⟩
  constructor
  · rw [hVirtualBalance]
    dsimp [currentReserveRatioDeviationZero, curveBalanceAt] at hCurrent
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    rw [hCurrent]
    congr 1
    dsimp [virtualSupplyOf]
    rw [hFloorSupply, hTotalSupply]
    exact (virtual_supply_after_floor_fee_burn
      (floorSupplyOf s) (totalSupplyOf s) bcTokenAmount
      hOldSupplyNoOverflow hNewFloorNoOverflow hBurnValLeTotalSupply).symm
  · rw [hFloorBalance]
    dsimp [curveBalanceAt]
    rw [hAlpha, hBPlusOne]
    congr 1
    exact hFloorSupply.symm

end Benchmark.Cases.Polaris.BondingCurve
