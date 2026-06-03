import Benchmark.Cases.Polaris.BondingCurve.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Polaris.BondingCurve

open Verity
open Verity.EVM.Uint256

private theorem virtual_supply_after_sell_net_burn
    (floor total net : Uint256)
    (hOldSupplyNoOverflow : floor.val + total.val < Verity.Core.Uint256.modulus)
    (hNetValLeTotalSupply : net.val <= total.val) :
    add floor (sub total net) = sub (add floor total) net := by
  apply Verity.Core.Uint256.ext
  change (add floor (sub total net)).val = (sub (add floor total) net).val
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
  change (add (add floor burn) (sub total burn)).val = (add floor total).val
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
    (virtual floor : Uint256)
    (hFloorValLeVirtual : floor.val <= virtual.val) :
    add floor (sub virtual floor) = virtual := by
  apply Verity.Core.Uint256.ext
  change (add floor (sub virtual floor)).val = virtual.val
  have hSubVal : (sub virtual floor).val = virtual.val - floor.val := by
    rw [Verity.EVM.Uint256.sub_eq_of_le hFloorValLeVirtual]
  have hAddNoOverflow :
      floor.val + (sub virtual floor).val < Verity.Core.Uint256.modulus := by
    rw [hSubVal]
    have hSumEq : floor.val + (virtual.val - floor.val) = virtual.val := by
      exact Nat.add_sub_of_le hFloorValLeVirtual
    rw [hSumEq]
    exact virtual.isLt
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
  change (add floor (add total minted)).val = (add (add floor total) minted).val
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
    (virtualSupply_ floorSupply_ computedVirtualPow computedFloorPow : Uint256)
    (s : ContractState)
    (hFloorNonZero : floorSupply_ != 0)
    (hFloorLeVirtual : floorSupply_ <= virtualSupply_)
    (hComputedVirtualPow : computedVirtualPow = curvePow virtualSupply_ (bPlusOneOf s))
    (hComputedFloorPow : computedFloorPow = curvePow floorSupply_ (bPlusOneOf s)) :
    let s' :=
      ((BaseBondingCurve.init
        virtualSupply_ floorSupply_ computedVirtualPow computedFloorPow).run s).snd
    virtualBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s) virtualSupply_ ∧
    floorSupplyOf s' = floorSupply_ ∧
    floorBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s) floorSupply_ ∧
    totalSupplyOf s' = sub virtualSupply_ floorSupply_ ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hFloorNeZero : floorSupply_ ≠ 0 := by
    intro h
    simp [h] at hFloorNonZero
  have hFloorLeVirtualVal : floorSupply_.val <= virtualSupply_.val := by
    simpa [Verity.Core.Uint256.le_def] using hFloorLeVirtual
  repeat' constructor
  all_goals
    simp [BaseBondingCurve.init, virtualBalanceOf, floorSupplyOf, floorBalanceOf,
      totalSupplyOf, BaseBondingCurve.virtualBalance, BaseBondingCurve.floorSupply,
      BaseBondingCurve.floorBalance, BaseBondingCurve.totalSupply,
      BaseBondingCurve.initialized, BaseBondingCurve.alpha, BaseBondingCurve.bPlusOne,
      alphaOf, bPlusOneOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision,
      hComputedVirtualPow, hComputedFloorPow, hFloorNeZero, hFloorLeVirtualVal,
      setStorage, Verity.require, Verity.bind, Bind.bind,
      getStorage, Contract.run, ContractResult.snd]

private theorem buy_slot_writes
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount computedNewVirtualPow : Uint256)
    (s : ContractState)
    (hInitialized : initializedOf s = 1)
    (hAmountNonZero : bcTokenAmount != 0)
    (hComputedNewVirtualPow :
      computedNewVirtualPow =
        curvePow
          (add (add (floorSupplyOf s) (totalSupplyOf s))
            (add bcTokenAmount buyFeeAmount))
          (bPlusOneOf s)) :
    let s' :=
      ((BaseBondingCurve.buy
        isFeeRouter bcTokenAmount buyFeeAmount computedNewVirtualPow).run s).snd
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
  have hAmountNeZero : bcTokenAmount ≠ 0 := by
    intro h
    simp [h] at hAmountNonZero
  repeat' constructor
  all_goals
    simp [BaseBondingCurve.buy, virtualBalanceOf, floorSupplyOf, floorBalanceOf,
      totalSupplyOf, alphaOf, bPlusOneOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision,
      BaseBondingCurve.virtualBalance, BaseBondingCurve.floorSupply,
      BaseBondingCurve.totalSupply, BaseBondingCurve.alpha, BaseBondingCurve.bPlusOne,
      BaseBondingCurve.initialized,
      hComputedNewVirtualPow, hInitialized', hAmountNeZero, getStorage, setStorage, Verity.require,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem sell_slot_writes
    (bcTokenAmount computedNewVirtualPow : Uint256) (s : ContractState)
    (hNetAmountNonZero : sellNetBurnAmount bcTokenAmount s != 0)
    (hNetLeOldSupply : sellNetBurnAmount bcTokenAmount s <= virtualSupplyOf s)
    (hNetLeTotalSupply : sellNetBurnAmount bcTokenAmount s <= totalSupplyOf s)
    (hComputedNewVirtualPow :
      computedNewVirtualPow =
        curvePow (sellVirtualSupplyAfter bcTokenAmount s) (bPlusOneOf s)) :
    let s' := ((BaseBondingCurve.sell bcTokenAmount computedNewVirtualPow).run s).snd
    virtualBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s)
        (sellVirtualSupplyAfter bcTokenAmount s) ∧
    floorSupplyOf s' = floorSupplyOf s ∧
    floorBalanceOf s' = floorBalanceOf s ∧
    totalSupplyOf s' = sub (totalSupplyOf s) (sellNetBurnAmount bcTokenAmount s) ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hNetNeZero : sellNetBurnAmount bcTokenAmount s ≠ 0 := by
    intro h
    simp [h] at hNetAmountNonZero
  have hNetNeZero' :
      sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000) ≠ 0 := by
    simpa [sellNetBurnAmount, sellFeeAmount, feePercentageOf, decimalPrecision] using hNetNeZero
  have hNetLeOldSupplyVal :
      (sellNetBurnAmount bcTokenAmount s).val <= (virtualSupplyOf s).val := by
    simpa [Verity.Core.Uint256.le_def] using hNetLeOldSupply
  have hNetLeOldSupplyVal' :
      (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000)).val <=
        (add (s.storage 1) (s.storage 3)).val := by
    simpa [sellNetBurnAmount, sellFeeAmount, feePercentageOf, virtualSupplyOf,
      floorSupplyOf, totalSupplyOf, decimalPrecision] using hNetLeOldSupplyVal
  have hNetLeTotalSupplyVal :
      (sellNetBurnAmount bcTokenAmount s).val <= (totalSupplyOf s).val := by
    simpa [Verity.Core.Uint256.le_def] using hNetLeTotalSupply
  have hNetLeTotalSupplyVal' :
      (sub bcTokenAmount (div (mul bcTokenAmount (s.storage 4)) 1000000000000000000)).val <=
        (s.storage 3).val := by
    simpa [sellNetBurnAmount, sellFeeAmount, feePercentageOf, totalSupplyOf,
      decimalPrecision] using hNetLeTotalSupplyVal
  repeat' constructor
  all_goals
    simp [BaseBondingCurve.sell, sellNetBurnAmount,
      sellFeeAmount, virtualBalanceOf, floorSupplyOf,
      floorBalanceOf, totalSupplyOf, feePercentageOf, alphaOf, bPlusOneOf,
      getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision, sellVirtualSupplyAfter,
      BaseBondingCurve.virtualBalance, BaseBondingCurve.floorSupply,
      BaseBondingCurve.totalSupply, BaseBondingCurve.feePercentage,
      BaseBondingCurve.alpha, BaseBondingCurve.bPlusOne,
      decimalPrecision, hComputedNewVirtualPow, hNetNeZero',
      hNetLeOldSupplyVal', hNetLeTotalSupplyVal', getStorage, setStorage, Verity.require,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem floor_sell_and_burn_slot_writes
    (authorizedFeeRouter : Bool) (bcTokenAmount computedNewFloorPow : Uint256)
    (s : ContractState)
    (hAuthorized : authorizedFeeRouter = true)
    (hAmountNonZero : bcTokenAmount != 0)
    (hNewFloorLeOldSupply :
      floorSupplyAfterFeeBurn bcTokenAmount s <= virtualSupplyOf s)
    (hBurnLeTotalSupply : bcTokenAmount <= totalSupplyOf s)
    (hComputedNewFloorPow :
      computedNewFloorPow =
        curvePow (floorSupplyAfterFeeBurn bcTokenAmount s) (bPlusOneOf s)) :
    let s' :=
      ((BaseBondingCurve.floorSellAndBurn
        authorizedFeeRouter bcTokenAmount computedNewFloorPow).run s).snd
    virtualBalanceOf s' = virtualBalanceOf s ∧
    floorSupplyOf s' = floorSupplyAfterFeeBurn bcTokenAmount s ∧
    floorBalanceOf s' =
      getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s)
        (floorSupplyAfterFeeBurn bcTokenAmount s) ∧
    totalSupplyOf s' = totalSupplyAfterFeeBurn bcTokenAmount s ∧
    alphaOf s' = alphaOf s ∧
    bPlusOneOf s' = bPlusOneOf s := by
  have hAuthorizedTrue : authorizedFeeRouter = true := hAuthorized
  have hAmountNeZero : bcTokenAmount ≠ 0 := by
    intro h
    simp [h] at hAmountNonZero
  have hNewFloorLeOldSupplyVal :
      (floorSupplyAfterFeeBurn bcTokenAmount s).val <= (virtualSupplyOf s).val := by
    simpa [Verity.Core.Uint256.le_def] using hNewFloorLeOldSupply
  have hNewFloorLeOldSupplyVal' :
      (add (s.storage 1) bcTokenAmount).val <= (add (s.storage 1) (s.storage 3)).val := by
    simpa [floorSupplyAfterFeeBurn, virtualSupplyOf, floorSupplyOf, totalSupplyOf]
      using hNewFloorLeOldSupplyVal
  have hBurnLeTotalSupplyVal : bcTokenAmount.val <= (totalSupplyOf s).val := by
    simpa [Verity.Core.Uint256.le_def] using hBurnLeTotalSupply
  have hBurnLeTotalSupplyVal' : bcTokenAmount.val <= (s.storage 3).val := by
    simpa [totalSupplyOf] using hBurnLeTotalSupplyVal
  repeat' constructor
  all_goals
    simp [BaseBondingCurve.floorSellAndBurn, floorSupplyAfterFeeBurn,
      totalSupplyAfterFeeBurn, virtualBalanceOf,
      floorSupplyOf, floorBalanceOf, totalSupplyOf,
      alphaOf, bPlusOneOf, getBalanceFromReserveRatio, reserveRatioBalanceFromLeft, decimalPrecision,
      BaseBondingCurve.floorSupply, BaseBondingCurve.floorBalance, BaseBondingCurve.totalSupply,
      BaseBondingCurve.alpha, BaseBondingCurve.bPlusOne,
      hComputedNewFloorPow, hAuthorizedTrue, hAmountNeZero, hNewFloorLeOldSupplyVal',
      hBurnLeTotalSupplyVal', getStorage, setStorage, Verity.require,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

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

  This is exactly the source sequence in `BaseBondingCurve.init`, modulo the
  documented `curvePow` boundary for PRB/ABDK fixed-point exponentiation.
-/
theorem init_reserve_ratio_zero
    (virtualSupply_ floorSupply_ computedVirtualPow computedFloorPow : Uint256)
    (s : ContractState)
    (hFloorNonZero : floorSupply_ != 0)
    (hFloorLeVirtual : floorSupply_ <= virtualSupply_)
    (hComputedVirtualPow :
      trustedCurvePowOutput s virtualSupply_ computedVirtualPow)
    (hComputedFloorPow :
      trustedCurvePowOutput s floorSupply_ computedFloorPow) :
    let s' :=
      ((BaseBondingCurve.init
        virtualSupply_ floorSupply_ computedVirtualPow computedFloorPow).run s).snd
    init_reserve_ratio_zero_spec s s' := by
  dsimp [init_reserve_ratio_zero_spec]
  let s' :=
    ((BaseBondingCurve.init
      virtualSupply_ floorSupply_ computedVirtualPow computedFloorPow).run s).snd
  change reserveRatioDeviationZero s'
  dsimp [reserveRatioDeviationZero, currentReserveRatioDeviationZero,
    floorReserveRatioDeviationZero]
  have hFloorLeVirtualVal : floorSupply_.val <= virtualSupply_.val := by
    simpa [Verity.Core.Uint256.le_def] using hFloorLeVirtual
  have hw := init_slot_writes
    virtualSupply_ floorSupply_ computedVirtualPow computedFloorPow s
    hFloorNonZero hFloorLeVirtual
    (by simpa [trustedCurvePowOutput] using hComputedVirtualPow)
    (by simpa [trustedCurvePowOutput] using hComputedFloorPow)
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

  This matches `BaseBondingCurve.buy`: callers other than the fee router mint fee
  tokens to the fee router, while the fee-router path pays no fee.
-/
theorem buy_preserves_reserve_ratio_zero
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount computedNewVirtualPow : Uint256)
    (s : ContractState)
    (hInitialized : initializedOf s = 1)
    (hAmountNonZero : bcTokenAmount != 0)
    (_hFeeAmount :
      buyFeeAmount =
        if isFeeRouter then
          0
        else
          div (mul bcTokenAmount (feePercentageOf s)) (sub decimalPrecision (feePercentageOf s)))
    (hComputedNewVirtualPow :
      trustedCurvePowOutput s
        (add (add (floorSupplyOf s) (totalSupplyOf s))
          (add bcTokenAmount buyFeeAmount))
        computedNewVirtualPow)
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
        isFeeRouter bcTokenAmount buyFeeAmount computedNewVirtualPow).run s).snd
    buy_preserves_reserve_ratio_zero_spec s s' := by
  dsimp [buy_preserves_reserve_ratio_zero_spec]
  intro hInv
  let s' :=
    ((BaseBondingCurve.buy
      isFeeRouter bcTokenAmount buyFeeAmount computedNewVirtualPow).run s).snd
  change reserveRatioDeviationZero s'
  rcases hInv with ⟨_hCurrent, hFloor⟩
  dsimp [reserveRatioDeviationZero, currentReserveRatioDeviationZero,
    floorReserveRatioDeviationZero]
  have hw := buy_slot_writes
    isFeeRouter bcTokenAmount buyFeeAmount computedNewVirtualPow s
    hInitialized hAmountNonZero
    (by simpa [trustedCurvePowOutput] using hComputedNewVirtualPow)
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
  - bounded Uint256 arithmetic for the source-level checked operations;
  - `curvePow` is the opaque boundary for the PRB/ABDK fixed-point pow
    implementation used by `_getBalanceFromReserveRatio`.
-/

/--
  Successful `sell` preserves current and floor reserve-ratio alignment.

  The theorem no longer assumes the post-reserve equality. The executable model
  writes `virtualBalance` to the trusted helper result for the post-sell virtual
  supply, and the arithmetic lemma `virtual_supply_after_sell_net_burn` proves
  that the stored post-state supply is the same full supply point.
-/
theorem sell_preserves_reserve_ratio_zero
    (bcTokenAmount computedNewVirtualPow : Uint256) (s : ContractState)
    (hNetAmountNonZero : sellNetBurnAmount bcTokenAmount s != 0)
    (hComputedNewVirtualPow :
      trustedCurvePowOutput s (sellVirtualSupplyAfter bcTokenAmount s)
        computedNewVirtualPow)
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hNetLeOldSupply : sellNetBurnAmount bcTokenAmount s <= virtualSupplyOf s)
    (hNetLeTotalSupply : sellNetBurnAmount bcTokenAmount s <= totalSupplyOf s)
    (hNetValLeTotalSupply :
      (sellNetBurnAmount bcTokenAmount s).val <= (totalSupplyOf s).val) :
    let s' := ((BaseBondingCurve.sell bcTokenAmount computedNewVirtualPow).run s).snd
    sell_preserves_reserve_ratio_zero_spec s s' := by
  dsimp [sell_preserves_reserve_ratio_zero_spec]
  intro hInv
  let s' := ((BaseBondingCurve.sell bcTokenAmount computedNewVirtualPow).run s).snd
  change reserveRatioDeviationZero s'
  rcases hInv with ⟨hCurrent, hFloor⟩
  dsimp [reserveRatioDeviationZero,
    currentReserveRatioDeviationZero, floorReserveRatioDeviationZero]
  have hw := sell_slot_writes bcTokenAmount computedNewVirtualPow s
    hNetAmountNonZero hNetLeOldSupply hNetLeTotalSupply
    (by simpa [trustedCurvePowOutput] using hComputedNewVirtualPow)
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
    (authorizedFeeRouter : Bool) (bcTokenAmount computedNewFloorPow : Uint256)
    (s : ContractState)
    (hAuthorized : authorizedFeeRouter = true)
    (hAmountNonZero : bcTokenAmount != 0)
    (hComputedNewFloorPow :
      trustedCurvePowOutput s (floorSupplyAfterFeeBurn bcTokenAmount s)
        computedNewFloorPow)
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
        authorizedFeeRouter bcTokenAmount computedNewFloorPow).run s).snd
    floorSellAndBurn_preserves_reserve_ratio_zero_spec s s' := by
  dsimp [floorSellAndBurn_preserves_reserve_ratio_zero_spec]
  intro hInv
  let s' :=
    ((BaseBondingCurve.floorSellAndBurn
      authorizedFeeRouter bcTokenAmount computedNewFloorPow).run s).snd
  change reserveRatioDeviationZero s'
  rcases hInv with ⟨hCurrent, _hFloor⟩
  dsimp [reserveRatioDeviationZero, currentReserveRatioDeviationZero,
    floorReserveRatioDeviationZero]
  have hw := floor_sell_and_burn_slot_writes
    authorizedFeeRouter bcTokenAmount computedNewFloorPow s
    hAuthorized hAmountNonZero hNewFloorLeOldSupply hBurnLeTotalSupply
    (by simpa [trustedCurvePowOutput] using hComputedNewFloorPow)
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
