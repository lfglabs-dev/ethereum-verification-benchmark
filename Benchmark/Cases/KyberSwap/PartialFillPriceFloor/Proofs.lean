import Benchmark.Cases.KyberSwap.PartialFillPriceFloor.Specs

namespace Benchmark.Cases.KyberSwap.PartialFillPriceFloor

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem checkReturnAmount_partial_success_implies_floor
    (spentAmount returnAmount amount minReturnAmount flags : Uint256)
    (s : ContractState)
    (hPartial : _flagsChecked flags partialFillFlag = true)
    (hRun :
      (MetaAggregationRouterV2._checkReturnAmount
        spentAmount returnAmount amount minReturnAmount flags).run s =
        ContractResult.success () s) :
    checkedScaledPriceFloorHolds spentAmount returnAmount
      { amount := amount, minReturnAmount := minReturnAmount, flags := flags } := by
  unfold checkedScaledPriceFloorHolds
  unfold MetaAggregationRouterV2._checkReturnAmount at hRun
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    Verity.require, _flagsChecked, partialFillFlag, mulPanic,
    requireSomeUint] at hRun hPartial
  by_cases hLeft : safeMul returnAmount amount = none
  · simp [hPartial, hLeft, mulPanic, requireSomeUint, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Contract.run, Verity.require] at hRun
  · cases hLeftSome : safeMul returnAmount amount with
    | none =>
        exact False.elim (hLeft (by simpa using hLeftSome))
    | some left =>
        by_cases hRight : safeMul minReturnAmount spentAmount = none
        · simp [hPartial, hLeftSome, hRight, mulPanic, requireSomeUint,
            Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
            Verity.require] at hRun
        · cases hRightSome : safeMul minReturnAmount spentAmount with
          | none =>
              exact False.elim (hRight (by simpa using hRightSome))
          | some right =>
              simp [hPartial, hLeftSome, hRightSome, mulPanic, requireSomeUint,
                Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
                Verity.require] at hRun
              by_cases hReq : right.val ≤ left.val
              · simpa [hLeftSome, hRightSome] using hReq
              · simp [hReq] at hRun

/--
  Successful execution of the modeled `_checkReturnAmount` helper in the
  partial-fill branch enforces the checked scaled price floor.
-/
theorem checkReturnAmount_partial_fill_price_floor
    (spentAmount returnAmount amount minReturnAmount flags : Uint256)
    (s : ContractState)
    (hPartial :
      isPartialFill
        { amount := amount, minReturnAmount := minReturnAmount, flags := flags } = true)
    (hRun :
      (MetaAggregationRouterV2._checkReturnAmount
        spentAmount returnAmount amount minReturnAmount flags).run s =
        ContractResult.success () s) :
    partial_fill_price_floor_spec spentAmount returnAmount
      { amount := amount, minReturnAmount := minReturnAmount, flags := flags } := by
  intro _
  exact checkReturnAmount_partial_success_implies_floor
    spentAmount returnAmount amount minReturnAmount flags s hPartial hRun

end Benchmark.Cases.KyberSwap.PartialFillPriceFloor
