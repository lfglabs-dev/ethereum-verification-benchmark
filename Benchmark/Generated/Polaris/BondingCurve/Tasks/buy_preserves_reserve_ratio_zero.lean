import Benchmark.Cases.Polaris.BondingCurve.Specs

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem buy_preserves_reserve_ratio_zero_task
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount computedNewVirtualBalance : Uint256)
    (s : ContractState)
    (hFeeAmount :
      buyFeeAmount =
        if isFeeRouter then
          0
        else
          div (mul bcTokenAmount (feePercentageOf s)) (sub decimalPrecision (feePercentageOf s)))
    (hComputedNewVirtual :
      computedNewVirtualBalance =
        curveBalance
          (add (add (floorSupplyOf s) (totalSupplyOf s))
            (add bcTokenAmount buyFeeAmount))) :
    let s' :=
      ((BaseBondingCurve.buy
        isFeeRouter bcTokenAmount buyFeeAmount computedNewVirtualBalance).run s).snd
    buy_preserves_reserve_ratio_zero_spec s s' := by
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
