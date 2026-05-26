import Benchmark.Cases.Polaris.BondingCurve.Specs

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem floor_sell_and_burn_preserves_reserve_ratio_zero_task
    (authorizedFeeRouter : Bool) (bcTokenAmount computedNewFloorBalance : Uint256)
    (s : ContractState)
    (hComputedNewFloor :
      computedNewFloorBalance = curveBalance (add (floorSupplyOf s) bcTokenAmount)) :
    let s' :=
      ((BaseBondingCurve.floorSellAndBurn
        authorizedFeeRouter bcTokenAmount computedNewFloorBalance).run s).snd
    floorSellAndBurn_preserves_reserve_ratio_zero_spec s s' := by
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
