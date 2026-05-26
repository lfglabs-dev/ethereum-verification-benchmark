import Benchmark.Cases.Polaris.BondingCurve.Specs

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem floor_sell_and_burn_preserves_reserve_ratio_zero_task
    (authorizedFeeRouter : Bool) (bcTokenAmount computedNewFloorBalance : Uint256)
    (s : ContractState)
    (hAuthorized : authorizedFeeRouter = true)
    (hAmountNonZero : bcTokenAmount != 0)
    (hComputedNewFloor :
      trustedCurveHelperOutput (floorSupplyAfterFeeBurn bcTokenAmount s)
        computedNewFloorBalance)
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
        authorizedFeeRouter bcTokenAmount computedNewFloorBalance).run s).snd
    floorSellAndBurn_preserves_reserve_ratio_zero_spec s s' := by
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
