import Benchmark.Cases.Polaris.BondingCurve.Specs

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem init_reserve_ratio_zero_task
    (virtualSupply_ floorSupply_ : Uint256)
    (s : ContractState)
    (hFloorNonZero : floorSupply_ != 0)
    (hFloorLeVirtual : floorSupply_ <= virtualSupply_) :
    let s' := ((BaseBondingCurve.init virtualSupply_ floorSupply_).run s).snd
    init_reserve_ratio_zero_spec s s' := by
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
