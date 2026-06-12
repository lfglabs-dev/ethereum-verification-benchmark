import Benchmark.Cases.Polaris.BondingCurve.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem sell_preserves_reserve_ratio_zero_task
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
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
