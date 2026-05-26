import Benchmark.Cases.Polaris.BondingCurve.Specs

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem sell_preserves_reserve_ratio_zero_task
    (bcTokenAmount computedNewVirtualBalance : Uint256) (s : ContractState)
    (hNetAmountNonZero :
      sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision) != 0)
    (hComputedNewVirtual :
      computedNewVirtualBalance =
        curveBalance
          (sub (add (floorSupplyOf s) (totalSupplyOf s))
            (sub bcTokenAmount (div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision)))) :
    let s' := ((BaseBondingCurve.sell bcTokenAmount computedNewVirtualBalance).run s).snd
    sell_preserves_reserve_ratio_zero_spec s s' := by
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
