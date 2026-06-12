import Benchmark.Cases.Polaris.BondingCurve.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.Polaris.BondingCurve.Tasks

open Benchmark.Cases.Polaris.BondingCurve
open Verity
open Verity.EVM.Uint256

theorem buy_preserves_reserve_ratio_zero_task
    (isFeeRouter : Bool) (bcTokenAmount buyFeeAmount : Uint256)
    (s : ContractState)
    (hInitialized : initializedOf s = 1)
    (hAmountNonZero : bcTokenAmount != 0)
    (hFeeAmount :
      buyFeeAmount =
        if isFeeRouter then
          0
        else
          div (mul bcTokenAmount (feePercentageOf s)) (sub decimalPrecision (feePercentageOf s)))
    (hOldSupplyNoOverflow :
      (floorSupplyOf s).val + (totalSupplyOf s).val < Verity.Core.Uint256.modulus)
    (hMintNoOverflow :
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
  exact ?_

end Benchmark.Generated.Polaris.BondingCurve.Tasks
