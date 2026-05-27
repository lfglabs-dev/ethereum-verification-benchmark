import Benchmark.Cases.Usual.DaoCollateral.Specs

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

/--
The redeem return value is the modeled floor-rounded oracle conversion, with CBR
coefficient applied when active.
-/
theorem redeem_return_formula
    (stableAmount minAmountOut price tokenUnit : Uint256) (rwaToken : Address)
    (s : ContractState)
    (hAmount : stableAmount != 0)
    (hPrice : price != 0)
    (hTokenUnit : tokenUnit != 0)
    (hReturnedNonzero :
      expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
        (cbrCoefOf s) (isCBROnState s) ≠ 0)
    (hMin :
      minAmountOut.val ≤
        (expectedReturnedCollateral stableAmount price tokenUnit (redeemFeeBpsOf s)
          (cbrCoefOf s) (isCBROnState s)).val)
    (hArithmetic :
      successfulRedeemArithmetic rwaToken stableAmount price tokenUnit s) :
    let result := (DaoCollateral.redeemDirect rwaToken stableAmount minAmountOut price tokenUnit).run s
    redeem_return_formula_spec result.fst stableAmount price tokenUnit s := by
  exact ?_

end Benchmark.Cases.Usual.DaoCollateral
