import Benchmark.Cases.Usual.DaoCollateral.Specs

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

/--
Direct redeem burns the user USD0 amount, remints only the explicit non-CBR fee,
and debits exactly the collateral returned under oracle, fee, CBR, and rounding.
-/
theorem redeem_conservation
    (rwaToken : Address) (stableAmount minAmountOut price tokenUnit : Uint256)
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
    let s' := ((DaoCollateral.redeemDirect rwaToken stableAmount minAmountOut price tokenUnit).run s).snd
    redeem_conservation_spec rwaToken stableAmount price tokenUnit s s' := by
  exact ?_

end Benchmark.Cases.Usual.DaoCollateral
