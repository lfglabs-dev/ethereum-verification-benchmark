import Benchmark.Cases.Usual.DaoCollateral.Specs

namespace Benchmark.Cases.Usual.DaoCollateral

open Verity
open Verity.EVM.Uint256

/--
The redeem fee is the configured basis-point fee, normalized through collateral
token precision when token decimals are below USD0's 18 decimals.
-/
theorem redeem_fee_formula
    (stableAmount tokenUnit : Uint256) (s : ContractState) :
    redeem_fee_formula_spec stableAmount tokenUnit s := by
  exact ?_

end Benchmark.Cases.Usual.DaoCollateral
