import Benchmark.Cases.Pendle.PySupplyPairing.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Pendle.PySupplyPairing

open Verity
open Verity.EVM.Uint256

/--
Successful pre-expiry `redeemPY` burns the exact computed amount from both PT
and YT supplies and from the contract's own PT/YT balances.
-/
theorem redeem_py_pre_expiry_burns_equal_amount
    (receiver : Address) (s : ContractState)
    (hNotExpired : s.storage 8 = 0)
    (hSelf : (s.thisAddress != zeroAddress) = true)
    (hPtBalanceEnough : s.storageMap 3 s.thisAddress >= redeemPYAmountOf s)
    (hYtBalanceEnough : s.storageMap 2 s.thisAddress >= redeemPYAmountOf s)
    (hPtSupplyEnough : s.storage 1 >= redeemPYAmountOf s)
    (hYtSupplyEnough : s.storage 0 >= redeemPYAmountOf s)
    (hRedeemUint248 : redeemPYAmountOf s <= uint248Max)
    (hIndexNonzero : (currentIndexOf s != 0) = true)
    (hRedeemMulNoOverflow :
      (redeemPYAmountOf s : Nat) * (ONE : Nat) <= Verity.Stdlib.Math.MAX_UINT256) :
    let s' := ((PendlePY.redeemPY receiver).run s).snd
    redeem_py_pre_expiry_burns_equal_amount_spec s s' := by
  exact ?_

end Benchmark.Cases.Pendle.PySupplyPairing
