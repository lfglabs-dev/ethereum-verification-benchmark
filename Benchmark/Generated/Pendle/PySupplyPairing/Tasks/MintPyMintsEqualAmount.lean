import Benchmark.Cases.Pendle.PySupplyPairing.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Pendle.PySupplyPairing

open Verity
open Verity.EVM.Uint256

/--
Successful `mintPY` increments both supplies and both receiver balances by the
exact computed `amountPYOut`.
-/
theorem mint_py_mints_equal_amount
    (receiverPT receiverYT : Address) (s : ContractState)
    (hNotExpired : s.storage 8 = 0)
    (hSyNoUnderflow : s.storage 5 >= s.storage 4)
    (hFloatingNonzero : (sub (s.storage 5) (s.storage 4) != 0) = true)
    (hMintMulNoOverflow :
      (floatingSyOf s : Nat) * (currentIndexOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hMintUint248 : mintPYAmountOf s <= uint248Max)
    (hYtSupplyAddNoOverflow :
      (ytSupply s : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hYtBalanceAddNoOverflow :
      (ytBalanceOf s receiverYT : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hPtSupplyAddNoOverflow :
      (ptSupply s : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hPtBalanceAddNoOverflow :
      (ptBalanceOf s receiverPT : Nat) + (mintPYAmountOf s : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hReceiverPT : (receiverPT != zeroAddress) = true)
    (hReceiverYT : (receiverYT != zeroAddress) = true) :
    let s' := ((PendlePY.mintPY receiverPT receiverYT).run s).snd
    mint_py_mints_equal_amount_spec receiverPT receiverYT s s' := by
  exact ?_

end Benchmark.Cases.Pendle.PySupplyPairing
