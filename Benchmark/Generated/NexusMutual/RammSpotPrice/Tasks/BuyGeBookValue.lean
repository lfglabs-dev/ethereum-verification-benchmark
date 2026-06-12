import Benchmark.Cases.NexusMutual.RammPriceBand.Proofs
import Benchmark.Grindset

namespace Benchmark.Cases.NexusMutual.RammSpotPrice

open Verity
open Verity.EVM.Uint256

/--
The buy spot price is always at or above book value, regardless of whether
the ratchet has converged (BV branch) or is still converging (ratchet branch).
-/
theorem spotPrice_buy_ge_book_value
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hBuyReserve : calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed != 0)
    (hSafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed) :
    spotPrice_buy_ge_book_value_spec eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed := by
  exact spotPrice_buy_ge_book_value_main
    eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
    hEth hOldEth hSupply hCapital hBuyReserve hSafe

end Benchmark.Cases.NexusMutual.RammSpotPrice
