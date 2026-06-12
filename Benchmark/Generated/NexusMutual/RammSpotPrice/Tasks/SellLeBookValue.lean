import Benchmark.Cases.NexusMutual.RammPriceBand.Proofs
import Benchmark.Grindset

namespace Benchmark.Cases.NexusMutual.RammSpotPrice

open Verity
open Verity.EVM.Uint256

/--
The sell spot price is always at or below book value, regardless of whether
the ratchet has converged (BV branch) or is still converging (ratchet branch).
-/
theorem spotPrice_sell_le_book_value
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hSellReserve : calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed != 0)
    (hSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed)
    (hScale : realisticSellScale eth capital supply) :
    spotPrice_sell_le_book_value_spec eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed := by
  exact spotPrice_sell_le_book_value_main
    eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
    hEth hOldEth hSupply hCapital hSellReserve hSafe hScale

end Benchmark.Cases.NexusMutual.RammSpotPrice
