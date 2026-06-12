import Benchmark.Cases.NexusMutual.RammPriceBand.Proofs
import Benchmark.Grindset

namespace Benchmark.Cases.NexusMutual.RammSpotPrice

open Verity
open Verity.EVM.Uint256

/--
The sell spot price never exceeds the buy spot price.
Together with buy_ge_book_value and sell_le_book_value, this gives: sell ≤ bv ≤ buy.
-/
theorem spotPrice_sell_le_buy
    (eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed : Uint256)
    (hEth : eth != 0)
    (hOldEth : oldEth != 0)
    (hSupply : supply != 0)
    (hCapital : capital != 0)
    (hBuyReserve : calculateBuyReserve eth oldEth oldNxmBuyReserve capital supply elapsed speed != 0)
    (hSellReserve : calculateSellReserve eth oldEth oldNxmSellReserve capital supply elapsed speed != 0)
    (hBuySafe : buyArithmeticSafe eth oldEth oldNxmBuyReserve capital supply elapsed speed)
    (hSellSafe : sellArithmeticSafe eth oldEth oldNxmSellReserve capital supply elapsed speed)
    (hScale : realisticSellScale eth capital supply) :
    spotPrice_sell_le_buy_spec eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed := by
  exact spotPrice_sell_le_buy_main
    eth oldEth oldNxmBuyReserve oldNxmSellReserve capital supply elapsed speed
    hEth hOldEth hSupply hCapital hBuyReserve hSellReserve hBuySafe hSellSafe hScale

end Benchmark.Cases.NexusMutual.RammSpotPrice
