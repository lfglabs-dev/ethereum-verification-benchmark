import Benchmark.Cases.NexusMutual.RammPriceBand.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity
open Verity.EVM.Uint256

/--
Executing `syncPriceBand` stores the synchronized sell quote.
-/
theorem syncPriceBand_sets_sell_price
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_sell_price_spec capital_ supply_ s s' := by
  try simp only [grind_norm] at *
  try unfold syncPriceBand_sets_sell_price_spec RammPriceBand.syncPriceBand RammPriceBand.capital RammPriceBand.supply RammPriceBand.bookValue RammPriceBand.buySpotPrice RammPriceBand.sellSpotPrice
  simp [grind_norm, *]

end Benchmark.Cases.NexusMutual.RammPriceBand
