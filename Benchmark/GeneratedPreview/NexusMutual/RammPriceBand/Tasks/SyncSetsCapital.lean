import Benchmark.Cases.NexusMutual.RammPriceBand.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.NexusMutual.RammPriceBand

open Verity
open Verity.EVM.Uint256

/--
Executing `syncPriceBand` stores the provided capital value.
-/
theorem syncPriceBand_sets_capital
    (capital_ supply_ : Uint256) (s : ContractState)
    (hSupply : supply_ != 0) :
    let s' := ((RammPriceBand.syncPriceBand capital_ supply_).run s).snd
    syncPriceBand_sets_capital_spec capital_ s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold syncPriceBand_sets_capital_spec
  grind [RammPriceBand.syncPriceBand, RammPriceBand.capital, RammPriceBand.supply, RammPriceBand.bookValue, RammPriceBand.buySpotPrice, RammPriceBand.sellSpotPrice]

end Benchmark.Cases.NexusMutual.RammPriceBand
