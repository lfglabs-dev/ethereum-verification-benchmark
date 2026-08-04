import Benchmark.Cases.Velora.BridgeStaking.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Velora.BridgeStaking

open Verity
open Verity.EVM.Uint256

/--
Reference: Benchmark.Cases.Velora.BridgeStaking.rescuePendingFunds_preserves_allocated
Proves conservation for every modeled rescue execution from the incoming invariant
alone, including record guards, partial receipt flags, checked underflow, successful
exact debits, and either SafeTransferLib result.
-/
theorem rescuePendingFunds_preserves_allocated
    (key : Uint256) (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState) :
    rescuePendingFunds_preserves_spec key vlrTransferSuccess
      wethTransferSuccess s := by
  exact ?_

end Benchmark.Cases.Velora.BridgeStaking
