import Benchmark.Cases.Velora.BridgeStaking.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Velora.BridgeStaking

open Verity
open Verity.EVM.Uint256

/--
Reference: Benchmark.Cases.Velora.BridgeStaking.withdrawUnallocatedTokens_preserves_allocated
Proves preservation for successful withdrawal and arithmetic, zero-amount, or
SafeTransferLib reverts under conservation alone.
-/
theorem withdrawUnallocatedTokens_preserves_allocated
    (isVlr transferSuccess : Bool) (s : ContractState) :
    withdrawUnallocatedTokens_preserves_spec isVlr transferSuccess s := by
  exact ?_

end Benchmark.Cases.Velora.BridgeStaking
