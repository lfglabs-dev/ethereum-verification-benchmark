import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
The Uniswap V3-style callback shortcut for `calldataLength == 0` pays the pool
with ERC20 `transferFrom(callerAddress, caller(), amountToPay)`. Its `from`
argument must still be the outer `deltaCompose` sender.
-/
theorem v3_callback_direct_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer.v3SwapCallbackDirectTransferFrom callerAddress).run s).snd
    swap_callback_preserves_outer_caller_spec {s with sender := callerAddress} s' ∧
    v3_direct_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
