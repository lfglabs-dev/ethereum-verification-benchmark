import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Permit2 pulls executed inside a swap callback must still use the outer
`deltaCompose` sender as `from`.
-/
theorem swap_callback_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer.swapCallbackPermit2TransferFrom callerAddress).run s).snd
    swap_callback_preserves_outer_caller_spec {s with sender := callerAddress} s' ∧
    permit2_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
