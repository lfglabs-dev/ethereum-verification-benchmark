import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Decoded `_deltaComposeInternal` `PERMIT2_TRANSFER_FROM` dispatch must preserve
the outer `deltaCompose` sender as the Permit2 `from` address.
-/
theorem delta_compose_internal_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._deltaComposeInternal_permit2TransferFrom callerAddress).run s).snd
    outerCaller s' = outerCallerWord {s with sender := callerAddress} ∧
    permit2_pull_uses_outer_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
