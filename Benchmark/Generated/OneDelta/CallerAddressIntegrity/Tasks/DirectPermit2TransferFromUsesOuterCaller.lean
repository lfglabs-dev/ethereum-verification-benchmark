import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Direct `PERMIT2_TRANSFER_FROM` operations must pull Permit2 funds from the outer
`deltaCompose` sender.
-/
theorem direct_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._permit2TransferFrom callerAddress).run s).snd
    permit2_pull_uses_outer_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
