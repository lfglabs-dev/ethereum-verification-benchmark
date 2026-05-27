import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Decoded `_deltaComposeInternal` `TRANSFER_FROM` dispatch must preserve the
outer `deltaCompose` sender as the ERC20 `transferFrom` source.
-/
theorem delta_compose_internal_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._deltaComposeInternal_transferFrom callerAddress).run s).snd
    outerCaller s' = outerCallerWord {s with sender := callerAddress} ∧
    erc20_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
