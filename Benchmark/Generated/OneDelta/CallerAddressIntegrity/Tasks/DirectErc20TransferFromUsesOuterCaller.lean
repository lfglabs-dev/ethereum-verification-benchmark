import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Direct `TRANSFER_FROM` operations must pull ERC20 funds from the outer
`deltaCompose` sender.
-/
theorem direct_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._transferFrom callerAddress).run s).snd
    erc20_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
