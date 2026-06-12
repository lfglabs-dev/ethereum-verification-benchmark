import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Decoded `_transfers` `TRANSFER_FROM` dispatch must preserve the outer
`deltaCompose` sender as the ERC20 `transferFrom` source.
-/
theorem transfers_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._transfers_transferFrom callerAddress).run s).snd
    erc20_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
