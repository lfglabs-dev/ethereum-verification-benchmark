import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
Decoded `_transfers` `PERMIT2_TRANSFER_FROM` dispatch must preserve the outer
`deltaCompose` sender as the Permit2 `from` address.
-/
theorem transfers_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._transfers_permit2TransferFrom callerAddress).run s).snd
    permit2_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
