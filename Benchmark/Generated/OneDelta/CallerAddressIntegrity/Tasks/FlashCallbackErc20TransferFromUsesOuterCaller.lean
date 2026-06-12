import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
ERC20 pulls executed inside a flash-loan callback must still use the outer
`deltaCompose` sender as `from`.
-/
theorem flash_callback_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer.flashLoanCallbackTransferFrom callerAddress).run s).snd
    flash_callback_preserves_outer_caller_spec {s with sender := callerAddress} s' ∧
    erc20_caller_spec {s with sender := callerAddress} s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
