import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

/--
In a batch that routes through both flash-loan and swap callbacks, every modeled
fund-pull path must retain the outer `deltaCompose` sender.
-/
theorem nested_flash_and_swap_callbacks_keep_outer_caller
    (s : ContractState) :
    let s' := ((OneDeltaComposer.allModeledPullsHarness).run s).snd
    all_path_batch_caller_integrity_spec s s' := by
  exact ?_

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
