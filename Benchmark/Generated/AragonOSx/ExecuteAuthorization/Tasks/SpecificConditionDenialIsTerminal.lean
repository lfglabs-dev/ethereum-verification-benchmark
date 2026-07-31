import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks

open Verity
open Benchmark.Cases.AragonOSx.ExecuteAuthorization

theorem task_specific_condition_denial_is_terminal
    (s : ContractState) (specificStatus : Uint256)
    (hNonzero : specificStatus ≠ 0) (hNotAllow : specificStatus ≠ 2) :
    specificConditionDenialIsTerminal_spec s specificStatus := by
  exact ?_

end Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks
