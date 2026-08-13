import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks

open Verity
open Benchmark.Cases.AragonOSx.ExecuteAuthorization

theorem task_execute_success_implies_authorized
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.execute specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    authorizedExecutionStarted s s' specificAllows genericCallerAllows genericTargetAllows := by
  exact ?_

end Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks
