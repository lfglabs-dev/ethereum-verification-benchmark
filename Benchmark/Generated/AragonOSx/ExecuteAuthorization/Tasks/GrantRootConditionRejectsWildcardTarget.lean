import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks

open Verity
open Benchmark.Cases.AragonOSx.ExecuteAuthorization

theorem task_grant_root_condition_rejects_wildcard_target
    (who : Address) (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardTargetGrantReverts_spec
      who ((DAOAuthorization.grantRootWithCondition who 256 1 true true specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  exact ?_

end Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks
