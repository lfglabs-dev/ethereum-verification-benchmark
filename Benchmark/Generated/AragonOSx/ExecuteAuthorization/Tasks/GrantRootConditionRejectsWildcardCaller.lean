import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks

open Verity
open Benchmark.Cases.AragonOSx.ExecuteAuthorization

theorem task_grant_root_condition_rejects_wildcard_caller
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardCallerGrantReverts_spec
      ((DAOAuthorization.grantRootWithCondition ANY_ADDR 256 0 true true specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  exact ?_

end Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks
