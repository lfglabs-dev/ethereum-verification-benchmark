import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks

open Verity
open Benchmark.Cases.AragonOSx.ExecuteAuthorization

theorem task_grant_execute_with_condition_requires_root
    (who condition : Address) (whereKind : Uint256)
    (conditionIsContract supportsInterface : Bool)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.grantExecuteWithCondition who condition whereKind conditionIsContract supportsInterface
      specificAllows genericCallerAllows genericTargetAllows).run s = ContractResult.success () s') :
    grantExecuteWithConditionRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  exact ?_

end Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks
