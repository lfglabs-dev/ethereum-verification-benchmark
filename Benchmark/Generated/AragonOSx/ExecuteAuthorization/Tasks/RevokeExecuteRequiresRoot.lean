import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks

open Verity
open Benchmark.Cases.AragonOSx.ExecuteAuthorization

theorem task_revoke_execute_requires_root
    (who : Address) (whereKind : Uint256)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.revokeExecute who whereKind specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    revokeExecuteRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  exact ?_

end Benchmark.Generated.AragonOSx.ExecuteAuthorization.Tasks
