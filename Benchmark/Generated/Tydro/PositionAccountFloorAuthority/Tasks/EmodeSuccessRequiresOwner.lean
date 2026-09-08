import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful eMode mutation requires the immutable owner. -/
theorem emode_success_requires_owner
    (category : Uint256) (poolSucceeds : Bool) (s : ContractState) :
    emode_authority_spec category poolSucceeds s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
