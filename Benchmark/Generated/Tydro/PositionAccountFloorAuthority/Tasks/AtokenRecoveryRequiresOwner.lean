import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful aToken recovery requires and pays the immutable owner. -/
theorem atoken_recovery_requires_owner
    (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) :
    atoken_authority_spec amount transferSucceeds s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
