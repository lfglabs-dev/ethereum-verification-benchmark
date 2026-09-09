import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful raw borrow-asset recovery requires and pays the immutable owner. -/
theorem raw_borrow_recovery_requires_owner
    (amount : Uint256) (transferSucceeds : Bool) (s : ContractState) :
    raw_borrow_authority_spec amount transferSucceeds s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
