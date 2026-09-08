import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful open enforces every modeled signed floor and ceiling. -/
theorem open_enforces_signed_floors
    (minOut out minSupply supplied maxBorrowed borrowed minHealth health : Uint256)
    (settles : Bool) (s : ContractState) :
    open_floor_spec minOut out minSupply supplied maxBorrowed borrowed minHealth health settles s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
