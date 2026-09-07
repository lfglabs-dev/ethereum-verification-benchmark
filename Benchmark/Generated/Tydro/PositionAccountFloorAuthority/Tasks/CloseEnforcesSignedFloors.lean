import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful close enforces every modeled signed floor and ceiling. -/
theorem close_enforces_signed_floors
    (minWithdraw withdrawn minOut out maxDebt debt maxCollateral collateral minHealth health : Uint256)
    (settles : Bool) (s : ContractState) :
    close_floor_spec minWithdraw withdrawn minOut out maxDebt debt maxCollateral collateral
      minHealth health settles s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
