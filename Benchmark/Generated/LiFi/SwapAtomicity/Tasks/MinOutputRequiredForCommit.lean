import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/-- Under-minimum LI.FI route output cannot commit as a successful route. -/
theorem min_output_required_for_commit
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    min_output_required_for_commit_spec route steps minAmount outputAmount := by
  exact ?_

end Benchmark.Cases.LiFi.SwapAtomicity
