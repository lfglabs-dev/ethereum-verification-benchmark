import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/-- A committed LI.FI route cannot represent a partially executed step list. -/
theorem committed_route_executes_every_step
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    committed_route_executes_every_step_spec route steps minAmount outputAmount := by
  exact ?_

end Benchmark.Cases.LiFi.SwapAtomicity
