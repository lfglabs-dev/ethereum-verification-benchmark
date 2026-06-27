import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/--
Any modeled public-route gate failure prevents a committed LI.FI final transfer.
-/
theorem route_gate_failure_prevents_commit
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    route_gate_failure_prevents_commit_spec
      route steps minAmount outputAmount := by
  exact ?_

end Benchmark.Cases.LiFi.SwapAtomicity
