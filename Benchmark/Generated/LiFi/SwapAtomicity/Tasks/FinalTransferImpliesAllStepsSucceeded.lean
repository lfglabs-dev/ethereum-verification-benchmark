import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/-- A committed final transfer means every modeled LI.FI route step succeeded. -/
theorem final_transfer_implies_all_steps_succeeded
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    final_transfer_implies_all_steps_succeeded_spec
      route steps minAmount outputAmount := by
  exact ?_

end Benchmark.Cases.LiFi.SwapAtomicity
