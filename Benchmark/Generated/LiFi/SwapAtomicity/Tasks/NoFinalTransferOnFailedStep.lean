import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/-- A failed modeled LI.FI route step prevents the public final receiver transfer. -/
theorem no_final_transfer_on_failed_step
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) :
    no_final_transfer_on_failed_step_spec route steps minAmount outputAmount := by
  exact ?_

end Benchmark.Cases.LiFi.SwapAtomicity
