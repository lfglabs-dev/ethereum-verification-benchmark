import Benchmark.Cases.LiFi.SwapAtomicity.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/-- Any failed modeled LI.FI swap route step forces the whole route to revert. -/
theorem failed_step_reverts
    (steps : List SwapStep) :
    failed_step_reverts_spec steps := by
  exact ?_

end Benchmark.Cases.LiFi.SwapAtomicity
