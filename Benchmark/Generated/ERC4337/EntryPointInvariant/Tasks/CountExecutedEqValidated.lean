import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Count of executed ops equals count of validated ops on success.
-/
theorem count_executed_eq_validated
    (validationResults : List ValidationResult) :
    count_executed_eq_validated_spec validationResults := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
