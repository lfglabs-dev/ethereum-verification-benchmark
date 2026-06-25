import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
On success, the execution-attempt list has one entry per UserOp.
-/
theorem execution_length_eq_validation_length
    (validationResults : List ValidationResult) :
    execution_length_eq_validation_length_spec validationResults := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
