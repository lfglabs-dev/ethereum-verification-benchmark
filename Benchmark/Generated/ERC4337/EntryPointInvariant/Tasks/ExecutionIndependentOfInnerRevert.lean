import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Execution attempt is independent of whether inner sender-call reverted.
-/
theorem execution_independent_of_inner_revert
    (ops1 ops2 : List OpInfo) (i : Nat) :
    execution_independent_of_inner_revert_spec ops1 ops2 i := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
