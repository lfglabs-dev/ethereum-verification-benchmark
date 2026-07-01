import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Fees collected equal the batch size on a successful run.
-/
theorem fees_collected_eq_ops_length
    (ops : List OpInfo) :
    fees_collected_eq_ops_length_spec ops := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
