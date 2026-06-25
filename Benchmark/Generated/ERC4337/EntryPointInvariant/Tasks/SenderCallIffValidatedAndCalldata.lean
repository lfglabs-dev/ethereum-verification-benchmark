import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Inner sender call is entered iff validation passed and callData non-empty.
-/
theorem sender_call_iff_validated_and_calldata
    (ops : List OpInfo) (i : Nat) :
    sender_call_iff_validated_and_calldata_spec ops i := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
