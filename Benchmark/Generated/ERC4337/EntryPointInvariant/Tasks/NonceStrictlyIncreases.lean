import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Strict nonce monotonicity: non-empty success strictly raises the nonce (no replay).
-/
theorem nonce_strictly_increases
    (ops : List FullOpInfo) (startNonce finalNonce : Nat) :
    nonce_strictly_increases_spec ops startNonce finalNonce := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
