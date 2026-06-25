import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
A mismatched declared nonce reverts the entire batch.
-/
theorem nonce_mismatch_reverts
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    nonce_mismatch_reverts_spec op rest startNonce := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
