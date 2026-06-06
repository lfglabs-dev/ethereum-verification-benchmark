import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Account approval is required for the batch to succeed.
-/
theorem account_rejection_reverts
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    account_rejection_reverts_spec op rest startNonce := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
