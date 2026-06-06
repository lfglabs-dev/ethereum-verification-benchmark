import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Paymaster approval is required when a paymaster is attached.
-/
theorem paymaster_rejection_reverts_when_present
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    paymaster_rejection_reverts_when_present_spec op rest startNonce := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
