import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
Paymaster approval flag has no effect when no paymaster is attached.
-/
theorem paymaster_irrelevant_when_absent
    (op : FullOpInfo) (rest : List FullOpInfo) (startNonce : Nat) :
    paymaster_irrelevant_when_absent_spec op rest startNonce := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
