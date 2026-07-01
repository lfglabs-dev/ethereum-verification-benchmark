import Benchmark.Cases.ERC4337.EntryPointInvariant.Specs

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity
open Verity.EVM.Uint256

/--
A reverted batch transfers nothing to the beneficiary.
-/
theorem no_beneficiary_payout_on_revert
    (ops : List FullOpInfo) (startNonce : Nat) :
    no_beneficiary_payout_on_revert_spec ops startNonce := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.ERC4337.EntryPointInvariant
