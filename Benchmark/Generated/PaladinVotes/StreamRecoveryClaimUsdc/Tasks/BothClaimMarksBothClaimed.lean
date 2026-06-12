import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimBoth` on the successful path marks the caller as claimed for
both tokens.
-/
theorem claimBoth_marks_both_claimed
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_marks_both_claimed_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
