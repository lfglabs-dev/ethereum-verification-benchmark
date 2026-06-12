import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimWeth` on the successful path decreases `totalWethAllocated`
by exactly the computed claim amount.
-/
theorem claimWeth_updates_total_allocated
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_updates_total_allocated_spec shareWad s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
