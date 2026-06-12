import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimWeth` when the computed payout would exceed the round total
reverts before any state writes, leaving the contract state unchanged.
-/
theorem claimWeth_reverts_if_exceeds_total
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hExceeds : add (s.storage 7) (computedWethClaimAmount shareWad s) > s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_reverts_if_exceeds_total_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
