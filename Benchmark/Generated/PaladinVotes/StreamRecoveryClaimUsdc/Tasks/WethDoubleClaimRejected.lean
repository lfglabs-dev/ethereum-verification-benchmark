import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimWeth` for an address that already claimed reverts before any
state writes, leaving the contract state unchanged.
-/
theorem claimWeth_reverts_if_already_claimed
    (shareWad : Uint256) (proofAccepted : Bool) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hClaimed : s.storageMap 9 s.sender != 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad proofAccepted).run s).snd
    claimWeth_reverts_if_already_claimed_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
