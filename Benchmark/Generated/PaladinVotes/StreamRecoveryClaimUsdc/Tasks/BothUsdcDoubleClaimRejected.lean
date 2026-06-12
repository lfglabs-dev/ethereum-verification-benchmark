import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimBoth` with a previously claimed USDC entitlement reverts
before any state writes, leaving the contract state unchanged.
-/
theorem claimBoth_reverts_if_usdc_already_claimed
    (usdcShareWad : Uint256)
    (usdcProofAccepted wethProofAccepted : Bool)
    (wethShareWad : Uint256)
    (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hClaimed : s.storageMap 5 s.sender != 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad usdcProofAccepted wethShareWad wethProofAccepted).run s).snd
    claimBoth_reverts_if_usdc_already_claimed_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
