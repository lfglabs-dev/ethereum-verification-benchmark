import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimBoth` with a previously claimed WETH entitlement reverts and
rolls back the earlier USDC sub-claim, leaving the contract state unchanged.
-/
theorem claimBoth_reverts_if_weth_already_claimed
    (usdcShareWad wethShareWad : Uint256)
    (wethProofAccepted : Bool)
    (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethClaimed : s.storageMap 9 s.sender != 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad wethProofAccepted).run s).snd
    claimBoth_reverts_if_weth_already_claimed_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
