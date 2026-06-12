import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

/--
Executing `claimBoth` when the computed USDC payout would exceed the round
total reverts before any state writes, leaving the contract state unchanged.
-/
theorem claimBoth_reverts_if_usdc_exceeds_total
    (usdcShareWad : Uint256)
    (wethProofAccepted : Bool)
    (wethShareWad : Uint256)
    (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hUsdcExceeds : add (s.storage 1) (computedClaimAmount usdcShareWad s) > s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad wethProofAccepted).run s).snd
    claimBoth_reverts_if_usdc_exceeds_total_spec s s' := by
  unfold claimBoth_reverts_if_usdc_exceeds_total_spec
  have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
    simp [hUsdcFresh]
  have hUsdcBoundFalse :
      ¬ add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
    simpa [computedClaimAmount] using (Nat.not_le_of_gt hUsdcExceeds)
  have hUsdcBoundFalseVal :
      ¬ (add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000)).val <= (s.storage 0).val := by
    simpa using hUsdcBoundFalse
  simp [StreamRecoveryClaimUsdc.claimBoth, StreamRecoveryClaimUsdc.claimUsdc,
    hWaiver, hActive, hUsdcFresh', hUsdcBoundFalseVal, StreamRecoveryClaimUsdc.roundUsdcTotal,
    StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated,
    StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver,
    StreamRecoveryClaimUsdc.hasClaimedUsdc, getMapping, getStorage, msgSender,
    Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
