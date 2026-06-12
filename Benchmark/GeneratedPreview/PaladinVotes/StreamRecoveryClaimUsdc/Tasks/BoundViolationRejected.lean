import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

/--
Executing `claimUsdc` when the computed payout would exceed the round total
reverts before any state writes, leaving the contract state unchanged.
-/
theorem claimUsdc_reverts_if_exceeds_total
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hExceeds : add (s.storage 1) (computedClaimAmount shareWad s) > s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_reverts_if_exceeds_total_spec s s' := by
  unfold claimUsdc_reverts_if_exceeds_total_spec
  have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
    simp [hFresh]
  have hBoundFalse :
      ¬ add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
    simpa [computedClaimAmount] using (Nat.not_le_of_gt hExceeds)
  simp [StreamRecoveryClaimUsdc.claimUsdc, hWaiver, hActive, hFresh', hBoundFalse,
    StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
    StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
    StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
    getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]
end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
