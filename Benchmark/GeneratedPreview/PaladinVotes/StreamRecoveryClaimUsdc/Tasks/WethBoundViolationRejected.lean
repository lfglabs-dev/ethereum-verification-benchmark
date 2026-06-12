import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

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
  unfold claimWeth_reverts_if_exceeds_total_spec
  have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
    simp [hFresh]
  have hBoundFalse :
      ¬ add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
    simpa [computedWethClaimAmount] using (Nat.not_le_of_gt hExceeds)
  simp [StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hFresh', hBoundFalse,
    StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
    StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
    StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
    getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]
end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
