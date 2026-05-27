import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimUsdc` for an address that already claimed reverts before any
state writes, leaving the contract state unchanged.
-/
theorem claimUsdc_reverts_if_already_claimed
    (shareWad : Uint256) (proofAccepted : Bool) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hClaimed : s.storageMap 5 s.sender != 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad proofAccepted).run s).snd
    claimUsdc_reverts_if_already_claimed_spec s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold claimUsdc_reverts_if_already_claimed_spec
  grind [StreamRecoveryClaimUsdc.claimUsdc, StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc, StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed, StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth]

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
