import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimBoth` on the successful path increases both claimed counters
by exactly their computed claim amounts.
-/
theorem claimBoth_updates_round_claimed
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_updates_round_claimed_spec usdcShareWad wethShareWad s s' := by
  simp_all [grind_norm, claimBoth_updates_round_claimed_spec, StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc, StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed, StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth, StreamRecoveryClaimUsdc.claimUsdc, StreamRecoveryClaimUsdc.claimableUsdc, StreamRecoveryClaimUsdc.claimWeth, StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, computedWethClaimAmount, claimUsdc_marks_claimed_spec, claimUsdc_updates_round_claimed_spec, claimUsdc_updates_total_allocated_spec, claimUsdc_claimed_plus_allocated_conserved_spec, claimUsdc_preserves_round_bound_spec, claimUsdc_reverts_if_already_claimed_spec, claimUsdc_reverts_if_exceeds_total_spec, claimUsdc_preserves_weth_state_spec, claimWeth_marks_claimed_spec, claimWeth_updates_round_claimed_spec, claimWeth_updates_total_allocated_spec, claimWeth_claimed_plus_allocated_conserved_spec, claimWeth_preserves_round_bound_spec, claimWeth_reverts_if_already_claimed_spec, claimWeth_reverts_if_exceeds_total_spec, claimWeth_preserves_usdc_state_spec, claimBoth_marks_both_claimed_spec, claimBoth_updates_round_claimed_spec, claimBoth_updates_total_allocated_spec, claimBoth_claimed_plus_allocated_conserved_spec, claimBoth_preserves_round_bounds_spec, claimBoth_reverts_if_usdc_already_claimed_spec, claimBoth_reverts_if_weth_already_claimed_spec, claimBoth_reverts_if_usdc_exceeds_total_spec, claimBoth_reverts_if_weth_exceeds_total_spec, claimBoth_matches_independent_claims_spec]

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
