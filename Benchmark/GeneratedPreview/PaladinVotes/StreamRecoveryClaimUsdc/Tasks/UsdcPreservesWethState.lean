import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

/--
Executing `claimUsdc` on the successful path preserves the WETH accounting
slice.
-/
theorem claimUsdc_preserves_weth_state
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_preserves_weth_state_spec s s' := by
  try simp only [grind_norm] at *
  try unfold claimUsdc_preserves_weth_state_spec
  try unfold StreamRecoveryClaimUsdc.roundUsdcTotal
  try unfold StreamRecoveryClaimUsdc.roundUsdcClaimed
  try unfold StreamRecoveryClaimUsdc.totalUsdcAllocated
  try unfold StreamRecoveryClaimUsdc.roundActive
  try unfold StreamRecoveryClaimUsdc.hasSignedWaiver
  try unfold StreamRecoveryClaimUsdc.hasClaimedUsdc
  try unfold StreamRecoveryClaimUsdc.roundWethTotal
  try unfold StreamRecoveryClaimUsdc.roundWethClaimed
  try unfold StreamRecoveryClaimUsdc.totalWethAllocated
  try unfold StreamRecoveryClaimUsdc.hasClaimedWeth
  try unfold StreamRecoveryClaimUsdc.claimUsdc
  try unfold StreamRecoveryClaimUsdc.claimableUsdc
  try unfold StreamRecoveryClaimUsdc.claimWeth
  try unfold StreamRecoveryClaimUsdc.claimBoth
  try unfold computedClaimAmount
  try unfold computedWethClaimAmount
  try unfold claimUsdc_marks_claimed_spec
  try unfold claimUsdc_updates_round_claimed_spec
  try unfold claimUsdc_updates_total_allocated_spec
  try unfold claimUsdc_claimed_plus_allocated_conserved_spec
  try unfold claimUsdc_preserves_round_bound_spec
  try unfold claimUsdc_reverts_if_already_claimed_spec
  try unfold claimUsdc_reverts_if_exceeds_total_spec
  try unfold claimUsdc_preserves_weth_state_spec
  try unfold claimWeth_marks_claimed_spec
  try unfold claimWeth_updates_round_claimed_spec
  try unfold claimWeth_updates_total_allocated_spec
  try unfold claimWeth_claimed_plus_allocated_conserved_spec
  try unfold claimWeth_preserves_round_bound_spec
  try unfold claimWeth_reverts_if_already_claimed_spec
  try unfold claimWeth_reverts_if_exceeds_total_spec
  try unfold claimWeth_preserves_usdc_state_spec
  try unfold claimBoth_marks_both_claimed_spec
  try unfold claimBoth_updates_round_claimed_spec
  try unfold claimBoth_updates_total_allocated_spec
  try unfold claimBoth_claimed_plus_allocated_conserved_spec
  try unfold claimBoth_preserves_round_bounds_spec
  try unfold claimBoth_reverts_if_usdc_already_claimed_spec
  try unfold claimBoth_reverts_if_weth_already_claimed_spec
  try unfold claimBoth_reverts_if_usdc_exceeds_total_spec
  try unfold claimBoth_reverts_if_weth_exceeds_total_spec
  try unfold claimBoth_matches_independent_claims_spec
  simp [grind_norm, StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc, StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed, StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth, StreamRecoveryClaimUsdc.claimUsdc, StreamRecoveryClaimUsdc.claimableUsdc, StreamRecoveryClaimUsdc.claimWeth, StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, computedWethClaimAmount, claimUsdc_marks_claimed_spec, claimUsdc_updates_round_claimed_spec, claimUsdc_updates_total_allocated_spec, claimUsdc_claimed_plus_allocated_conserved_spec, claimUsdc_preserves_round_bound_spec, claimUsdc_reverts_if_already_claimed_spec, claimUsdc_reverts_if_exceeds_total_spec, claimUsdc_preserves_weth_state_spec, claimWeth_marks_claimed_spec, claimWeth_updates_round_claimed_spec, claimWeth_updates_total_allocated_spec, claimWeth_claimed_plus_allocated_conserved_spec, claimWeth_preserves_round_bound_spec, claimWeth_reverts_if_already_claimed_spec, claimWeth_reverts_if_exceeds_total_spec, claimWeth_preserves_usdc_state_spec, claimBoth_marks_both_claimed_spec, claimBoth_updates_round_claimed_spec, claimBoth_updates_total_allocated_spec, claimBoth_claimed_plus_allocated_conserved_spec, claimBoth_preserves_round_bounds_spec, claimBoth_reverts_if_usdc_already_claimed_spec, claimBoth_reverts_if_weth_already_claimed_spec, claimBoth_reverts_if_usdc_exceeds_total_spec, claimBoth_reverts_if_weth_exceeds_total_spec, claimBoth_matches_independent_claims_spec, *]
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
