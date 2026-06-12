import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

/--
Executing `claimBoth` when the computed WETH payout would exceed the round
total reverts and rolls back the earlier USDC sub-claim, leaving the contract
state unchanged.
-/
theorem claimBoth_reverts_if_weth_exceeds_total
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethExceeds : add (s.storage 7) (computedWethClaimAmount wethShareWad s) > s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_reverts_if_weth_exceeds_total_spec s s' := by
  unfold claimBoth_reverts_if_weth_exceeds_total_spec
  have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
    simp [hUsdcFresh]
  have hWethFresh' : (s.storageMap 9 s.sender == 0) = true := by
    simp [hWethFresh]
  have hUsdcBound' :
      add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
    simpa [computedClaimAmount] using hUsdcBound
  have hUsdcBoundVal :
      (add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000)).val <= (s.storage 0).val := by
    simpa using hUsdcBound'
  have hWethBoundFalse :
      ¬ add (s.storage 7) (div (mul wethShareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
    simpa [computedWethClaimAmount] using (Nat.not_le_of_gt hWethExceeds)
  have hWethBoundFalseVal :
      ¬ (add (s.storage 7) (div (mul wethShareWad (s.storage 6)) 1000000000000000000)).val <= (s.storage 6).val := by
    simpa using hWethBoundFalse
  simp [StreamRecoveryClaimUsdc.claimBoth, StreamRecoveryClaimUsdc.claimUsdc,
    StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hUsdcFresh', hWethFresh',
    hUsdcBoundVal, hWethBoundFalseVal, StreamRecoveryClaimUsdc.roundUsdcTotal,
    StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated,
    StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver,
    StreamRecoveryClaimUsdc.hasClaimedUsdc, StreamRecoveryClaimUsdc.roundWethTotal,
    StreamRecoveryClaimUsdc.roundWethClaimed, StreamRecoveryClaimUsdc.totalWethAllocated,
    StreamRecoveryClaimUsdc.hasClaimedWeth, getMapping, getStorage, setMapping,
    setStorage, msgSender, Verity.require, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, Contract.run, ContractResult.snd]
end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
