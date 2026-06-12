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
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
