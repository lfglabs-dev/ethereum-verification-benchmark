import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

private theorem add_sub_assoc (a b c : Uint256) : a + (b - c) = (a + b) - c := by
  have lhs_eq : (a + (b - c)) + c = a + b := by
    have hCancel := Verity.Core.Uint256.sub_add_cancel_left b c
    calc
      (a + (b - c)) + c = a + ((b - c) + c) := by rw [Verity.Core.Uint256.add_assoc]
      _ = a + b := by rw [hCancel]
  have rhs_eq : ((a + b) - c) + c = a + b :=
    Verity.Core.Uint256.sub_add_cancel_left (a + b) c
  exact Verity.Core.Uint256.add_right_cancel (by rw [lhs_eq, rhs_eq])

private theorem claimBoth_slot_writes
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 5 s.sender = 1 ∧
    s'.storage 1 = add (s.storage 1) (computedClaimAmount usdcShareWad s) ∧
    s'.storage 2 = sub (s.storage 2) (computedClaimAmount usdcShareWad s) ∧
    s'.storage 6 = s.storage 6 ∧
    s'.storageMap 9 s.sender = 1 ∧
    s'.storage 7 = add (s.storage 7) (computedWethClaimAmount wethShareWad s) ∧
    s'.storage 8 = sub (s.storage 8) (computedWethClaimAmount wethShareWad s) := by
  have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
    simp [hUsdcFresh]
  have hWethFresh' : (s.storageMap 9 s.sender == 0) = true := by
    simp [hWethFresh]
  have hUsdcBound' :
      add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
    simpa [computedClaimAmount] using hUsdcBound
  have hWethBound' :
      add (s.storage 7) (div (mul wethShareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
    simpa [computedWethClaimAmount] using hWethBound
  have hUsdcBoundVal :
      (add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000)).val <= (s.storage 0).val := by
    simpa using hUsdcBound'
  have hWethBoundVal :
      (add (s.storage 7) (div (mul wethShareWad (s.storage 6)) 1000000000000000000)).val <= (s.storage 6).val := by
    simpa using hWethBound'
  repeat' constructor
  all_goals
    simp [StreamRecoveryClaimUsdc.claimBoth, StreamRecoveryClaimUsdc.claimUsdc,
      StreamRecoveryClaimUsdc.claimWeth, computedClaimAmount, computedWethClaimAmount,
      hWaiver, hActive, hUsdcFresh', hWethFresh',
      hUsdcBoundVal, hWethBoundVal, StreamRecoveryClaimUsdc.roundUsdcTotal,
      StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated,
      StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver,
      StreamRecoveryClaimUsdc.hasClaimedUsdc, StreamRecoveryClaimUsdc.roundWethTotal,
      StreamRecoveryClaimUsdc.roundWethClaimed, StreamRecoveryClaimUsdc.totalWethAllocated,
      StreamRecoveryClaimUsdc.hasClaimedWeth, getMapping, getStorage, setMapping,
      setStorage, msgSender, Verity.require, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.snd]

/--
Executing `claimBoth` preserves the claimed-plus-allocated accounting mass
for both tokens.
-/
theorem claimBoth_claimed_plus_allocated_conserved
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_claimed_plus_allocated_conserved_spec usdcShareWad wethShareWad s s' := by
  rcases claimBoth_slot_writes usdcShareWad wethShareWad s
      hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
    ⟨_, _, hUsdcClaimed, hUsdcAllocated, _, _, hWethClaimed, hWethAllocated⟩
  unfold claimBoth_claimed_plus_allocated_conserved_spec
  constructor
  · dsimp
    rw [hUsdcClaimed, hUsdcAllocated]
    calc
      add (add (s.storage 1) (computedClaimAmount usdcShareWad s)) (sub (s.storage 2) (computedClaimAmount usdcShareWad s))
          = add (computedClaimAmount usdcShareWad s) (add (s.storage 1) (sub (s.storage 2) (computedClaimAmount usdcShareWad s))) := by
              calc
                add (add (s.storage 1) (computedClaimAmount usdcShareWad s))
                    (sub (s.storage 2) (computedClaimAmount usdcShareWad s))
                    =
                    add (add (computedClaimAmount usdcShareWad s) (s.storage 1))
                      (sub (s.storage 2) (computedClaimAmount usdcShareWad s)) := by
                        exact Verity.Core.Uint256.add_left_comm (s.storage 1)
                          (computedClaimAmount usdcShareWad s)
                          (sub (s.storage 2) (computedClaimAmount usdcShareWad s))
                _ = add (computedClaimAmount usdcShareWad s)
                      (add (s.storage 1) (sub (s.storage 2) (computedClaimAmount usdcShareWad s))) := by
                        exact Verity.Core.Uint256.add_assoc (computedClaimAmount usdcShareWad s)
                          (s.storage 1)
                          (sub (s.storage 2) (computedClaimAmount usdcShareWad s))
      _ = add (computedClaimAmount usdcShareWad s) ((add (s.storage 1) (s.storage 2)) - computedClaimAmount usdcShareWad s) := by
            simpa using congrArg (fun t => add (computedClaimAmount usdcShareWad s) t)
              (add_sub_assoc (s.storage 1) (s.storage 2) (computedClaimAmount usdcShareWad s))
      _ = add ((add (s.storage 1) (s.storage 2)) - computedClaimAmount usdcShareWad s) (computedClaimAmount usdcShareWad s) := by
            exact Verity.Core.Uint256.add_comm _ _
      _ = add (s.storage 1) (s.storage 2) := by
            exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 1) (s.storage 2))
              (computedClaimAmount usdcShareWad s)
  · dsimp
    rw [hWethClaimed, hWethAllocated]
    calc
      add (add (s.storage 7) (computedWethClaimAmount wethShareWad s)) (sub (s.storage 8) (computedWethClaimAmount wethShareWad s))
          = add (computedWethClaimAmount wethShareWad s) (add (s.storage 7) (sub (s.storage 8) (computedWethClaimAmount wethShareWad s))) := by
              calc
                add (add (s.storage 7) (computedWethClaimAmount wethShareWad s))
                    (sub (s.storage 8) (computedWethClaimAmount wethShareWad s))
                    =
                    add (add (computedWethClaimAmount wethShareWad s) (s.storage 7))
                      (sub (s.storage 8) (computedWethClaimAmount wethShareWad s)) := by
                        exact Verity.Core.Uint256.add_left_comm (s.storage 7)
                          (computedWethClaimAmount wethShareWad s)
                          (sub (s.storage 8) (computedWethClaimAmount wethShareWad s))
                _ = add (computedWethClaimAmount wethShareWad s)
                      (add (s.storage 7) (sub (s.storage 8) (computedWethClaimAmount wethShareWad s))) := by
                        exact Verity.Core.Uint256.add_assoc (computedWethClaimAmount wethShareWad s)
                          (s.storage 7)
                          (sub (s.storage 8) (computedWethClaimAmount wethShareWad s))
      _ = add (computedWethClaimAmount wethShareWad s) ((add (s.storage 7) (s.storage 8)) - computedWethClaimAmount wethShareWad s) := by
            simpa using congrArg (fun t => add (computedWethClaimAmount wethShareWad s) t)
              (add_sub_assoc (s.storage 7) (s.storage 8) (computedWethClaimAmount wethShareWad s))
      _ = add ((add (s.storage 7) (s.storage 8)) - computedWethClaimAmount wethShareWad s) (computedWethClaimAmount wethShareWad s) := by
            exact Verity.Core.Uint256.add_comm _ _
      _ = add (s.storage 7) (s.storage 8) := by
            exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 7) (s.storage 8))
              (computedWethClaimAmount wethShareWad s)
end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
