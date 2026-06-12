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

private theorem claimWeth_slot_writes
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storageMap 5 = s.storageMap 5 ∧
    s'.storage 6 = s.storage 6 ∧
    s'.storageMap 9 s.sender = 1 ∧
    s'.storage 7 = add (s.storage 7) (computedWethClaimAmount shareWad s) ∧
    s'.storage 8 = sub (s.storage 8) (computedWethClaimAmount shareWad s) := by
  have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
    simp [hFresh]
  have hBound' :
      add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
    simpa [computedWethClaimAmount] using hBound
  repeat' constructor
  all_goals
    simp [StreamRecoveryClaimUsdc.claimWeth, computedWethClaimAmount, hWaiver, hActive, hFresh', hBound',
      StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
      StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
      StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
      StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
      StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
      getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

/--
Executing `claimWeth` moves the computed amount from `totalWethAllocated`
into `roundWethClaimed`, preserving the combined accounting mass.
-/
theorem claimWeth_claimed_plus_allocated_conserved
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_claimed_plus_allocated_conserved_spec shareWad s s' := by
  rcases claimWeth_slot_writes shareWad s hWaiver hActive hFresh hBound with
    ⟨_, _, _, _, _, _, hClaimed, hAllocated⟩
  unfold claimWeth_claimed_plus_allocated_conserved_spec
  dsimp
  rw [hClaimed, hAllocated]
  calc
    add (add (s.storage 7) (computedWethClaimAmount shareWad s)) (sub (s.storage 8) (computedWethClaimAmount shareWad s))
        = add (computedWethClaimAmount shareWad s) (add (s.storage 7) (sub (s.storage 8) (computedWethClaimAmount shareWad s))) := by
            calc
              add (add (s.storage 7) (computedWethClaimAmount shareWad s))
                  (sub (s.storage 8) (computedWethClaimAmount shareWad s))
                  =
                  add (add (computedWethClaimAmount shareWad s) (s.storage 7))
                    (sub (s.storage 8) (computedWethClaimAmount shareWad s)) := by
                      exact Verity.Core.Uint256.add_left_comm (s.storage 7)
                        (computedWethClaimAmount shareWad s)
                        (sub (s.storage 8) (computedWethClaimAmount shareWad s))
              _ = add (computedWethClaimAmount shareWad s)
                    (add (s.storage 7) (sub (s.storage 8) (computedWethClaimAmount shareWad s))) := by
                      exact Verity.Core.Uint256.add_assoc (computedWethClaimAmount shareWad s)
                        (s.storage 7)
                        (sub (s.storage 8) (computedWethClaimAmount shareWad s))
    _ = add (computedWethClaimAmount shareWad s) ((add (s.storage 7) (s.storage 8)) - computedWethClaimAmount shareWad s) := by
          simpa using congrArg (fun t => add (computedWethClaimAmount shareWad s) t)
            (add_sub_assoc (s.storage 7) (s.storage 8) (computedWethClaimAmount shareWad s))
    _ = add ((add (s.storage 7) (s.storage 8)) - computedWethClaimAmount shareWad s) (computedWethClaimAmount shareWad s) := by
          exact Verity.Core.Uint256.add_comm _ _
    _ = add (s.storage 7) (s.storage 8) := by
          exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 7) (s.storage 8))
            (computedWethClaimAmount shareWad s)
end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
