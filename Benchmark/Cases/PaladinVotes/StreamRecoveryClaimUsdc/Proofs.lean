import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

open Verity
open Verity.EVM.Uint256

private theorem uint256_add_notation (a b : Uint256) : a + b = add a b := rfl
private theorem uint256_sub_notation (a b : Uint256) : a - b = sub a b := rfl

private theorem add_sub_assoc (a b c : Uint256) : a + (b - c) = (a + b) - c := by
  have lhs_eq : (a + (b - c)) + c = a + b := by
    have hCancel := Verity.Core.Uint256.sub_add_cancel_left b c
    calc
      (a + (b - c)) + c = a + ((b - c) + c) := by rw [Verity.Core.Uint256.add_assoc]
      _ = a + b := by rw [hCancel]
  have rhs_eq : ((a + b) - c) + c = a + b :=
    Verity.Core.Uint256.sub_add_cancel_left (a + b) c
  exact Verity.Core.Uint256.add_right_cancel (by rw [lhs_eq, rhs_eq])

private theorem claimUsdc_slot_writes
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 5 s.sender = 1 ∧
    s'.storage 1 = add (s.storage 1) (computedClaimAmount shareWad s) ∧
    s'.storage 2 = sub (s.storage 2) (computedClaimAmount shareWad s) ∧
    s'.storage 6 = s.storage 6 ∧
    s'.storage 7 = s.storage 7 ∧
    s'.storage 8 = s.storage 8 ∧
    s'.storageMap 9 = s.storageMap 9 := by
  have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
    simp [hFresh]
  have hBound' :
      add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
    simpa [computedClaimAmount] using hBound
  repeat' constructor
  all_goals
    simp [StreamRecoveryClaimUsdc.claimUsdc, computedClaimAmount, hWaiver, hActive, hFresh', hBound',
      StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
      StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
      StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
      StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
      StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
      getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

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
Executing `claimUsdc` on the successful path marks the caller as claimed.
-/
theorem claimUsdc_marks_user_claimed
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_marks_claimed_spec s s' := by
  unfold claimUsdc_marks_claimed_spec
  exact (claimUsdc_slot_writes shareWad s hWaiver hActive hFresh hBound).2.1

/--
Executing `claimUsdc` on the successful path increases `roundUsdcClaimed`
by exactly the computed claim amount.
-/
theorem claimUsdc_updates_round_claimed
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_updates_round_claimed_spec shareWad s s' := by
  unfold claimUsdc_updates_round_claimed_spec
  exact (claimUsdc_slot_writes shareWad s hWaiver hActive hFresh hBound).2.2.1

/--
Executing `claimUsdc` on the successful path decreases `totalUsdcAllocated`
by exactly the computed claim amount.
-/
theorem claimUsdc_updates_total_allocated
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_updates_total_allocated_spec shareWad s s' := by
  unfold claimUsdc_updates_total_allocated_spec
  exact (claimUsdc_slot_writes shareWad s hWaiver hActive hFresh hBound).2.2.2.1

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
  unfold claimUsdc_preserves_weth_state_spec
  exact (claimUsdc_slot_writes shareWad s hWaiver hActive hFresh hBound).2.2.2.2

/--
Executing `claimUsdc` on the successful path preserves the round bound.
-/
theorem claimUsdc_preserves_round_bound
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_preserves_round_bound_spec s' := by
  rcases claimUsdc_slot_writes shareWad s hWaiver hActive hFresh hBound with
    ⟨hTotal, _, hClaimed, _, _, _, _, _⟩
  unfold claimUsdc_preserves_round_bound_spec
  simpa [hTotal, hClaimed] using hBound

/--
Executing `claimUsdc` moves the computed amount from `totalUsdcAllocated`
into `roundUsdcClaimed`, preserving the combined accounting mass.
-/
theorem claimUsdc_claimed_plus_allocated_conserved
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 5 s.sender = 0)
    (hBound : add (s.storage 1) (computedClaimAmount shareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimUsdc shareWad true).run s).snd
    claimUsdc_claimed_plus_allocated_conserved_spec shareWad s s' := by
  rcases claimUsdc_slot_writes shareWad s hWaiver hActive hFresh hBound with
    ⟨_, _, hClaimed, hAllocated, _, _, _, _⟩
  unfold claimUsdc_claimed_plus_allocated_conserved_spec
  dsimp
  rw [hClaimed, hAllocated]
  calc
    add (add (s.storage 1) (computedClaimAmount shareWad s)) (sub (s.storage 2) (computedClaimAmount shareWad s))
        = add (computedClaimAmount shareWad s) (add (s.storage 1) (sub (s.storage 2) (computedClaimAmount shareWad s))) := by
            calc
              add (add (s.storage 1) (computedClaimAmount shareWad s))
                  (sub (s.storage 2) (computedClaimAmount shareWad s))
                  =
                  add (add (computedClaimAmount shareWad s) (s.storage 1))
                    (sub (s.storage 2) (computedClaimAmount shareWad s)) := by
                      exact Verity.Core.Uint256.add_left_comm (s.storage 1)
                        (computedClaimAmount shareWad s)
                        (sub (s.storage 2) (computedClaimAmount shareWad s))
              _ = add (computedClaimAmount shareWad s)
                    (add (s.storage 1) (sub (s.storage 2) (computedClaimAmount shareWad s))) := by
                      exact Verity.Core.Uint256.add_assoc (computedClaimAmount shareWad s)
                        (s.storage 1)
                        (sub (s.storage 2) (computedClaimAmount shareWad s))
    _ = add (computedClaimAmount shareWad s) ((add (s.storage 1) (s.storage 2)) - computedClaimAmount shareWad s) := by
          simpa [uint256_add_notation, uint256_sub_notation] using
            congrArg (fun t => add (computedClaimAmount shareWad s) t)
            (add_sub_assoc (s.storage 1) (s.storage 2) (computedClaimAmount shareWad s))
    _ = add ((add (s.storage 1) (s.storage 2)) - computedClaimAmount shareWad s) (computedClaimAmount shareWad s) := by
          exact Verity.Core.Uint256.add_comm _ _
    _ = add (s.storage 1) (s.storage 2) := by
          exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 1) (s.storage 2))
            (computedClaimAmount shareWad s)

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
  unfold claimUsdc_reverts_if_already_claimed_spec
  have hClaimedNe : s.storageMap 5 s.sender ≠ 0 := by
    simpa using hClaimed
  have hClaimed' : (s.storageMap 5 s.sender == 0) = false := by
    simp [hClaimedNe]
  simp [StreamRecoveryClaimUsdc.claimUsdc, hWaiver, hActive, hClaimed',
    StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
    StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
    StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
    getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

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

/--
Executing `claimWeth` on the successful path marks the caller as claimed.
-/
theorem claimWeth_marks_user_claimed
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_marks_claimed_spec s s' := by
  unfold claimWeth_marks_claimed_spec
  exact (claimWeth_slot_writes shareWad s hWaiver hActive hFresh hBound).2.2.2.2.2.1

/--
Executing `claimWeth` on the successful path increases `roundWethClaimed`
by exactly the computed claim amount.
-/
theorem claimWeth_updates_round_claimed
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_updates_round_claimed_spec shareWad s s' := by
  unfold claimWeth_updates_round_claimed_spec
  exact (claimWeth_slot_writes shareWad s hWaiver hActive hFresh hBound).2.2.2.2.2.2.1

/--
Executing `claimWeth` on the successful path decreases `totalWethAllocated`
by exactly the computed claim amount.
-/
theorem claimWeth_updates_total_allocated
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_updates_total_allocated_spec shareWad s s' := by
  unfold claimWeth_updates_total_allocated_spec
  exact (claimWeth_slot_writes shareWad s hWaiver hActive hFresh hBound).2.2.2.2.2.2.2

/--
Executing `claimWeth` on the successful path preserves the USDC accounting
slice.
-/
theorem claimWeth_preserves_usdc_state
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_preserves_usdc_state_spec s s' := by
  unfold claimWeth_preserves_usdc_state_spec
  rcases claimWeth_slot_writes shareWad s hWaiver hActive hFresh hBound with
    ⟨hTotal, hClaimed, hAllocated, hMap, _, _, _, _⟩
  exact ⟨hTotal, hClaimed, hAllocated, hMap⟩

/--
Executing `claimWeth` on the successful path preserves the round bound.
-/
theorem claimWeth_preserves_round_bound
    (shareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hFresh : s.storageMap 9 s.sender = 0)
    (hBound : add (s.storage 7) (computedWethClaimAmount shareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad true).run s).snd
    claimWeth_preserves_round_bound_spec s' := by
  rcases claimWeth_slot_writes shareWad s hWaiver hActive hFresh hBound with
    ⟨_, _, _, _, hTotal, _, hClaimed, _⟩
  unfold claimWeth_preserves_round_bound_spec
  simpa [hTotal, hClaimed] using hBound

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
          simpa [uint256_add_notation, uint256_sub_notation] using
            congrArg (fun t => add (computedWethClaimAmount shareWad s) t)
            (add_sub_assoc (s.storage 7) (s.storage 8) (computedWethClaimAmount shareWad s))
    _ = add ((add (s.storage 7) (s.storage 8)) - computedWethClaimAmount shareWad s) (computedWethClaimAmount shareWad s) := by
          exact Verity.Core.Uint256.add_comm _ _
    _ = add (s.storage 7) (s.storage 8) := by
          exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 7) (s.storage 8))
            (computedWethClaimAmount shareWad s)

/--
Executing `claimWeth` for an address that already claimed reverts before any
state writes, leaving the contract state unchanged.
-/
theorem claimWeth_reverts_if_already_claimed
    (shareWad : Uint256) (proofAccepted : Bool) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hClaimed : s.storageMap 9 s.sender != 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimWeth shareWad proofAccepted).run s).snd
    claimWeth_reverts_if_already_claimed_spec s s' := by
  unfold claimWeth_reverts_if_already_claimed_spec
  have hClaimedNe : s.storageMap 9 s.sender ≠ 0 := by
    simpa using hClaimed
  have hClaimed' : (s.storageMap 9 s.sender == 0) = false := by
    simp [hClaimedNe]
  simp [StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hClaimed',
    StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
    StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
    StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
    getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

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

/--
Executing `claimBoth` on the successful path marks the caller as claimed for
both tokens.
-/
theorem claimBoth_marks_both_claimed
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_marks_both_claimed_spec s s' := by
  unfold claimBoth_marks_both_claimed_spec
  rcases claimBoth_slot_writes usdcShareWad wethShareWad s
      hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
    ⟨_, hUsdcClaimed, _, _, _, hWethClaimed, _, _⟩
  exact ⟨hUsdcClaimed, hWethClaimed⟩

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
  unfold claimBoth_updates_round_claimed_spec
  rcases claimBoth_slot_writes usdcShareWad wethShareWad s
      hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
    ⟨_, _, hUsdcClaimed, _, _, _, hWethClaimed, _⟩
  exact ⟨hUsdcClaimed, hWethClaimed⟩

/--
Executing `claimBoth` on the successful path decreases both allocated counters
by exactly their computed claim amounts.
-/
theorem claimBoth_updates_total_allocated
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_updates_total_allocated_spec usdcShareWad wethShareWad s s' := by
  unfold claimBoth_updates_total_allocated_spec
  rcases claimBoth_slot_writes usdcShareWad wethShareWad s
      hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
    ⟨_, _, _, hUsdcAllocated, _, _, _, hWethAllocated⟩
  exact ⟨hUsdcAllocated, hWethAllocated⟩

/--
Executing `claimBoth` on the successful path preserves both round bounds.
-/
theorem claimBoth_preserves_round_bounds
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_preserves_round_bounds_spec s' := by
  rcases claimBoth_slot_writes usdcShareWad wethShareWad s
      hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
    ⟨hUsdcTotal, _, hUsdcClaimed, _, hWethTotal, _, hWethClaimed, _⟩
  unfold claimBoth_preserves_round_bounds_spec
  constructor
  · simpa [hUsdcTotal, hUsdcClaimed] using hUsdcBound
  · simpa [hWethTotal, hWethClaimed] using hWethBound

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
  · rw [hUsdcClaimed, hUsdcAllocated]
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
            simpa [uint256_add_notation, uint256_sub_notation] using
              congrArg (fun t => add (computedClaimAmount usdcShareWad s) t)
              (add_sub_assoc (s.storage 1) (s.storage 2) (computedClaimAmount usdcShareWad s))
      _ = add ((add (s.storage 1) (s.storage 2)) - computedClaimAmount usdcShareWad s) (computedClaimAmount usdcShareWad s) := by
            exact Verity.Core.Uint256.add_comm _ _
      _ = add (s.storage 1) (s.storage 2) := by
            exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 1) (s.storage 2))
              (computedClaimAmount usdcShareWad s)
  · rw [hWethClaimed, hWethAllocated]
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
            simpa [uint256_add_notation, uint256_sub_notation] using
              congrArg (fun t => add (computedWethClaimAmount wethShareWad s) t)
              (add_sub_assoc (s.storage 7) (s.storage 8) (computedWethClaimAmount wethShareWad s))
      _ = add ((add (s.storage 7) (s.storage 8)) - computedWethClaimAmount wethShareWad s) (computedWethClaimAmount wethShareWad s) := by
            exact Verity.Core.Uint256.add_comm _ _
      _ = add (s.storage 7) (s.storage 8) := by
            exact Verity.Core.Uint256.sub_add_cancel_left (add (s.storage 7) (s.storage 8))
              (computedWethClaimAmount wethShareWad s)

/--
Executing `claimBoth` with a previously claimed USDC entitlement reverts
before any state writes, leaving the contract state unchanged.
-/
theorem claimBoth_reverts_if_usdc_already_claimed
    (usdcShareWad : Uint256)
    (usdcProofAccepted wethProofAccepted : Bool)
    (wethShareWad : Uint256)
    (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hClaimed : s.storageMap 5 s.sender != 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad usdcProofAccepted wethShareWad wethProofAccepted).run s).snd
    claimBoth_reverts_if_usdc_already_claimed_spec s s' := by
  unfold claimBoth_reverts_if_usdc_already_claimed_spec
  have hClaimedNe : s.storageMap 5 s.sender ≠ 0 := by
    simpa using hClaimed
  have hClaimed' : (s.storageMap 5 s.sender == 0) = false := by
    simp [hClaimedNe]
  simp [StreamRecoveryClaimUsdc.claimBoth, StreamRecoveryClaimUsdc.claimUsdc,
    hWaiver, hActive, hClaimed', StreamRecoveryClaimUsdc.roundUsdcTotal,
    StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated,
    StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver,
    StreamRecoveryClaimUsdc.hasClaimedUsdc, getMapping, getStorage, msgSender,
    Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

/--
Executing `claimBoth` with a previously claimed WETH entitlement reverts and
rolls back the earlier USDC sub-claim, leaving the contract state unchanged.
-/
theorem claimBoth_reverts_if_weth_already_claimed
    (usdcShareWad wethShareWad : Uint256)
    (wethProofAccepted : Bool)
    (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethClaimed : s.storageMap 9 s.sender != 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad wethProofAccepted).run s).snd
    claimBoth_reverts_if_weth_already_claimed_spec s s' := by
  unfold claimBoth_reverts_if_weth_already_claimed_spec
  have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
    simp [hUsdcFresh]
  have hUsdcBound' :
      add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
    simpa [computedClaimAmount] using hUsdcBound
  have hUsdcBoundVal :
      (add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000)).val <= (s.storage 0).val := by
    simpa using hUsdcBound'
  have hWethClaimedNe : s.storageMap 9 s.sender ≠ 0 := by
    simpa using hWethClaimed
  have hWethClaimed' : (s.storageMap 9 s.sender == 0) = false := by
    simp [hWethClaimedNe]
  simp [StreamRecoveryClaimUsdc.claimBoth, StreamRecoveryClaimUsdc.claimUsdc,
    StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hUsdcFresh', hUsdcBoundVal,
    hWethClaimed', StreamRecoveryClaimUsdc.roundUsdcTotal,
    StreamRecoveryClaimUsdc.roundUsdcClaimed, StreamRecoveryClaimUsdc.totalUsdcAllocated,
    StreamRecoveryClaimUsdc.roundActive, StreamRecoveryClaimUsdc.hasSignedWaiver,
    StreamRecoveryClaimUsdc.hasClaimedUsdc, StreamRecoveryClaimUsdc.roundWethTotal,
    StreamRecoveryClaimUsdc.roundWethClaimed, StreamRecoveryClaimUsdc.totalWethAllocated,
    StreamRecoveryClaimUsdc.hasClaimedWeth, getMapping, getStorage, setMapping,
    setStorage, msgSender, Verity.require, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, Contract.run, ContractResult.snd]

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

/--
Executing `claimBoth` yields the same USDC slice as `claimUsdc` alone and the
same WETH slice as `claimWeth` alone.
-/
theorem claimBoth_matches_independent_claims
    (usdcShareWad wethShareWad : Uint256) (s : ContractState)
    (hWaiver : s.storageMap 4 s.sender != 0)
    (hActive : s.storage 3 != 0)
    (hUsdcFresh : s.storageMap 5 s.sender = 0)
    (hWethFresh : s.storageMap 9 s.sender = 0)
    (hUsdcBound : add (s.storage 1) (computedClaimAmount usdcShareWad s) <= s.storage 0)
    (hWethBound : add (s.storage 7) (computedWethClaimAmount wethShareWad s) <= s.storage 6) :
    let s' := ((StreamRecoveryClaimUsdc.claimBoth usdcShareWad true wethShareWad true).run s).snd
    claimBoth_matches_independent_claims_spec usdcShareWad wethShareWad s s' := by
  unfold claimBoth_matches_independent_claims_spec
  dsimp
  rcases claimBoth_slot_writes usdcShareWad wethShareWad s
      hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
    ⟨hUsdcTotal, hUsdcClaimed, hUsdcRoundClaimed, hUsdcAllocated,
      hWethTotal, hWethClaimed, hWethRoundClaimed, hWethAllocated⟩
  rcases claimUsdc_slot_writes usdcShareWad s hWaiver hActive hUsdcFresh hUsdcBound with
    ⟨hUsdcTotalSolo, hUsdcClaimedSolo, hUsdcRoundClaimedSolo, hUsdcAllocatedSolo, _, _, _, _⟩
  rcases claimWeth_slot_writes wethShareWad s hWaiver hActive hWethFresh hWethBound with
    ⟨_, _, _, _, hWethTotalSolo, hWethClaimedSolo, hWethRoundClaimedSolo, hWethAllocatedSolo⟩
  repeat' constructor
  · exact hUsdcTotal.trans hUsdcTotalSolo.symm
  · exact hUsdcClaimed.trans hUsdcClaimedSolo.symm
  · exact hUsdcRoundClaimed.trans hUsdcRoundClaimedSolo.symm
  · exact hUsdcAllocated.trans hUsdcAllocatedSolo.symm
  · exact hWethTotal.trans hWethTotalSolo.symm
  · exact hWethClaimed.trans hWethClaimedSolo.symm
  · exact hWethRoundClaimed.trans hWethRoundClaimedSolo.symm
  · exact hWethAllocated.trans hWethAllocatedSolo.symm

end Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc
