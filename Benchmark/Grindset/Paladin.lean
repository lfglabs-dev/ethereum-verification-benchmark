import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Grindset.Paladin

open Verity
open Verity.EVM.Uint256
open Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc

theorem add_sub_assoc (a b c : Uint256) : a + (b - c) = (a + b) - c := by
  have lhs_eq : (a + (b - c)) + c = a + b := by
    have hCancel := Verity.Core.Uint256.sub_add_cancel_left b c
    calc
      (a + (b - c)) + c = a + ((b - c) + c) := by rw [Verity.Core.Uint256.add_assoc]
      _ = a + b := by rw [hCancel]
  have rhs_eq : ((a + b) - c) + c = a + b :=
    Verity.Core.Uint256.sub_add_cancel_left (a + b) c
  exact Verity.Core.Uint256.add_right_cancel (by rw [lhs_eq, rhs_eq])

theorem claimUsdc_slot_writes
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

theorem claimWeth_slot_writes
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

theorem claimBoth_slot_writes
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

end Benchmark.Grindset.Paladin
