import Benchmark.Cases.Velora.BridgeStaking.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Benchmark.Cases.Velora.BridgeStaking

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

private theorem pure_contract_eq :
    (Pure.pure () : Contract Unit) = fun st => ContractResult.success () st := rfl

private theorem sub_val_of_le (a b : Uint256) (h : b.val ≤ a.val) :
    (sub a b).val = a.val - b.val :=
  Verity.EVM.Uint256.sub_eq_of_le h

/-! ## withdrawUnallocatedTokens -/

theorem withdrawUnallocatedTokens_preserves_allocated
    (isVlr transferSuccess : Bool) (s : ContractState) :
    withdrawUnallocatedTokens_preserves_spec isVlr transferSuccess s := by
  unfold withdrawUnallocatedTokens_preserves_spec
  dsimp only
  intro hInv
  dsimp only [allocatedConservationInvariant, allocatedVlrInvariant,
    allocatedWethInvariant, vlrBalanceOf, wethBalanceOf,
    allocatedVLROf, allocatedWETHOf] at hInv ⊢
  have hPureEq := pure_contract_eq
  cases isVlr with
  | true =>
    have hSafe : safeSub (s.storage 0) (s.storage 2) =
        some (sub (s.storage 0) (s.storage 2)) := by
      simpa using Verity.Proofs.Stdlib.Math.safeSub_some
        (s.storage 0) (s.storage 2) hInv.left
    let unallocated := sub (s.storage 0) (s.storage 2)
    have hUnallocLe : unallocated.val ≤ (s.storage 0).val := by
      dsimp [unallocated]
      rw [sub_val_of_le _ _ hInv.left]
      omega
    have hSafeOuter : safeSub (s.storage 0) unallocated =
        some (sub (s.storage 0) unallocated) := by
      simpa using Verity.Proofs.Stdlib.Math.safeSub_some
        (s.storage 0) unallocated hUnallocLe
    by_cases hGt0 : unallocated > 0
    · change 0 < unallocated.val at hGt0
      cases transferSuccess with
      | false =>
        simpa [Staking.withdrawUnallocatedTokens,
          Staking.vlrBalance, Staking.wethBalance,
          Staking.allocatedVLR, Staking.allocatedWETH,
          subPanic, requireSomeUint, Verity.pure, Pure.pure,
          Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, setStorage,
          hPureEq, hSafe, hSafeOuter, hGt0, unallocated] using hInv
      | true =>
        constructor
        · simp [Staking.withdrawUnallocatedTokens,
            Staking.vlrBalance, Staking.wethBalance,
            Staking.allocatedVLR, Staking.allocatedWETH,
            subPanic, requireSomeUint, Verity.pure, Pure.pure,
            Verity.require, Verity.bind, Bind.bind,
            Contract.run, ContractResult.snd, getStorage, setStorage,
            hPureEq, hSafe, hSafeOuter, hGt0, unallocated]
          rw [sub_val_of_le _ _ hUnallocLe, sub_val_of_le _ _ hInv.left]
          exact Nat.le_of_eq (Nat.sub_sub_self hInv.left).symm
        · simpa [Staking.withdrawUnallocatedTokens,
            Staking.vlrBalance, Staking.wethBalance,
            Staking.allocatedVLR, Staking.allocatedWETH,
            subPanic, requireSomeUint, Verity.pure, Pure.pure,
            Verity.require, Verity.bind, Bind.bind,
            Contract.run, ContractResult.snd, getStorage, setStorage,
            hPureEq, hSafe, hSafeOuter, hGt0, unallocated] using hInv.right
    · change ¬ 0 < unallocated.val at hGt0
      simpa [Staking.withdrawUnallocatedTokens,
        Staking.vlrBalance, Staking.wethBalance,
        Staking.allocatedVLR, Staking.allocatedWETH,
        subPanic, requireSomeUint, Verity.pure, Pure.pure,
          Verity.require, Verity.bind, Bind.bind,
        Contract.run, ContractResult.snd, getStorage, setStorage,
        hPureEq, hSafe, hGt0, unallocated] using hInv
  | false =>
    have hSafe : safeSub (s.storage 1) (s.storage 3) =
        some (sub (s.storage 1) (s.storage 3)) := by
      simpa using Verity.Proofs.Stdlib.Math.safeSub_some
        (s.storage 1) (s.storage 3) hInv.right
    let unallocated := sub (s.storage 1) (s.storage 3)
    have hUnallocLe : unallocated.val ≤ (s.storage 1).val := by
      dsimp [unallocated]
      rw [sub_val_of_le _ _ hInv.right]
      omega
    have hSafeOuter : safeSub (s.storage 1) unallocated =
        some (sub (s.storage 1) unallocated) := by
      simpa using Verity.Proofs.Stdlib.Math.safeSub_some
        (s.storage 1) unallocated hUnallocLe
    by_cases hGt0 : unallocated > 0
    · change 0 < unallocated.val at hGt0
      cases transferSuccess with
      | false =>
        simpa [Staking.withdrawUnallocatedTokens,
          Staking.vlrBalance, Staking.wethBalance,
          Staking.allocatedVLR, Staking.allocatedWETH,
          subPanic, requireSomeUint, Verity.pure, Pure.pure,
          Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, setStorage,
          hPureEq, hSafe, hSafeOuter, hGt0, unallocated] using hInv
      | true =>
        constructor
        · simpa [Staking.withdrawUnallocatedTokens,
            Staking.vlrBalance, Staking.wethBalance,
            Staking.allocatedVLR, Staking.allocatedWETH,
            subPanic, requireSomeUint, Verity.pure, Pure.pure,
            Verity.require, Verity.bind, Bind.bind,
            Contract.run, ContractResult.snd, getStorage, setStorage,
            hPureEq, hSafe, hSafeOuter, hGt0, unallocated] using hInv.left
        · simp [Staking.withdrawUnallocatedTokens,
            Staking.vlrBalance, Staking.wethBalance,
            Staking.allocatedVLR, Staking.allocatedWETH,
            subPanic, requireSomeUint, Verity.pure, Pure.pure,
            Verity.require, Verity.bind, Bind.bind,
            Contract.run, ContractResult.snd, getStorage, setStorage,
            hPureEq, hSafe, hSafeOuter, hGt0, unallocated]
          rw [sub_val_of_le _ _ hUnallocLe, sub_val_of_le _ _ hInv.right]
          exact Nat.le_of_eq (Nat.sub_sub_self hInv.right).symm
    · change ¬ 0 < unallocated.val at hGt0
      simpa [Staking.withdrawUnallocatedTokens,
        Staking.vlrBalance, Staking.wethBalance,
        Staking.allocatedVLR, Staking.allocatedWETH,
        subPanic, requireSomeUint, Verity.pure, Pure.pure,
          Verity.require, Verity.bind, Bind.bind,
        Contract.run, ContractResult.snd, getStorage, setStorage,
        hPureEq, hSafe, hGt0, unallocated] using hInv

/--
Rescue preserves conservation from the incoming invariant alone. The proof covers
all receipt flags, public-body guards, checked underflow reverts, successful exact
debits, and either SafeTransferLib result. A failed transfer rolls the entire call
back to `s`, including any earlier VLR rescue writes.
-/
theorem rescuePendingFunds_preserves_allocated
    (key : Uint256) (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState) :
    rescuePendingFunds_preserves_spec key vlrTransferSuccess
      wethTransferSuccess s := by
  unfold rescuePendingFunds_preserves_spec
  dsimp only
  intro hInv
  dsimp only [allocatedConservationInvariant, allocatedVlrInvariant,
    allocatedWethInvariant, vlrBalanceOf, wethBalanceOf,
    allocatedVLROf, allocatedWETHOf] at hInv ⊢
  by_cases hStarted :
      Verity.Core.Address.ofNat (s.storageMapUint 6 key).val = 0
  · simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
      Staking.stakingWethAmount, Staking.stakingBeneficiary,
      Staking.stakingVlrReceived, Staking.stakingWethReceived,
      Staking.allocatedVLR, Staking.allocatedWETH,
      Staking.vlrBalance, Staking.wethBalance,
      Verity.require, Verity.bind, Bind.bind, Contract.run,
      ContractResult.snd, getMappingUint, getMappingUintAddr,
      hStarted] using hInv
  · by_cases hV : s.storageMapUint 7 key = 1
    · by_cases hW : s.storageMapUint 8 key = 1
      · simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
          Staking.stakingWethAmount, Staking.stakingBeneficiary,
          Staking.stakingVlrReceived, Staking.stakingWethReceived,
          Staking.allocatedVLR, Staking.allocatedWETH,
          Staking.vlrBalance, Staking.wethBalance,
          Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getMappingUint,
          getMappingUintAddr, hStarted, hV, hW] using hInv
      · cases hSA : safeSub (s.storage 2) (s.storageMapUint 4 key) with
        | none =>
          simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
            Staking.stakingWethAmount, Staking.stakingBeneficiary,
            Staking.stakingVlrReceived, Staking.stakingWethReceived,
            Staking.allocatedVLR, Staking.allocatedWETH,
            Staking.vlrBalance, Staking.wethBalance, subPanic,
            requireSomeUint, Verity.pure, Pure.pure, Verity.require,
            Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
            getStorage, getMappingUint, getMappingUintAddr,
            hStarted, hV, hW, hSA] using hInv
        | some nA =>
          cases hSB : safeSub (s.storage 0) (s.storageMapUint 4 key) with
          | none =>
            simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
              Staking.stakingWethAmount, Staking.stakingBeneficiary,
              Staking.stakingVlrReceived, Staking.stakingWethReceived,
              Staking.allocatedVLR, Staking.allocatedWETH,
              Staking.vlrBalance, Staking.wethBalance, subPanic,
              requireSomeUint, Verity.pure, Pure.pure, Verity.require,
              Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
              getStorage, getMappingUint, getMappingUintAddr,
              hStarted, hV, hW, hSA, hSB] using hInv
          | some nB =>
            have hAle : (s.storageMapUint 4 key).val ≤ (s.storage 2).val := by
              apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
              rw [hSA]
              rfl
            have hBle : (s.storageMapUint 4 key).val ≤ (s.storage 0).val := by
              apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
              rw [hSB]
              rfl
            have hnA : nA = sub (s.storage 2) (s.storageMapUint 4 key) := by
              exact Option.some.inj (hSA.symm.trans
                (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hAle))
            have hnB : nB = sub (s.storage 0) (s.storageMapUint 4 key) := by
              exact Option.some.inj (hSB.symm.trans
                (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hBle))
            cases vlrTransferSuccess with
            | false =>
              simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
                Staking.stakingWethAmount, Staking.stakingBeneficiary,
                Staking.stakingVlrReceived, Staking.stakingWethReceived,
                Staking.allocatedVLR, Staking.allocatedWETH,
                Staking.vlrBalance, Staking.wethBalance, subPanic,
                requireSomeUint, Verity.pure, Pure.pure, Verity.require,
                Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
                getStorage, setStorage, getMappingUint, getMappingUintAddr,
                setMappingUint, hStarted, hV, hW, hSA, hSB] using hInv
            | true =>
              simp [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
                Staking.stakingWethAmount, Staking.stakingBeneficiary,
                Staking.stakingVlrReceived, Staking.stakingWethReceived,
                Staking.allocatedVLR, Staking.allocatedWETH,
                Staking.vlrBalance, Staking.wethBalance, subPanic,
                requireSomeUint, Verity.pure, Pure.pure, Verity.require,
                Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
                getStorage, setStorage, getMappingUint, getMappingUintAddr,
                setMappingUint, hStarted, hV, hW, hSA, hSB]
              constructor
              · rw [hnA, hnB, sub_val_of_le _ _ hAle,
                  sub_val_of_le _ _ hBle]
                exact Nat.sub_le_sub_right hInv.left _
              · exact hInv.right
    · by_cases hW : s.storageMapUint 8 key = 1
      · cases hSA : safeSub (s.storage 3) (s.storageMapUint 5 key) with
        | none =>
          simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
            Staking.stakingWethAmount, Staking.stakingBeneficiary,
            Staking.stakingVlrReceived, Staking.stakingWethReceived,
            Staking.allocatedVLR, Staking.allocatedWETH,
            Staking.vlrBalance, Staking.wethBalance, subPanic,
            requireSomeUint, Verity.pure, Pure.pure, Verity.require,
            Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
            getStorage, getMappingUint, getMappingUintAddr,
            hStarted, hV, hW, hSA] using hInv
        | some nA =>
          cases hSB : safeSub (s.storage 1) (s.storageMapUint 5 key) with
          | none =>
            simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
              Staking.stakingWethAmount, Staking.stakingBeneficiary,
              Staking.stakingVlrReceived, Staking.stakingWethReceived,
              Staking.allocatedVLR, Staking.allocatedWETH,
              Staking.vlrBalance, Staking.wethBalance, subPanic,
              requireSomeUint, Verity.pure, Pure.pure, Verity.require,
              Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
              getStorage, getMappingUint, getMappingUintAddr,
              hStarted, hV, hW, hSA, hSB] using hInv
          | some nB =>
            have hAle : (s.storageMapUint 5 key).val ≤ (s.storage 3).val := by
              apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
              rw [hSA]
              rfl
            have hBle : (s.storageMapUint 5 key).val ≤ (s.storage 1).val := by
              apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
              rw [hSB]
              rfl
            have hnA : nA = sub (s.storage 3) (s.storageMapUint 5 key) := by
              exact Option.some.inj (hSA.symm.trans
                (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hAle))
            have hnB : nB = sub (s.storage 1) (s.storageMapUint 5 key) := by
              exact Option.some.inj (hSB.symm.trans
                (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hBle))
            cases wethTransferSuccess with
            | false =>
              simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
                Staking.stakingWethAmount, Staking.stakingBeneficiary,
                Staking.stakingVlrReceived, Staking.stakingWethReceived,
                Staking.allocatedVLR, Staking.allocatedWETH,
                Staking.vlrBalance, Staking.wethBalance, subPanic,
                requireSomeUint, Verity.pure, Pure.pure, Verity.require,
                Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
                getStorage, setStorage, getMappingUint, getMappingUintAddr,
                setMappingUint, hStarted, hV, hW, hSA, hSB] using hInv
            | true =>
              simp [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
                Staking.stakingWethAmount, Staking.stakingBeneficiary,
                Staking.stakingVlrReceived, Staking.stakingWethReceived,
                Staking.allocatedVLR, Staking.allocatedWETH,
                Staking.vlrBalance, Staking.wethBalance, subPanic,
                requireSomeUint, Verity.pure, Pure.pure, Verity.require,
                Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
                getStorage, setStorage, getMappingUint, getMappingUintAddr,
                setMappingUint, hStarted, hV, hW, hSA, hSB]
              constructor
              · exact hInv.left
              · rw [hnA, hnB, sub_val_of_le _ _ hAle,
                  sub_val_of_le _ _ hBle]
                exact Nat.sub_le_sub_right hInv.right _
      · simpa [Staking.rescuePendingFunds, Staking.stakingVlrAmount,
          Staking.stakingWethAmount, Staking.stakingBeneficiary,
          Staking.stakingVlrReceived, Staking.stakingWethReceived,
          Staking.allocatedVLR, Staking.allocatedWETH,
          Staking.vlrBalance, Staking.wethBalance,
          Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, getMappingUint,
          getMappingUintAddr, hStarted, hV, hW] using hInv


/-! ## handleV3AcrossMessage helper proofs -/

theorem creditVlrReceipt_preserves
    (key received credited : Uint256) (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hAdd : safeAdd (s.storage 2) received = some credited)
    (hBound : credited.val ≤ (s.storage 0).val) :
    allocatedConservationInvariant (((Staking.creditVlrReceipt key received).run s).snd) := by
  dsimp only [allocatedConservationInvariant, allocatedVlrInvariant,
    allocatedWethInvariant, vlrBalanceOf, wethBalanceOf,
    allocatedVLROf, allocatedWETHOf] at hInv ⊢
  simp [Staking.creditVlrReceipt, Staking.allocatedVLR,
    Staking.stakingVlrReceived, addPanic, requireSomeUint,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
    getStorage, setStorage, setMappingUint, hAdd]
  exact ⟨hBound, hInv.right⟩

theorem creditWethReceipt_preserves
    (key received credited : Uint256) (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hAdd : safeAdd (s.storage 3) received = some credited)
    (hBound : credited.val ≤ (s.storage 1).val) :
    allocatedConservationInvariant (((Staking.creditWethReceipt key received).run s).snd) := by
  dsimp only [allocatedConservationInvariant, allocatedVlrInvariant,
    allocatedWethInvariant, vlrBalanceOf, wethBalanceOf,
    allocatedVLROf, allocatedWETHOf] at hInv ⊢
  simp [Staking.creditWethReceipt, Staking.allocatedWETH,
    Staking.stakingWethReceived, addPanic, requireSomeUint,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
    getStorage, setStorage, setMappingUint, hAdd]
  exact ⟨hInv.left, hBound⟩

theorem settleIfComplete_preserves
    (key depositResult : Uint256) (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState)
    (hInv : allocatedConservationInvariant s) :
    allocatedConservationInvariant (((Staking.settleIfComplete key depositResult
      vlrTransferSuccess wethTransferSuccess).run s).snd) := by
  dsimp only [allocatedConservationInvariant, allocatedVlrInvariant,
    allocatedWethInvariant, vlrBalanceOf, wethBalanceOf,
    allocatedVLROf, allocatedWETHOf] at hInv ⊢
  by_cases hV : s.storageMapUint 7 key = 1
  · by_cases hW : s.storageMapUint 8 key = 1
    · cases hSA : safeSub (s.storage 2) (s.storageMapUint 4 key) with
      | none => simp [Staking.settleIfComplete, Staking.stakingVlrReceived,
          Staking.stakingWethReceived, Staking.stakingVlrAmount,
          Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
          Staking.vlrBalance, Staking.wethBalance, subPanic, requireSomeUint,
          Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind, Contract.run,
          ContractResult.snd, getStorage, setStorage, getMappingUint,
          setMappingUint, hV, hW, hSA, hInv]
      | some nAV =>
        cases hSB : safeSub (s.storage 0) (s.storageMapUint 4 key) with
        | none => simp [Staking.settleIfComplete, Staking.stakingVlrReceived,
            Staking.stakingWethReceived, Staking.stakingVlrAmount,
            Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
            Staking.vlrBalance, Staking.wethBalance, subPanic, requireSomeUint,
            Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind, Contract.run,
            ContractResult.snd, getStorage, setStorage, getMappingUint,
            setMappingUint, hV, hW, hSA, hSB, hInv]
        | some nBV =>
          cases hSWA : safeSub (s.storage 3) (s.storageMapUint 5 key) with
          | none => simp [Staking.settleIfComplete, Staking.stakingVlrReceived,
              Staking.stakingWethReceived, Staking.stakingVlrAmount,
              Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
              Staking.vlrBalance, Staking.wethBalance, subPanic, requireSomeUint,
              Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind, Contract.run,
              ContractResult.snd, getStorage, setStorage, getMappingUint,
              setMappingUint, hV, hW, hSA, hSB, hSWA, hInv]
          | some nAW =>
            cases hSWB : safeSub (s.storage 1) (s.storageMapUint 5 key) with
            | none => simp [Staking.settleIfComplete, Staking.stakingVlrReceived,
                Staking.stakingWethReceived, Staking.stakingVlrAmount,
                Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
                Staking.vlrBalance, Staking.wethBalance, subPanic, requireSomeUint,
                Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind, Contract.run,
                ContractResult.snd, getStorage, setStorage, getMappingUint,
                setMappingUint, hV, hW, hSA, hSB, hSWA, hSWB, hInv]
            | some nBW =>
              have hAle : (s.storageMapUint 4 key).val ≤ (s.storage 2).val := by
                apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
                rw [hSA]
                rfl
              have hBle : (s.storageMapUint 4 key).val ≤ (s.storage 0).val := by
                apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
                rw [hSB]
                rfl
              have hWAle : (s.storageMapUint 5 key).val ≤ (s.storage 3).val := by
                apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
                rw [hSWA]
                rfl
              have hWBle : (s.storageMapUint 5 key).val ≤ (s.storage 1).val := by
                apply (Verity.Proofs.Stdlib.Automation.safeSub_some_iff_ge _ _).mp
                rw [hSWB]
                rfl
              have hnAV : nAV = sub (s.storage 2) (s.storageMapUint 4 key) := by
                exact Option.some.inj (hSA.symm.trans (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hAle))
              have hnBV : nBV = sub (s.storage 0) (s.storageMapUint 4 key) := by
                exact Option.some.inj (hSB.symm.trans (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hBle))
              have hnAW : nAW = sub (s.storage 3) (s.storageMapUint 5 key) := by
                exact Option.some.inj (hSWA.symm.trans (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hWAle))
              have hnBW : nBW = sub (s.storage 1) (s.storageMapUint 5 key) := by
                exact Option.some.inj (hSWB.symm.trans (Verity.Proofs.Stdlib.Math.safeSub_some _ _ hWBle))
              by_cases hDep : depositResult = 1
              · simp [Staking.settleIfComplete, Staking.stakingVlrReceived,
                  Staking.stakingWethReceived, Staking.stakingVlrAmount,
                  Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
                  Staking.vlrBalance, Staking.wethBalance, subPanic, requireSomeUint,
                  Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind, Contract.run,
                  ContractResult.snd, getStorage, setStorage, getMappingUint,
                  setMappingUint, hV, hW, hSA, hSB, hSWA, hSWB, hDep]
                constructor
                · rw [hnAV, hnBV, sub_val_of_le _ _ hAle,
                    sub_val_of_le _ _ hBle]
                  exact Nat.sub_le_sub_right hInv.left _
                · rw [hnAW, hnBW, sub_val_of_le _ _ hWAle,
                    sub_val_of_le _ _ hWBle]
                  exact Nat.sub_le_sub_right hInv.right _
              · cases vlrTransferSuccess with
                | false =>
                  simpa [Staking.settleIfComplete, Staking.stakingVlrReceived,
                    Staking.stakingWethReceived, Staking.stakingVlrAmount,
                    Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
                    Staking.vlrBalance, Staking.wethBalance, subPanic, requireSomeUint,
                    Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind,
                    Contract.run, ContractResult.snd, getStorage, setStorage,
                    getMappingUint, setMappingUint, hV, hW, hSA, hSB, hSWA,
                    hSWB, hDep] using hInv
                | true =>
                  cases wethTransferSuccess with
                  | false =>
                    simpa [Staking.settleIfComplete, Staking.stakingVlrReceived,
                      Staking.stakingWethReceived, Staking.stakingVlrAmount,
                      Staking.stakingWethAmount, Staking.allocatedVLR,
                      Staking.allocatedWETH, Staking.vlrBalance, Staking.wethBalance,
                      subPanic, requireSomeUint, Verity.pure, Pure.pure,
                      Verity.require, Verity.bind, Bind.bind, Contract.run,
                      ContractResult.snd, getStorage, setStorage, getMappingUint,
                      setMappingUint, hV, hW, hSA, hSB, hSWA, hSWB, hDep] using hInv
                  | true =>
                    simp [Staking.settleIfComplete, Staking.stakingVlrReceived,
                      Staking.stakingWethReceived, Staking.stakingVlrAmount,
                      Staking.stakingWethAmount, Staking.allocatedVLR,
                      Staking.allocatedWETH, Staking.vlrBalance, Staking.wethBalance,
                      subPanic, requireSomeUint, Verity.pure, Pure.pure,
                      Verity.require, Verity.bind, Bind.bind, Contract.run,
                      ContractResult.snd, getStorage, setStorage, getMappingUint,
                      setMappingUint, hV, hW, hSA, hSB, hSWA, hSWB, hDep]
                    constructor
                    · rw [hnAV, hnBV, sub_val_of_le _ _ hAle,
                        sub_val_of_le _ _ hBle]
                      exact Nat.sub_le_sub_right hInv.left _
                    · rw [hnAW, hnBW, sub_val_of_le _ _ hWAle,
                        sub_val_of_le _ _ hWBle]
                      exact Nat.sub_le_sub_right hInv.right _
    · simpa [Staking.settleIfComplete, Staking.stakingVlrReceived,
        Staking.stakingWethReceived, Staking.stakingVlrAmount,
        Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
        Staking.vlrBalance, Staking.wethBalance, getMappingUint,
        Verity.pure, Pure.pure, Verity.bind, Bind.bind, Contract.run,
        ContractResult.snd, hV, hW] using hInv
  · simpa [Staking.settleIfComplete, Staking.stakingVlrReceived,
      Staking.stakingWethReceived, Staking.stakingVlrAmount,
      Staking.stakingWethAmount, Staking.allocatedVLR, Staking.allocatedWETH,
      Staking.vlrBalance, Staking.wethBalance, getMappingUint,
      Verity.pure, Pure.pure, Verity.bind, Bind.bind, Contract.run,
      ContractResult.snd, hV] using hInv

private theorem sequence_preserves
    (f g : Contract Unit) (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hf : allocatedConservationInvariant ((f.run s).snd))
    (hg : ∀ t, allocatedConservationInvariant t →
      allocatedConservationInvariant ((g.run t).snd)) :
    allocatedConservationInvariant ((((do f; g) : Contract Unit).run s).snd) := by
  cases hfRun : f s
  · rename_i u t
    have hInvT : allocatedConservationInvariant t := by
      simpa [Contract.run, hfRun] using hf
    have hG := hg t hInvT
    cases hgRun : g t
    · simpa [Contract.run, Verity.bind, Bind.bind, hfRun, hgRun] using hG
    · simpa [Contract.run, Verity.bind, Bind.bind, hfRun, hgRun] using hInv
  · simpa [Contract.run, Verity.bind, Bind.bind, hfRun] using hInv

theorem processValidatedVlr_preserves
    (key received credited depositResult : Uint256)
    (vlrTransferSuccess wethTransferSuccess : Bool) (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hAdd : safeAdd (s.storage 2) received = some credited)
    (hBound : credited.val ≤ (s.storage 0).val) :
    allocatedConservationInvariant
      (((Staking.processValidatedReceipt key true received depositResult
        vlrTransferSuccess wethTransferSuccess).run s).snd) := by
  rw [Staking.processValidatedReceipt]
  exact sequence_preserves _ _ s hInv
    (creditVlrReceipt_preserves key received credited s hInv hAdd hBound)
    (fun t ht => settleIfComplete_preserves key depositResult
      vlrTransferSuccess wethTransferSuccess t ht)

theorem processValidatedWeth_preserves
    (key received credited depositResult : Uint256)
    (vlrTransferSuccess wethTransferSuccess : Bool) (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hAdd : safeAdd (s.storage 3) received = some credited)
    (hBound : credited.val ≤ (s.storage 1).val) :
    allocatedConservationInvariant
      (((Staking.processValidatedReceipt key false received depositResult
        vlrTransferSuccess wethTransferSuccess).run s).snd) := by
  rw [Staking.processValidatedReceipt]
  exact sequence_preserves _ _ s hInv
    (creditWethReceipt_preserves key received credited s hInv hAdd hBound)
    (fun t ht => settleIfComplete_preserves key depositResult
      vlrTransferSuccess wethTransferSuccess t ht)

theorem prepareRecord_storage
    (key vlrAmount wethAmount : Uint256) (beneficiary : Address)
    (isVlr : Bool) (receivedAmount : Uint256) (s : ContractState) (i : Nat) :
    (((Staking.prepareRecord key vlrAmount wethAmount beneficiary isVlr receivedAmount).run s).snd).storage i =
      s.storage i := by
  cases isVlr with
  | false =>
    by_cases hNew : Core.Address.ofNat (s.storageMapUint 6 key).val = 0
    all_goals by_cases hV : s.storageMapUint 7 key = 1
    all_goals by_cases hW : s.storageMapUint 8 key = 1
    all_goals by_cases hAmt : receivedAmount =
      (if Core.Address.ofNat (s.storageMapUint 6 key).val = 0 then wethAmount else s.storageMapUint 5 key)
    all_goals by_cases hZero : s.storageMapUint 8 key = 0
    all_goals simp_all [Staking.prepareRecord, Staking.stakingVlrAmount,
      Staking.stakingWethAmount, Staking.stakingBeneficiary,
      Staking.stakingVlrReceived, Staking.stakingWethReceived,
      Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, getMappingUint, getMappingUintAddr,
      setMappingUint, setMappingUintAddr]
  | true =>
    by_cases hNew : Core.Address.ofNat (s.storageMapUint 6 key).val = 0
    all_goals by_cases hV : s.storageMapUint 7 key = 1
    all_goals by_cases hW : s.storageMapUint 8 key = 1
    all_goals by_cases hAmt : receivedAmount =
      (if Core.Address.ofNat (s.storageMapUint 6 key).val = 0 then vlrAmount else s.storageMapUint 4 key)
    all_goals by_cases hZero : s.storageMapUint 7 key = 0
    all_goals simp_all [Staking.prepareRecord, Staking.stakingVlrAmount,
      Staking.stakingWethAmount, Staking.stakingBeneficiary,
      Staking.stakingVlrReceived, Staking.stakingWethReceived,
      Verity.pure, Pure.pure, Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, getMappingUint, getMappingUintAddr,
      setMappingUint, setMappingUintAddr]

theorem prepareRecord_preserves
    (key vlrAmount wethAmount : Uint256) (beneficiary : Address)
    (isVlr : Bool) (receivedAmount : Uint256) (s : ContractState)
    (hInv : allocatedConservationInvariant s) :
    allocatedConservationInvariant
      (((Staking.prepareRecord key vlrAmount wethAmount beneficiary isVlr receivedAmount).run s).snd) := by
  dsimp only [allocatedConservationInvariant, allocatedVlrInvariant,
    allocatedWethInvariant, vlrBalanceOf, wethBalanceOf,
    allocatedVLROf, allocatedWETHOf] at hInv ⊢
  simpa [prepareRecord_storage] using hInv

theorem prepareThenProcessVlr_preserves
    (key vlrAmount wethAmount receivedAmount credited depositResult : Uint256)
    (beneficiary : Address) (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hAdd : safeAdd (s.storage 2) receivedAmount = some credited)
    (hBound : credited.val ≤ (s.storage 0).val) :
    allocatedConservationInvariant
      ((((do
        Staking.prepareRecord key vlrAmount wethAmount beneficiary true receivedAmount
        Staking.processValidatedReceipt key true receivedAmount depositResult
          vlrTransferSuccess wethTransferSuccess) : Contract Unit).run s).snd) := by
  cases hPrep : Staking.prepareRecord key vlrAmount wethAmount beneficiary true receivedAmount s
  · rename_i u t
    have hInvT : allocatedConservationInvariant t := by
      have h := prepareRecord_preserves key vlrAmount wethAmount beneficiary true receivedAmount s hInv
      simpa [Contract.run, hPrep] using h
    have hStorage : ∀ i, t.storage i = s.storage i := by
      intro i
      have h := prepareRecord_storage key vlrAmount wethAmount beneficiary true receivedAmount s i
      simpa [Contract.run, hPrep] using h
    have hAddT : safeAdd (t.storage 2) receivedAmount = some credited := by
      rw [hStorage]
      exact hAdd
    have hBoundT : credited.val ≤ (t.storage 0).val := by
      rw [hStorage]
      exact hBound
    have hProcess := processValidatedVlr_preserves key receivedAmount credited depositResult
      vlrTransferSuccess wethTransferSuccess t hInvT hAddT hBoundT
    cases hRun : Staking.processValidatedReceipt key true receivedAmount depositResult
      vlrTransferSuccess wethTransferSuccess t
    · simpa [Contract.run, Verity.bind, Bind.bind, hPrep, hRun] using hProcess
    · simpa [Contract.run, Verity.bind, Bind.bind, hPrep, hRun] using hInv
  · simpa [Contract.run, Verity.bind, Bind.bind, hPrep] using hInv

theorem prepareThenProcessWeth_preserves
    (key vlrAmount wethAmount receivedAmount credited depositResult : Uint256)
    (beneficiary : Address) (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState)
    (hInv : allocatedConservationInvariant s)
    (hAdd : safeAdd (s.storage 3) receivedAmount = some credited)
    (hBound : credited.val ≤ (s.storage 1).val) :
    allocatedConservationInvariant
      ((((do
        Staking.prepareRecord key vlrAmount wethAmount beneficiary false receivedAmount
        Staking.processValidatedReceipt key false receivedAmount depositResult
          vlrTransferSuccess wethTransferSuccess) : Contract Unit).run s).snd) := by
  cases hPrep : Staking.prepareRecord key vlrAmount wethAmount beneficiary false receivedAmount s
  · rename_i u t
    have hInvT : allocatedConservationInvariant t := by
      have h := prepareRecord_preserves key vlrAmount wethAmount beneficiary false receivedAmount s hInv
      simpa [Contract.run, hPrep] using h
    have hStorage : ∀ i, t.storage i = s.storage i := by
      intro i
      have h := prepareRecord_storage key vlrAmount wethAmount beneficiary false receivedAmount s i
      simpa [Contract.run, hPrep] using h
    have hAddT : safeAdd (t.storage 3) receivedAmount = some credited := by
      rw [hStorage]
      exact hAdd
    have hBoundT : credited.val ≤ (t.storage 1).val := by
      rw [hStorage]
      exact hBound
    have hProcess := processValidatedWeth_preserves key receivedAmount credited depositResult
      vlrTransferSuccess wethTransferSuccess t hInvT hAddT hBoundT
    cases hRun : Staking.processValidatedReceipt key false receivedAmount depositResult
      vlrTransferSuccess wethTransferSuccess t
    · simpa [Contract.run, Verity.bind, Bind.bind, hPrep, hRun] using hProcess
    · simpa [Contract.run, Verity.bind, Bind.bind, hPrep, hRun] using hInv
  · simpa [Contract.run, Verity.bind, Bind.bind, hPrep] using hInv

theorem handleV3AcrossMessage_preserves_allocated
    (key vlrAmount wethAmount minBptAmount : Uint256)
    (beneficiary : Address)
    (isVlr : Bool)
    (receivedAmount depositResult : Uint256)
    (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState) :
    handleV3AcrossMessage_preserves_spec key vlrAmount wethAmount minBptAmount
      beneficiary isVlr receivedAmount depositResult vlrTransferSuccess
      wethTransferSuccess s := by
  unfold handleV3AcrossMessage_preserves_spec
  dsimp only
  intro hInv
  cases isVlr with
  | false =>
    cases hAdd : safeAdd (s.storage 3) receivedAmount with
    | none =>
      simpa [Staking.handleV3AcrossMessage, Staking.vlrBalance,
        Staking.wethBalance, Staking.allocatedVLR, Staking.allocatedWETH,
        addPanic, requireSomeUint, Verity.pure, Pure.pure,
        Verity.require, Verity.bind, Bind.bind,
        Contract.run, ContractResult.snd, getStorage, hAdd] using hInv
    | some credited =>
      by_cases hBal : credited.val ≤ (s.storage 1).val
      · have hComp := prepareThenProcessWeth_preserves key vlrAmount wethAmount
          receivedAmount credited depositResult beneficiary vlrTransferSuccess
          wethTransferSuccess s hInv hAdd hBal
        simpa [Staking.handleV3AcrossMessage, Staking.vlrBalance,
          Staking.wethBalance, Staking.allocatedVLR, Staking.allocatedWETH,
          addPanic, requireSomeUint, Verity.pure, Pure.pure,
        Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, hAdd, hBal] using hComp
      · simpa [Staking.handleV3AcrossMessage, Staking.vlrBalance,
          Staking.wethBalance, Staking.allocatedVLR, Staking.allocatedWETH,
          addPanic, requireSomeUint, Verity.pure, Pure.pure,
        Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, hAdd, hBal] using hInv
  | true =>
    cases hAdd : safeAdd (s.storage 2) receivedAmount with
    | none =>
      simpa [Staking.handleV3AcrossMessage, Staking.vlrBalance,
        Staking.wethBalance, Staking.allocatedVLR, Staking.allocatedWETH,
        addPanic, requireSomeUint, Verity.pure, Pure.pure,
        Verity.require, Verity.bind, Bind.bind,
        Contract.run, ContractResult.snd, getStorage, hAdd] using hInv
    | some credited =>
      by_cases hBal : credited.val ≤ (s.storage 0).val
      · have hComp := prepareThenProcessVlr_preserves key vlrAmount wethAmount
          receivedAmount credited depositResult beneficiary vlrTransferSuccess
          wethTransferSuccess s hInv hAdd hBal
        simpa [Staking.handleV3AcrossMessage, Staking.vlrBalance,
          Staking.wethBalance, Staking.allocatedVLR, Staking.allocatedWETH,
          addPanic, requireSomeUint, Verity.pure, Pure.pure,
        Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, hAdd, hBal] using hComp
      · simpa [Staking.handleV3AcrossMessage, Staking.vlrBalance,
          Staking.wethBalance, Staking.allocatedVLR, Staking.allocatedWETH,
          addPanic, requireSomeUint, Verity.pure, Pure.pure,
        Verity.require, Verity.bind, Bind.bind,
          Contract.run, ContractResult.snd, getStorage, hAdd, hBal] using hInv

end Benchmark.Cases.Velora.BridgeStaking
