import Benchmark.Cases.Pareto.RedemptionBacking.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Pareto.RedemptionBacking

open Verity
open Verity.EVM.Uint256

@[simp] private theorem readSlot_eq_storage (s : ContractState) (slotIdx : Nat) :
    s.readSlot slotIdx = s.storage slotIdx := rfl
@[simp] private theorem readAddrSlot_eq_storageAddr (s : ContractState) (slotIdx : Nat) :
    s.readAddrSlot slotIdx = s.storageAddr slotIdx := rfl
@[simp] private theorem readMap_eq_storageMap (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.readMap slotIdx k = s.storageMap slotIdx k := rfl
@[simp] private theorem readMapUint_eq_storageMapUint (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.readMapUint slotIdx k = s.storageMapUint slotIdx k := rfl
@[simp] private theorem readMap2_eq_storageMap2 (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.readMap2 slotIdx k1 k2 = s.storageMap2 slotIdx k1 k2 := rfl
@[simp] private theorem readTransient_eq_transientStorage (s : ContractState) (slotIdx : Nat) :
    s.readTransient slotIdx = s.transientStorage slotIdx := rfl
@[simp] private theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl
@[simp] private theorem storageAddr_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageAddr =
      s.storageAddr := rfl
@[simp] private theorem storageMap_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      s.storageMap := rfl
@[simp] private theorem storageMapUint_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapUint =
      s.storageMapUint := rfl
@[simp] private theorem storageMap2_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap2 =
      s.storageMap2 := rfl
@[simp] private theorem address_ofNat_storageWords_addr (s : ContractState) (slotIdx : Nat) :
    Verity.Core.Address.ofNat (s.storageWords (.addr slotIdx)).val = s.storageAddr slotIdx := rfl


/--
Under the modeled successful `depositFunds` branch, including the source reserve
require (`hReserveGuard`) and checked-arithmetic side conditions, the post-state
satisfies the closed-epoch reserve guard.
-/
theorem depositFunds_preserves_closed_epoch_reserve_guard
    (depositedScaled : Uint256) (s : ContractState)
    (hCollateralized : s.storage 5 != 0)
    (hDepositLeIdle : depositedScaled.val <= (s.storage 0).val)
    (hCurrentLeReserved : (s.storage 3).val <= (s.storage 2).val)
    (hAddNoOverflow :
      (sub (s.storage 0) depositedScaled).val + (s.storage 1).val <
        Verity.Core.Uint256.modulus)
    (hReserveGuard :
      (sub (s.storage 2) (s.storage 3)).val <=
        (add (sub (s.storage 0) depositedScaled) (s.storage 1)).val) :
    let s' := ((ParetoDollarQueue.depositFunds depositedScaled).run s).snd
    depositFunds_preserves_closed_epoch_reserve_guard_spec s s' := by
  dsimp [depositFunds_preserves_closed_epoch_reserve_guard_spec]
  unfold closed_epoch_reserve_guard
  have hReqIdle : depositedScaled <= s.storage 0 := by
    simpa [Verity.Core.Uint256.le_def] using hDepositLeIdle
  have hReqReserved : s.storage 3 <= s.storage 2 := by
    simpa [Verity.Core.Uint256.le_def] using hCurrentLeReserved
  have hAddVal :
      (add (sub (s.storage 0) depositedScaled) (s.storage 1)).val =
        (sub (s.storage 0) depositedScaled).val + (s.storage 1).val := by
    exact Verity.EVM.Uint256.add_eq_of_lt hAddNoOverflow
  have hReqNoOverflow :
      sub (s.storage 0) depositedScaled <=
        add (sub (s.storage 0) depositedScaled) (s.storage 1) := by
    rw [Verity.Core.Uint256.le_def, hAddVal]
    exact Nat.le_add_right _ _
  have hReqNoOverflowVal :
      (sub (s.storage 0) depositedScaled).val <=
        (add (sub (s.storage 0) depositedScaled) (s.storage 1)).val := by
    simpa [Verity.Core.Uint256.le_def] using hReqNoOverflow
  have hReqGuard :
      sub (s.storage 2) (s.storage 3) <= add (sub (s.storage 0) depositedScaled) (s.storage 1) := by
    simpa [Verity.Core.Uint256.le_def] using hReserveGuard
  by_cases hPrevReady : (s.storage 4).val <= (sub (s.storage 0) depositedScaled).val
  · simp [ParetoDollarQueue.depositFunds, ParetoDollarQueue.idleCollateralScaled,
      ParetoDollarQueue.totCreditVaultsRequestedScaled,
      ParetoDollarQueue.totReservedWithdrawals, ParetoDollarQueue.currentEpochPending,
      ParetoDollarQueue.previousEpochPending, ParetoDollarQueue.collateralizedFlag,
      idleCollateralScaledOf, totCreditVaultsRequestedScaledOf,
      totReservedWithdrawalsOf, currentEpochPendingOf, closedClaims,
      hCollateralized, hReqIdle, hReqNoOverflowVal,
      hPrevReady, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, hAddNoOverflow,
      hCurrentLeReserved, hReserveGuard]
  · simp [ParetoDollarQueue.depositFunds, ParetoDollarQueue.idleCollateralScaled,
      ParetoDollarQueue.totCreditVaultsRequestedScaled,
      ParetoDollarQueue.totReservedWithdrawals, ParetoDollarQueue.currentEpochPending,
      ParetoDollarQueue.previousEpochPending, ParetoDollarQueue.collateralizedFlag,
      idleCollateralScaledOf, totCreditVaultsRequestedScaledOf,
      totReservedWithdrawalsOf, currentEpochPendingOf, closedClaims,
      hCollateralized, hReqIdle, hReqNoOverflowVal,
      hPrevReady, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, hAddNoOverflow,
      hCurrentLeReserved, hReserveGuard]

end Benchmark.Cases.Pareto.RedemptionBacking
