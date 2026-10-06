import Benchmark.Cases.Starkware.StarkgateEscrow.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Starkware.StarkgateEscrow

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


set_option linter.unusedVariables false

/--
Deposit lemma: after depositing `amount`, the new balance is `asset + amount` and
the new cumulative deposits is `dep + amount`, so the lower bound is preserved.
The overflow bounds ensure that `add` does not wrap.
-/
private theorem deposit_bound
    (asset dep withd assets : Nat)
    (hInv : asset >= dep - withd)
    (hAssetNoOverflow : asset + assets < Verity.Core.Uint256.modulus)
    (hDepNoOverflow : dep + assets < Verity.Core.Uint256.modulus) :
    asset + assets >= dep + assets - withd := by
  omega

/--
Withdrawal lemma: after withdrawing `amount`, the new balance is `asset - amount`
and the new cumulative withdrawals is `withd + amount`. The lower bound is preserved
because the invariant is a lower bound on asset that moves in lockstep with the
balance reduction.
-/
private theorem withdraw_bound
    (asset dep withd assets : Nat)
    (hInv : asset >= dep - withd)
    (hAssetsLeBalance : assets <= asset)
    (hWithdNoOverflow : withd + assets < Verity.Core.Uint256.modulus) :
    asset - assets >= dep - (withd + assets) := by
  omega

/-- Active deposits preserve the escrow lower bound on the successful no-overflow path. -/
theorem deposit_preserves_escrow_lower_bound
    (amount : Uint256) (s : ContractState)
    (hPre : escrow_lower_bound_spec s)
    (hAmountGt0 : amount.val > 0)
    (hAssetNoOverflow : (s.storage 0).val + amount.val < Verity.Core.Uint256.modulus)
    (hDepNoOverflow : (s.storage 1).val + amount.val < Verity.Core.Uint256.modulus) :
    let s' := ((StarkgateBridge.deposit amount).run s).snd
    deposit_preserves_escrow_lower_bound_spec s s' := by
  dsimp [deposit_preserves_escrow_lower_bound_spec]
  intro _hPre
  unfold escrow_lower_bound_spec
  have hReq : amount > 0 := by
    simpa [Verity.Core.Uint256.lt_def] using hAmountGt0
  have hBound := deposit_bound (s.storage 0).val (s.storage 1).val (s.storage 2).val amount.val
    hPre hAssetNoOverflow hDepNoOverflow
  simpa [StarkgateBridge.deposit, StarkgateBridge.assetBalance,
    StarkgateBridge.cumulativeDeposits, StarkgateBridge.cumulativeWithdrawals,
    assetBalanceOf, cumulativeDepositsOf, cumulativeWithdrawalsOf,
    hReq, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    Verity.EVM.Uint256.add_eq_of_lt hAssetNoOverflow,
    Verity.EVM.Uint256.add_eq_of_lt hDepNoOverflow] using hBound

/-- Withdrawals preserve the escrow lower bound on the successful path. -/
theorem withdraw_preserves_escrow_lower_bound
    (amount : Uint256) (s : ContractState)
    (hPre : escrow_lower_bound_spec s)
    (hAmountLeBalance : amount.val <= (s.storage 0).val)
    (hWithdNoOverflow : (s.storage 2).val + amount.val < Verity.Core.Uint256.modulus) :
    let s' := ((StarkgateBridge.withdraw amount).run s).snd
    withdraw_preserves_escrow_lower_bound_spec s s' := by
  dsimp [withdraw_preserves_escrow_lower_bound_spec]
  intro _hPre
  unfold escrow_lower_bound_spec
  have hReq : amount <= s.storage 0 := by
    simpa [Verity.Core.Uint256.le_def] using hAmountLeBalance
  have hBound := withdraw_bound (s.storage 0).val (s.storage 1).val (s.storage 2).val amount.val
    hPre hAmountLeBalance hWithdNoOverflow
  simpa [StarkgateBridge.withdraw, StarkgateBridge.assetBalance,
    StarkgateBridge.cumulativeDeposits, StarkgateBridge.cumulativeWithdrawals,
    assetBalanceOf, cumulativeDepositsOf, cumulativeWithdrawalsOf,
    hReq, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    Verity.EVM.Uint256.sub_eq_of_le hAmountLeBalance,
    Verity.EVM.Uint256.add_eq_of_lt hWithdNoOverflow] using hBound

/-- Deposit reclaims preserve the escrow lower bound on the successful path. -/
theorem depositReclaim_preserves_escrow_lower_bound
    (amount : Uint256) (s : ContractState)
    (hPre : escrow_lower_bound_spec s)
    (hAmountLeBalance : amount.val <= (s.storage 0).val)
    (hWithdNoOverflow : (s.storage 2).val + amount.val < Verity.Core.Uint256.modulus) :
    let s' := ((StarkgateBridge.depositReclaim amount).run s).snd
    depositReclaim_preserves_escrow_lower_bound_spec s s' := by
  dsimp [depositReclaim_preserves_escrow_lower_bound_spec]
  intro _hPre
  unfold escrow_lower_bound_spec
  have hReq : amount <= s.storage 0 := by
    simpa [Verity.Core.Uint256.le_def] using hAmountLeBalance
  have hBound := withdraw_bound (s.storage 0).val (s.storage 1).val (s.storage 2).val amount.val
    hPre hAmountLeBalance hWithdNoOverflow
  simpa [StarkgateBridge.depositReclaim, StarkgateBridge.assetBalance,
    StarkgateBridge.cumulativeDeposits, StarkgateBridge.cumulativeWithdrawals,
    assetBalanceOf, cumulativeDepositsOf, cumulativeWithdrawalsOf,
    hReq, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    Verity.EVM.Uint256.sub_eq_of_le hAmountLeBalance,
    Verity.EVM.Uint256.add_eq_of_lt hWithdNoOverflow] using hBound

end Benchmark.Cases.Starkware.StarkgateEscrow
