import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

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
@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] private theorem storageAddr_writeAddrSlot (s : ContractState) (slotIdx : Nat) (value : Address) (slotIdx' : Nat) :
    (s.writeAddrSlot slotIdx value).storageAddr slotIdx' =
      if slotIdx' == slotIdx then value else s.storageAddr slotIdx' := by
  by_cases h : slotIdx' = slotIdx
  · subst h; simp
  · simp [ContractState.storageAddr_writeAddrSlot_other s h value, h]
@[simp] private theorem storageMap_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256)
    (slotIdx' : Nat) (key' : Address) :
    (s.writeMap slotIdx key value).storageMap slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMap slotIdx' key' := by
  simp [ContractState.storageMap, ContractState.writeMap]
@[simp] private theorem storageMapUint_writeMapUint (s : ContractState) (slotIdx : Nat) (key value : Uint256)
    (slotIdx' : Nat) (key' : Uint256) :
    (s.writeMapUint slotIdx key value).storageMapUint slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMapUint slotIdx' key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint]
@[simp] private theorem storage_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storage = s.storage := by
  funext wordSlot; simp [ContractState.storage, ContractState.writeMap2]
@[simp] private theorem storageAddr_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageAddr = s.storageAddr := by
  funext addrSlot; simp [ContractState.storageAddr, ContractState.writeMap2]
@[simp] private theorem storageMap_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap = s.storageMap := by
  funext mapSlot mapKey; simp [ContractState.storageMap, ContractState.writeMap2]
@[simp] private theorem storageMapUint_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey; simp [ContractState.storageMapUint, ContractState.writeMap2]
@[simp] private theorem storageMap2_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256)
    (slotIdx' : Nat) (key1' key2' : Address) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap2 slotIdx' key1' key2' =
      if slotIdx' == slotIdx && key1' == key1 && key2' == key2 then value else s.storageMap2 slotIdx' key1' key2' := by
  simp [ContractState.storageMap2, ContractState.writeMap2, and_assoc]
@[simp] private theorem storageWords_slot_eq (s : ContractState) (slotIdx : Nat) :
    s.storageWords (.slot slotIdx) = s.storage slotIdx := rfl
@[simp] private theorem storageWords_map_eq (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.storageWords (.map slotIdx k) = s.storageMap slotIdx k := rfl
@[simp] private theorem storageWords_mapUint_eq (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.storageWords (.mapUint slotIdx k) = s.storageMapUint slotIdx k := rfl
@[simp] private theorem storageWords_map2_eq (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.storageWords (.map2 slotIdx k1 k2) = s.storageMap2 slotIdx k1 k2 := rfl

set_option linter.unusedSimpArgs false

/-- A successful vault solve consumes the only active marker, so all four
    terminal entry points reject or ignore immediate replay. -/
theorem vault_solve_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    vault_solve_terminal_exclusivity_spec requestKey s := by
  rcases hCovered with ⟨_, hAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKind with hDeposit | hRedeem
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [vault_solve_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hDepositRaw, hAmountRaw]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [vault_solve_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hRedeemRaw, hAmountRaw, hOneNeZero]

/-- A direct solve consumes the active marker before payout and cannot be replayed through any terminal path. -/
theorem direct_solve_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hFixed : fixedPriceOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    direct_solve_terminal_exclusivity_spec requestKey s := by
  rcases hCovered with ⟨_, hAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hFixedRaw : s.storageMap 3 requestKey = 1 := by
    simpa [fixedPriceOf] using hFixed
  have hFixedNe : s.storageMap 3 requestKey ≠ 0 := by
    rw [hFixedRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKind with hDeposit | hRedeem
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    simp [direct_solve_terminal_exclusivity_spec, hFixedNe, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hDepositRaw, hAmountRaw]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    simp [direct_solve_terminal_exclusivity_spec, hFixedNe, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hRedeemRaw, hAmountRaw, hOneNeZero]

/-- An expired vault solve takes the source refund branch, consumes the active marker, and excludes every later terminal path. -/
theorem expired_vault_solve_refund_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    expired_vault_solve_refund_terminal_exclusivity_spec requestKey s := by
  rcases hCovered with ⟨_, hAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKind with hDeposit | hRedeem
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [expired_vault_solve_refund_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hDepositRaw, hAmountRaw]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [expired_vault_solve_refund_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hRedeemRaw, hAmountRaw, hOneNeZero]

/-- An expired fixed-price direct solve takes the source refund branch, consumes the active marker, and excludes every later terminal path. -/
theorem expired_direct_solve_refund_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hFixed : fixedPriceOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    expired_direct_solve_refund_terminal_exclusivity_spec requestKey s := by
  rcases hCovered with ⟨_, hAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hFixedRaw : s.storageMap 3 requestKey = 1 := by
    simpa [fixedPriceOf] using hFixed
  have hFixedNe : s.storageMap 3 requestKey ≠ 0 := by
    rw [hFixedRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKind with hDeposit | hRedeem
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    simp [expired_direct_solve_refund_terminal_exclusivity_spec, hFixedNe, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hDepositRaw, hAmountRaw]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    simp [expired_direct_solve_refund_terminal_exclusivity_spec, hFixedNe, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hRedeemRaw, hAmountRaw, hOneNeZero]


/-- An authorized or expired refund consumes the active marker and excludes every later terminal path. -/
theorem refund_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    refund_terminal_exclusivity_spec requestKey s := by
  rcases hCovered with ⟨_, hAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKind with hDeposit | hRedeem
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [refund_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hDepositRaw, hAmountRaw]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [refund_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hRedeemRaw, hAmountRaw, hOneNeZero]

/-- A permitted cancellation consumes the active marker and excludes every later terminal path. -/
theorem cancellation_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    cancellation_terminal_exclusivity_spec requestKey s := by
  rcases hCovered with ⟨_, hAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKind with hDeposit | hRedeem
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [cancellation_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hDepositRaw, hAmountRaw]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    by_cases hFixedReplay : s.storageMap 3 requestKey = 0 <;>
    simp [cancellation_terminal_exclusivity_spec, hFixedReplay, AeraProvisionerV2.solveRequestVault,
      AeraProvisionerV2._solveRequestVault, AeraProvisionerV2.solveRequestDirect,
      AeraProvisionerV2.refundRequest, AeraProvisionerV2.cancelRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow,
      activeOf, requestKindOf, escrowAmountOf, fixedPriceOf, directReplayRejected,
      depositEscrowOf, unitEscrowOf,
      depositKind, redeemKind, noOutcome, vaultSolveOutcome, directSolveOutcome,
      refundOutcome, cancellationOutcome, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hActiveNe, hRedeemRaw, hAmountRaw, hOneNeZero]

/-- The single public invariant: one active request activation cannot produce
    two terminal outcomes. The six route lemmas above discharge every modeled
    live, expired-refund, refund, and cancellation branch. -/
theorem active_request_cannot_be_consumed_twice
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    active_request_cannot_be_consumed_twice_spec requestKey s := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact vault_solve_terminal_exclusivity requestKey s hActive hKind hCovered
  · exact expired_vault_solve_refund_terminal_exclusivity
      requestKey s hActive hKind hCovered
  · exact refund_terminal_exclusivity requestKey s hActive hKind hCovered
  · exact cancellation_terminal_exclusivity requestKey s hActive hKind hCovered
  · intro hFixed
    exact ⟨
      direct_solve_terminal_exclusivity requestKey s hActive hFixed hKind hCovered,
      expired_direct_solve_refund_terminal_exclusivity
        requestKey s hActive hFixed hKind hCovered⟩

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
