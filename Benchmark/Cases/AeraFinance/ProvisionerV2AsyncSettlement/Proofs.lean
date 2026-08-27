import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256
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
