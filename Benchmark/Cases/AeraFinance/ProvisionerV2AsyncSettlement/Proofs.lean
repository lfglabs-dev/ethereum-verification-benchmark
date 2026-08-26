import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256
set_option linter.unusedSimpArgs false

/-- Request creation establishes the reachable active-escrow premise used by all
    terminal settlement theorems. -/
theorem create_request_establishes_active_escrow
    (requestKey : Address) (kind amount : Uint256) (isFixedPrice : Bool)
    (s : ContractState)
    (hKind : kind = depositKind ∨ kind = redeemKind)
    (hInactive : activeOf s requestKey = 0)
    (hBalanceGrows :
      escrowBalanceOf s kind <= add (escrowBalanceOf s kind) amount)
    (hAmountCovered :
      amount <= add (escrowBalanceOf s kind) amount) :
    create_request_establishes_active_escrow_spec requestKey kind amount isFixedPrice s := by
  have hInactiveRaw : s.storageMap 0 requestKey = 0 := by
    simpa [activeOf] using hInactive
  rcases hKind with hDeposit | hRedeem
  · have hKindRaw : kind = 0 := by simpa [depositKind] using hDeposit
    have hBalanceGrowsRaw : s.storage 3 <= add (s.storage 3) amount := by
      simpa [escrowBalanceOf, hKindRaw, depositKind, depositEscrowOf] using hBalanceGrows
    have hAmountCoveredRaw : amount <= add (s.storage 3) amount := by
      simpa [escrowBalanceOf, hKindRaw, depositKind, depositEscrowOf] using hAmountCovered
    by_cases hFixed : isFixedPrice = true <;>
    simp [create_request_establishes_active_escrow_spec, activeEscrowCovered,
      escrowBalanceOf, AeraProvisionerV2.createRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow, activeOf, requestKindOf, escrowAmountOf,
      fixedPriceOf,
      depositEscrowOf, unitEscrowOf, depositKind, getStorage, setStorage,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hKindRaw, hInactiveRaw, hBalanceGrowsRaw, hAmountCoveredRaw, hFixed]
  · have hKindRaw : kind = 1 := by simpa [redeemKind] using hRedeem
    have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
    have hBalanceGrowsRaw : s.storage 4 <= add (s.storage 4) amount := by
      simpa [escrowBalanceOf, hKindRaw, depositKind, redeemKind, unitEscrowOf, hOneNeZero] using hBalanceGrows
    have hAmountCoveredRaw : amount <= add (s.storage 4) amount := by
      simpa [escrowBalanceOf, hKindRaw, depositKind, redeemKind, unitEscrowOf, hOneNeZero] using hAmountCovered
    by_cases hFixed : isFixedPrice = true <;>
    simp [create_request_establishes_active_escrow_spec, activeEscrowCovered,
      escrowBalanceOf, AeraProvisionerV2.createRequest,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow, activeOf, requestKindOf, escrowAmountOf,
      fixedPriceOf,
      depositEscrowOf, unitEscrowOf, depositKind, redeemKind, getStorage, setStorage,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hKindRaw, hInactiveRaw, hBalanceGrowsRaw, hAmountCoveredRaw, hOneNeZero,
      hFixed]

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

/-- One guarded failure in the two-request vault loop preserves that deposit or
    redeem request's active marker and escrow while a distinct same-kind request
    settles. -/
theorem guarded_batch_failure_preserves_active_escrow
    (firstKey secondKey : Address) (firstAmount secondAmount : Uint256)
    (s : ContractState)
    (hDistinct : firstKey ≠ secondKey)
    (hFirstActive : activeOf s firstKey = 1)
    (hSecondActive : activeOf s secondKey = 1)
    (hKinds :
      (requestKindOf s firstKey = depositKind ∧
        requestKindOf s secondKey = depositKind) ∨
      (requestKindOf s firstKey = redeemKind ∧
        requestKindOf s secondKey = redeemKind))
    (hFirstAmount : escrowAmountOf s firstKey = firstAmount)
    (hSecondAmount : escrowAmountOf s secondKey = secondAmount)
    (hSecondCovered : activeEscrowCovered s secondKey)
    (hRemaining :
      firstAmount <=
        sub (escrowBalanceOf s (requestKindOf s firstKey)) secondAmount) :
    guarded_batch_failure_preserves_active_escrow_spec
      firstKey secondKey firstAmount secondAmount s := by
  have hDistinct' : secondKey ≠ firstKey := Ne.symm hDistinct
  have hFirstActiveRaw : s.storageMap 0 firstKey = 1 := by
    simpa [activeOf] using hFirstActive
  have hSecondActiveRaw : s.storageMap 0 secondKey = 1 := by
    simpa [activeOf] using hSecondActive
  have hSecondActiveNe : s.storageMap 0 secondKey ≠ 0 := by
    rw [hSecondActiveRaw]
    decide
  have hFirstAmountRaw : s.storageMap 2 firstKey = firstAmount := by
    simpa [escrowAmountOf] using hFirstAmount
  have hSecondAmountRaw : s.storageMap 2 secondKey = secondAmount := by
    simpa [escrowAmountOf] using hSecondAmount
  rcases hSecondCovered with ⟨_, hSecondCoveredAmount⟩
  rcases hKinds with ⟨hFirstDeposit, hSecondDeposit⟩ | ⟨hFirstRedeem, hSecondRedeem⟩
  · have hFirstKindRaw : s.storageMap 1 firstKey = 0 := by
      simpa [requestKindOf, depositKind] using hFirstDeposit
    have hSecondKindRaw : s.storageMap 1 secondKey = 0 := by
      simpa [requestKindOf, depositKind] using hSecondDeposit
    have hSecondCoveredRaw : secondAmount.val <= (s.storage 3).val := by
      simpa [escrowAmountOf, escrowBalanceOf, requestKindOf, hSecondKindRaw,
        depositKind, depositEscrowOf, hSecondAmountRaw] using hSecondCoveredAmount
    have hRemainingRaw : firstAmount <= sub (s.storage 3) secondAmount := by
      simpa [escrowBalanceOf, requestKindOf, hFirstKindRaw, depositKind,
        depositEscrowOf] using hRemaining
    simp [guarded_batch_failure_preserves_active_escrow_spec,
      activeEscrowCovered, escrowBalanceOf,
      AeraProvisionerV2.solveRequestsVaultTwo, AeraProvisionerV2._solveRequestVault,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow, activeOf, requestKindOf, escrowAmountOf,
      fixedPriceOf,
      depositEscrowOf, unitEscrowOf, depositKind, redeemKind, noOutcome,
      vaultSolveOutcome, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hDistinct, hDistinct', hFirstActiveRaw,
      hSecondActiveNe, hFirstKindRaw, hSecondKindRaw, hFirstAmountRaw,
      hSecondAmountRaw, hSecondCoveredRaw, hRemainingRaw]
    decide
  · have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
    have hFirstKindRaw : s.storageMap 1 firstKey = 1 := by
      simpa [requestKindOf, redeemKind] using hFirstRedeem
    have hSecondKindRaw : s.storageMap 1 secondKey = 1 := by
      simpa [requestKindOf, redeemKind] using hSecondRedeem
    have hSecondCoveredRaw : secondAmount.val <= (s.storage 4).val := by
      simpa [escrowAmountOf, escrowBalanceOf, requestKindOf, hSecondKindRaw,
        depositKind, redeemKind, unitEscrowOf, hOneNeZero, hSecondAmountRaw]
        using hSecondCoveredAmount
    have hRemainingRaw : firstAmount <= sub (s.storage 4) secondAmount := by
      simpa [escrowBalanceOf, requestKindOf, hFirstKindRaw, depositKind,
        redeemKind, unitEscrowOf, hOneNeZero] using hRemaining
    simp [guarded_batch_failure_preserves_active_escrow_spec,
      activeEscrowCovered, escrowBalanceOf,
      AeraProvisionerV2.solveRequestsVaultTwo, AeraProvisionerV2._solveRequestVault,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow, activeOf, requestKindOf, escrowAmountOf,
      fixedPriceOf,
      depositEscrowOf, unitEscrowOf, depositKind, redeemKind, noOutcome,
      vaultSolveOutcome, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hDistinct, hDistinct', hFirstActiveRaw,
      hSecondActiveNe, hFirstKindRaw, hSecondKindRaw, hFirstAmountRaw,
      hSecondAmountRaw, hSecondCoveredRaw, hRemainingRaw, hOneNeZero]
    decide

/-- If a later, opposite-kind vault interaction reverts after an earlier request
    has tentatively settled, whole-batch EVM rollback restores the complete input
    state, including both active escrows. -/
theorem reverting_batch_preserves_active_escrow
    (requestKey otherKey : Address) (s : ContractState)
    (hDistinct : requestKey ≠ otherKey)
    (hActive : activeOf s requestKey = 1)
    (hOtherActive : activeOf s otherKey = 1)
    (hKinds :
      (requestKindOf s requestKey = depositKind ∧
        requestKindOf s otherKey = redeemKind) ∨
      (requestKindOf s requestKey = redeemKind ∧
        requestKindOf s otherKey = depositKind))
    (hCovered : activeEscrowCovered s requestKey)
    (hOtherCovered : activeEscrowCovered s otherKey) :
    reverting_batch_preserves_active_escrow_spec requestKey otherKey s := by
  have hDistinct' : otherKey ≠ requestKey := Ne.symm hDistinct
  rcases hCovered with ⟨_, hAmount⟩
  rcases hOtherCovered with ⟨_, hOtherAmount⟩
  have hActiveRaw : s.storageMap 0 requestKey = 1 := by
    simpa [activeOf] using hActive
  have hActiveNe : s.storageMap 0 requestKey ≠ 0 := by
    rw [hActiveRaw]
    decide
  have hOtherActiveRaw : s.storageMap 0 otherKey = 1 := by
    simpa [activeOf] using hOtherActive
  have hOtherActiveNe : s.storageMap 0 otherKey ≠ 0 := by
    rw [hOtherActiveRaw]
    decide
  have hOneNeZero : (1 : Uint256) ≠ 0 := by decide
  rcases hKinds with ⟨hDeposit, hOtherRedeem⟩ | ⟨hRedeem, hOtherDeposit⟩
  · have hAmount' : escrowAmountOf s requestKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hDeposit, depositKind] using hAmount
    have hOtherAmount' : escrowAmountOf s otherKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hOtherRedeem, depositKind, redeemKind, hOneNeZero]
        using hOtherAmount
    have hDepositRaw : s.storageMap 1 requestKey = 0 := by
      simpa [requestKindOf, depositKind] using hDeposit
    have hOtherRedeemRaw : s.storageMap 1 otherKey = 1 := by
      simpa [requestKindOf, redeemKind] using hOtherRedeem
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hAmount'
    have hOtherAmountRaw : (s.storageMap 2 otherKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hOtherAmount'
    simp [reverting_batch_preserves_active_escrow_spec,
      AeraProvisionerV2.solveRequestsVaultTwo, AeraProvisionerV2._solveRequestVault,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, hActiveNe, hOtherActiveNe, hDistinct, hDistinct',
      hDepositRaw, hOtherRedeemRaw, hAmountRaw, hOtherAmountRaw, hOneNeZero]
  · have hAmount' : escrowAmountOf s requestKey <= unitEscrowOf s := by
      simpa [escrowBalanceOf, hRedeem, depositKind, redeemKind, hOneNeZero] using hAmount
    have hOtherAmount' : escrowAmountOf s otherKey <= depositEscrowOf s := by
      simpa [escrowBalanceOf, hOtherDeposit, depositKind] using hOtherAmount
    have hRedeemRaw : s.storageMap 1 requestKey = 1 := by
      simpa [requestKindOf, redeemKind] using hRedeem
    have hOtherDepositRaw : s.storageMap 1 otherKey = 0 := by
      simpa [requestKindOf, depositKind] using hOtherDeposit
    have hAmountRaw : (s.storageMap 2 requestKey).val <= (s.storage 4).val := by
      simpa [escrowAmountOf, unitEscrowOf] using hAmount'
    have hOtherAmountRaw : (s.storageMap 2 otherKey).val <= (s.storage 3).val := by
      simpa [escrowAmountOf, depositEscrowOf] using hOtherAmount'
    simp [reverting_batch_preserves_active_escrow_spec,
      AeraProvisionerV2.solveRequestsVaultTwo, AeraProvisionerV2._solveRequestVault,
      AeraProvisionerV2._escrowBalance, AeraProvisionerV2._setEscrowBalance,
      AeraProvisionerV2.active, AeraProvisionerV2.requestKind,
      AeraProvisionerV2.escrowAmount, AeraProvisionerV2.fixedPrice,
      AeraProvisionerV2.depositEscrow,
      AeraProvisionerV2.unitEscrow, getStorage, setStorage, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, hActiveNe, hOtherActiveNe, hDistinct, hDistinct', hRedeemRaw,
      hOtherDepositRaw, hAmountRaw, hOtherAmountRaw, hOneNeZero]

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
