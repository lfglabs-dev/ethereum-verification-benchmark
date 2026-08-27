import Verity.Specs.Common
import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Contract

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

/-- Source replay-protection bit. -/
def activeOf (s : ContractState) (requestKey : Address) : Uint256 :=
  s.storageMap 0 requestKey

/-- Hash-committed deposit/redeem discriminator in the model. -/
def requestKindOf (s : ContractState) (requestKey : Address) : Uint256 :=
  s.storageMap 1 requestKey

/-- Hash-committed escrow amount in the model. -/
def escrowAmountOf (s : ContractState) (requestKey : Address) : Uint256 :=
  s.storageMap 2 requestKey

/-- Hash-committed fixed-price discriminator used by direct settlement. -/
def fixedPriceOf (s : ContractState) (requestKey : Address) : Uint256 :=
  s.storageMap 3 requestKey

/-- Aggregate deposit-token custody snapshot. -/
def depositEscrowOf (s : ContractState) : Uint256 := s.storage 3

/-- Aggregate vault-unit custody snapshot. -/
def unitEscrowOf (s : ContractState) : Uint256 := s.storage 4

/-- The aggregate custody channel selected by a request kind. -/
def escrowBalanceOf (s : ContractState) (kind : Uint256) : Uint256 :=
  if kind == depositKind then depositEscrowOf s else unitEscrowOf s

/-- A request is active and its committed amount is covered by the matching
    aggregate escrow channel. -/
def activeEscrowCovered (s : ContractState) (requestKey : Address) : Prop :=
  activeOf s requestKey = 1 ∧
    escrowAmountOf s requestKey <= escrowBalanceOf s (requestKindOf s requestKey)

/-- A direct replay is rejected either by the fixed-price gate or by the cleared
    active request marker. -/
def directReplayRejected (result : ContractResult Uint256) (s : ContractState) : Prop :=
  result = ContractResult.success noOutcome s ∨
    result = ContractResult.revert "NotFixedPrice" s

/-- Successful vault settlement is terminal: it consumes the active bit once,
    and every immediate terminal replay is ignored or rejected. -/
def vault_solve_terminal_exclusivity_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  let first := (AeraProvisionerV2.solveRequestVault requestKey true true true).run s
  let settled := first.snd
  let vaultReplay := (AeraProvisionerV2.solveRequestVault requestKey true true true).run settled
  let directReplay := (AeraProvisionerV2.solveRequestDirect requestKey true true).run settled
  let refundReplay := (AeraProvisionerV2.refundRequest requestKey true true).run settled
  let cancelReplay := (AeraProvisionerV2.cancelRequest requestKey true true).run settled
  first = ContractResult.success vaultSolveOutcome settled ∧
    activeOf settled requestKey = 0 ∧
    vaultReplay = ContractResult.success noOutcome settled ∧
    directReplayRejected directReplay settled ∧
    refundReplay = ContractResult.revert "HashNotFound" settled ∧
    cancelReplay = ContractResult.revert "HashNotFound" settled

/-- Successful direct settlement has the same one-terminal-outcome property. -/
def direct_solve_terminal_exclusivity_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  let first := (AeraProvisionerV2.solveRequestDirect requestKey true true).run s
  let settled := first.snd
  let vaultReplay := (AeraProvisionerV2.solveRequestVault requestKey true true true).run settled
  let directReplay := (AeraProvisionerV2.solveRequestDirect requestKey true true).run settled
  let refundReplay := (AeraProvisionerV2.refundRequest requestKey true true).run settled
  let cancelReplay := (AeraProvisionerV2.cancelRequest requestKey true true).run settled
  first = ContractResult.success directSolveOutcome settled ∧
    activeOf settled requestKey = 0 ∧
    vaultReplay = ContractResult.success noOutcome settled ∧
    directReplayRejected directReplay settled ∧
    refundReplay = ContractResult.revert "HashNotFound" settled ∧
    cancelReplay = ContractResult.revert "HashNotFound" settled

/-- An expired vault-solve entry follows the source refund branch and consumes the
    request exactly once. -/
def expired_vault_solve_refund_terminal_exclusivity_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  let first := (AeraProvisionerV2.solveRequestVault requestKey true false true).run s
  let settled := first.snd
  let vaultReplay := (AeraProvisionerV2.solveRequestVault requestKey true false true).run settled
  let directReplay := (AeraProvisionerV2.solveRequestDirect requestKey false true).run settled
  let refundReplay := (AeraProvisionerV2.refundRequest requestKey true true).run settled
  let cancelReplay := (AeraProvisionerV2.cancelRequest requestKey true true).run settled
  first = ContractResult.success refundOutcome settled ∧
    activeOf settled requestKey = 0 ∧
    vaultReplay = ContractResult.success noOutcome settled ∧
    directReplayRejected directReplay settled ∧
    refundReplay = ContractResult.revert "HashNotFound" settled ∧
    cancelReplay = ContractResult.revert "HashNotFound" settled

/-- An expired fixed-price direct-solve entry follows the source refund branch and
    consumes the request exactly once. -/
def expired_direct_solve_refund_terminal_exclusivity_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  let first := (AeraProvisionerV2.solveRequestDirect requestKey false true).run s
  let settled := first.snd
  let vaultReplay := (AeraProvisionerV2.solveRequestVault requestKey true false true).run settled
  let directReplay := (AeraProvisionerV2.solveRequestDirect requestKey false true).run settled
  let refundReplay := (AeraProvisionerV2.refundRequest requestKey true true).run settled
  let cancelReplay := (AeraProvisionerV2.cancelRequest requestKey true true).run settled
  first = ContractResult.success refundOutcome settled ∧
    activeOf settled requestKey = 0 ∧
    vaultReplay = ContractResult.success noOutcome settled ∧
    directReplayRejected directReplay settled ∧
    refundReplay = ContractResult.revert "HashNotFound" settled ∧
    cancelReplay = ContractResult.revert "HashNotFound" settled

/-- Successful authorized/expired refund is terminal and excludes every solve or
    cancellation replay. -/
def refund_terminal_exclusivity_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  let first := (AeraProvisionerV2.refundRequest requestKey true true).run s
  let settled := first.snd
  let vaultReplay := (AeraProvisionerV2.solveRequestVault requestKey true true true).run settled
  let directReplay := (AeraProvisionerV2.solveRequestDirect requestKey true true).run settled
  let refundReplay := (AeraProvisionerV2.refundRequest requestKey true true).run settled
  let cancelReplay := (AeraProvisionerV2.cancelRequest requestKey true true).run settled
  first = ContractResult.success refundOutcome settled ∧
    activeOf settled requestKey = 0 ∧
    vaultReplay = ContractResult.success noOutcome settled ∧
    directReplayRejected directReplay settled ∧
    refundReplay = ContractResult.revert "HashNotFound" settled ∧
    cancelReplay = ContractResult.revert "HashNotFound" settled

/-- Successful cancellation is terminal and excludes every solve or refund
    replay. Cancellation fee plus net refund consumes one full escrow record. -/
def cancellation_terminal_exclusivity_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  let first := (AeraProvisionerV2.cancelRequest requestKey true true).run s
  let settled := first.snd
  let vaultReplay := (AeraProvisionerV2.solveRequestVault requestKey true true true).run settled
  let directReplay := (AeraProvisionerV2.solveRequestDirect requestKey true true).run settled
  let refundReplay := (AeraProvisionerV2.refundRequest requestKey true true).run settled
  let cancelReplay := (AeraProvisionerV2.cancelRequest requestKey true true).run settled
  first = ContractResult.success cancellationOutcome settled ∧
    activeOf settled requestKey = 0 ∧
    vaultReplay = ContractResult.success noOutcome settled ∧
    directReplayRejected directReplay settled ∧
    refundReplay = ContractResult.revert "HashNotFound" settled ∧
    cancelReplay = ContractResult.revert "HashNotFound" settled

/-- One reader-facing invariant over every modeled terminal route. Live vault
    solve, refund, and cancellation apply to active deposit or redemption
    requests. Direct routes additionally require the hash-committed fixed-price
    bit. Each route consumes the active marker and excludes every later terminal
    route for the same activation. -/
def active_request_cannot_be_consumed_twice_spec
    (requestKey : Address) (s : ContractState) : Prop :=
  vault_solve_terminal_exclusivity_spec requestKey s ∧
    expired_vault_solve_refund_terminal_exclusivity_spec requestKey s ∧
    refund_terminal_exclusivity_spec requestKey s ∧
    cancellation_terminal_exclusivity_spec requestKey s ∧
    (fixedPriceOf s requestKey = 1 →
      direct_solve_terminal_exclusivity_spec requestKey s ∧
      expired_direct_solve_refund_terminal_exclusivity_spec requestKey s)

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
