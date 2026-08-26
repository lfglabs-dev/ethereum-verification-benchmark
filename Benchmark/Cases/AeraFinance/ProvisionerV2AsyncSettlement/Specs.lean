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

/-- Successful request creation establishes the active escrow state consumed by
    the terminal exclusivity theorems below. -/
def create_request_establishes_active_escrow_spec
    (requestKey : Address) (kind amount : Uint256) (isFixedPrice : Bool)
    (s : ContractState) : Prop :=
  let result :=
    (AeraProvisionerV2.createRequest requestKey kind amount isFixedPrice true).run s
  let s' := result.snd
  result = ContractResult.success () s' ∧
    activeOf s' requestKey = 1 ∧
    requestKindOf s' requestKey = kind ∧
    escrowAmountOf s' requestKey = amount ∧
    fixedPriceOf s' requestKey = (if isFixedPrice then 1 else 0) ∧
    activeEscrowCovered s' requestKey

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

/-- In a two-request vault batch, a guarded failure preserves the first active
    deposit and its committed amount while a distinct second request settles. -/
def guarded_batch_failure_preserves_active_escrow_spec
    (firstKey secondKey : Address) (firstAmount secondAmount : Uint256)
    (s : ContractState) : Prop :=
  let result :=
    (AeraProvisionerV2.solveRequestsVaultTwo
      firstKey secondKey false true true true true true).run s
  let s' := result.snd
  result = ContractResult.success vaultSolveOutcome s' ∧
    activeOf s' firstKey = 1 ∧
    activeOf s' secondKey = 0 ∧
    requestKindOf s' firstKey = requestKindOf s firstKey ∧
    escrowAmountOf s' firstKey = firstAmount ∧
    escrowBalanceOf s' (requestKindOf s firstKey) =
      sub (escrowBalanceOf s (requestKindOf s firstKey)) secondAmount ∧
    firstAmount <= escrowBalanceOf s' (requestKindOf s firstKey) ∧
    activeEscrowCovered s' firstKey ∧
    escrowAmountOf s secondKey = secondAmount

/-- If an external interaction makes the vault batch revert after the source has
    tentatively cleared a hash, EVM atomicity restores the full input state. -/
def reverting_batch_preserves_active_escrow_spec
    (requestKey otherKey : Address) (s : ContractState) : Prop :=
  (AeraProvisionerV2.solveRequestsVaultTwo
      requestKey otherKey true true true true true false).run s =
    ContractResult.revert "ExternalInteractionFailed" s

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
