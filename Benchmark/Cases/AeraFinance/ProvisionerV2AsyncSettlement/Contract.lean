/-
Source-faithful lifecycle slice for Aera Finance V3 `ProvisionerV2` async
`RequestV2` settlement.

Pinned upstream:
`aera-finance/aera-contracts-public@f0ebc15985b2f19d1e599b604370fdbaeb314180`
`v3/src/core/ProvisionerV2.sol`.

Simplifications and boundaries:

* `bytes32` request hashes are represented by collision-free `Address` keys. The
  model assumes distinct keys for distinct ABI-packed `RequestV2` payloads. It
  does not prove Keccak collision resistance.
* `asyncRequestHashes[key]` is represented exactly by `active[key]`. The request
  kind, escrow amount, and fixed-price bit are ghost decompositions of fields
  committed by the hash. Solidity receives those fields again in calldata rather
  than storing them separately. The theorem starts from one active activation;
  request creation and later reactivation are outside the model, so it does not
  claim lifetime uniqueness for a reusable request hash.
* Deposit-token and vault-unit escrow balances are modeled as local aggregate
  counters. Aggregate coverage is an execution premise, not a proof of
  per-request escrow provenance. In Solidity these balances live in two external
  ERC-20 contracts. The model assumes successful ERC-20 calls move the requested
  amount exactly, with no fee-on-transfer, rebasing, callback, or false-success
  behavior.
* Price conversion, deposit-cap calculation, cancellation-fee calculation,
  authorization, deadlines, token enablement, and other policy checks are not
  recomputed. Vault eligibility is summarized by `guardsPass`; refund and
  cancellation gates are explicit booleans; direct-route eligibility is limited
  by the hash-committed fixed-price bit and the theorem premises. The invariant
  concerns terminal consumption after those source gates permit the route.
* Events, approvals, solver-tip aggregation, receivers, and exact payout routing
  are omitted. `requestIsLive` preserves the source deadline branch: live
  requests solve and expired requests refund. Terminal outcome codes are return
  witnesses for the corresponding source events.
* `interactionSucceeds` represents the external vault/token boundary after the
  source clears the active hash. `Contract.run` preserves EVM atomicity: failure
  rolls the complete call back to its input state.
-/

import Contracts.Common

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-- Ghost request kind: zero is deposit, one is redeem. -/
def depositKind : Uint256 := 0
def redeemKind : Uint256 := 1

/-- Proof outcome witnesses. Zero means no terminal outcome. -/
def noOutcome : Uint256 := 0
def vaultSolveOutcome : Uint256 := 1
def directSolveOutcome : Uint256 := 2
def refundOutcome : Uint256 := 3
def cancellationOutcome : Uint256 := 4

verity_contract AeraProvisionerV2 where
  storage
    -- Source `asyncRequestHashes`.
    active : Address → Uint256 := slot 0
    -- Ghost decomposition of hash-committed request fields.
    requestKind : Address → Uint256 := slot 1
    escrowAmount : Address → Uint256 := slot 2
    -- Ghost decomposition of `RequestV2.isFixedPrice`.
    fixedPrice : Address → Uint256 := slot 3
    -- External ERC-20 balance abstractions for the provisioner's custody.
    depositEscrow : Uint256 := slot 3
    unitEscrow : Uint256 := slot 4

  function internal _escrowBalance (kind : Uint256) : Uint256 := do
    if kind == 0 then
      let balance ← getStorage depositEscrow
      return balance
    else
      let balance ← getStorage unitEscrow
      return balance

  function internal _setEscrowBalance (kind : Uint256, amount : Uint256) : Unit := do
    if kind == 0 then
      setStorage depositEscrow amount
    else
      setStorage unitEscrow amount

  -- One `_solveRequestsVault` loop iteration. Source guard failures return
  -- without clearing the hash. An invalid hash also returns without effect.
  function internal _solveRequestVault
      (requestKey : Address, guardsPass : Bool, requestIsLive : Bool,
       interactionSucceeds : Bool) : Uint256 := do
    if guardsPass then
      let oldActive ← getMapping active requestKey
      if oldActive == 0 then
        return 0
      else
        let kind ← getMapping requestKind requestKey
        let amount ← getMapping escrowAmount requestKey
        let oldEscrow ← _escrowBalance kind
        require (oldEscrow >= amount) "EscrowUnderflow"
        setMapping active requestKey 0
        _setEscrowBalance kind (sub oldEscrow amount)
        require interactionSucceeds "ExternalInteractionFailed"
        if requestIsLive then return 1 else return 3
    else
      return 0

  function solveRequestVault
      (requestKey : Address, guardsPass : Bool, requestIsLive : Bool,
       interactionSucceeds : Bool) : Uint256 := do
    let outcome ← _solveRequestVault requestKey guardsPass requestIsLive interactionSucceeds
    return outcome

  -- Source `_solveRequestDirect`: an invalid hash returns; otherwise the hash
  -- is cleared before the external exchange, whose failure reverts the call.
  function solveRequestDirect
      (requestKey : Address, requestIsLive : Bool, interactionSucceeds : Bool) : Uint256 := do
    let isFixedPrice ← getMapping fixedPrice requestKey
    require (isFixedPrice != 0) "NotFixedPrice"
    let oldActive ← getMapping active requestKey
    if oldActive == 0 then
      return 0
    else
      let kind ← getMapping requestKind requestKey
      let amount ← getMapping escrowAmount requestKey
      let oldEscrow ← _escrowBalance kind
      require (oldEscrow >= amount) "EscrowUnderflow"
      setMapping active requestKey 0
      _setEscrowBalance kind (sub oldEscrow amount)
      require interactionSucceeds "ExternalInteractionFailed"
      if requestIsLive then return 2 else return 3

  -- Source `refundRequest`: authorization/deadline is the explicit gate;
  -- missing active hashes revert.
  function refundRequest
      (requestKey : Address, authorizedOrExpired : Bool, transferSucceeds : Bool) : Uint256 := do
    require authorizedOrExpired "DeadlineInFutureAndUnauthorized"
    let oldActive ← getMapping active requestKey
    require (oldActive != 0) "HashNotFound"
    let kind ← getMapping requestKind requestKey
    let amount ← getMapping escrowAmount requestKey
    let oldEscrow ← _escrowBalance kind
    require (oldEscrow >= amount) "EscrowUnderflow"
    setMapping active requestKey 0
    _setEscrowBalance kind (sub oldEscrow amount)
    require transferSucceeds "SafeERC20FailedOperation"
    return 3

  -- Source `cancelRequest`: all cancellation gates and fee computations are
  -- summarized by `cancellationAllowed`; fee plus net refund consumes the full
  -- escrow amount.
  function cancelRequest
      (requestKey : Address, cancellationAllowed : Bool, transferSucceeds : Bool) : Uint256 := do
    require cancellationAllowed "CancellationNotAllowed"
    let oldActive ← getMapping active requestKey
    require (oldActive != 0) "HashNotFound"
    let kind ← getMapping requestKind requestKey
    let amount ← getMapping escrowAmount requestKey
    let oldEscrow ← _escrowBalance kind
    require (oldEscrow >= amount) "EscrowUnderflow"
    setMapping active requestKey 0
    _setEscrowBalance kind (sub oldEscrow amount)
    require transferSucceeds "SafeERC20FailedOperation"
    return 4

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
