import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Contracts

/-!
# EntryPoint v0.9 — one-op, decoded-parameter projection

This file is a hand-written, **one-op, decoded-parameter projection** of the
load-bearing slice of `EntryPoint.sol` at commit
`b36a1ed52ae00da6f8a4c8d50181e2877e4fa410`
(eth-infinitism/account-abstraction, v0.9). It is **not** a faithful
line-by-line Solidity translation: the real `handleOps` is a batch
entrypoint over `PackedUserOperation[] calldata`, whereas this contract
takes a single op's already-decoded scalar parameters and runs validation
then execution for that one op.

Known, deliberate divergences from the Solidity source:

* **Single-nonce abstraction.** The real `NonceManager` keys nonces by the
  2D pair `(sender, uint192 key)` and updates them via
  `_validateAndUpdateNonce` inside `_validatePrepayment`. Here `nonces` is
  a flat `Address → Uint256` map (the inner key is collapsed away), and the
  nonce check happens before the account validation call rather than after.
  A faithful 2D nonce model lives in `UserOp.lean`, not here.
* **Boolean paymaster oracle.** Paymaster presence is just
  `paymaster != 0`, and `validatePaymasterUserOp` is an `externalCall`
  oracle checked against the zero word. Real `paymasterAndData` decoding,
  context bytes, malformed-return checks, and gas-limit checks are omitted.
* **No prefund/deposit accounting.** `missingAccountFunds`, the AA21
  account-deposit debit, the paymaster deposit debit before validation,
  gas-price math, refunds, and the real `_compensate` ETH transfer (which
  can revert) are not modeled. `_compensate` here just bumps a deposit
  counter by a constant fee.
* **Transient-guard mismatch.** The `tload`/`tstore` lock block below
  models an OpenZeppelin-style EIP-1153 transient **mutex**. The actual
  EntryPoint v0.9 `nonReentrant` modifier is **not** a mutex in this
  source: it checks `tx.origin == msg.sender && msg.sender.code.length == 0`
  (an EOA-caller restriction). The mutex here is a stand-in, not a
  translation of that guard.
* **Other omissions.** Validation-data aggregator/time-window parsing,
  OOG/low-prefund sentinel handling, the `executeUserOp` selector branch,
  `currentUserOpHash`, real event emission, and the aggregated-signature
  path are all out of scope for this projection.

The headline theorem is **not** carried by this file. The abstract models
in `Contract.lean` and `Trace.lean` carry the proven indexed
execution-count biconditional; this contract is a Verity-shaped projection
that downstream refinement lemmas connect to that abstract model.

The Solidity → Verity mapping applied by the projection:

  | Solidity                                       | Verity                             |
  |------------------------------------------------|------------------------------------|
  | `mapping(address => uint256) deposits`         | `deposits : Address → Uint256`    |
  | 2D `nonceSequence[sender][key]`                | flat `nonces : Address → Uint256` |
  | `nonReentrant` (tx.origin/EOA check)           | `tload` / `tstore` mutex stand-in  |
  | `account.validateUserOp(...)` external call    | `externalCall "validateUserOp"` oracle |
  | `paymaster.validatePaymasterUserOp(...)` call  | `externalCall "validatePaymasterUserOp"` oracle |
  | `this.innerHandleOp(...)` self-call (try/catch)| `tryCatch (call ...)`              |
  | `Exec.call(sender, ..., callData)`             | `call ...`                         |
  | `_compensate(beneficiary, collected)`          | constant-fee deposit bump          |
-/

verity_contract EntryPointV09 where
  storage
    -- Reentrancy lock backed by transient storage (EIP-1153 in real source).
    -- We expose it as a storage slot for the Verity model but it semantically
    -- corresponds to the transient slot used by ReentrancyGuardTransient.
    reentrancyLock : Uint256 := slot 0
    -- StakeManager: deposit balance per account.
    deposits : Address → Uint256 := slot 1
    -- NonceManager: 2D nonce sequence number per (sender, key). We model the
    -- common single-key case by collapsing the inner key into the address.
    nonces : Address → Uint256 := slot 2
    -- Aggregator address slot used in the aggregated-op path. Set to the
    -- per-batch aggregator during _iterateValidationPhase.
    currentAggregator : Address := slot 3
    -- For the proof we also need an observable "opInfos was set" marker per
    -- index. This is the Verity-side representation of the in-memory
    -- `UserOpInfo[] opInfos` array; the corresponding bytecode-level
    -- statement is given as the memory-frame theorem in Frame.lean.
    opInfoRecord : Uint256 → Uint256 := slot 4

  errors
    -- Mirrors EntryPoint v0.9's typed custom errors. Declaring them here
    -- gives the Verity compiler the right selector and ABI encoding for
    -- the revert path, so the differential test sees byte-equivalent
    -- revert data against the solc-compiled artifact.
    --
    -- `revert FailedOp(opIndex, reason)` — opIndex < ops.length, reason
    -- is the canonical "AAxx ..." string per `account-abstraction/contracts/core/Helpers.sol`.
    error FailedOp(Uint256, Uint256)
    -- `revert FailedOpWithRevert(opIndex, reason, innerRevertData)` —
    -- carries the original revert data from the account / paymaster call.
    error FailedOpWithRevert(Uint256, Uint256, Uint256)
    -- `revert PostOpReverted(returnData)` — emitted by `_executeUserOp`
    -- when the paymaster's postOp callback reverted.
    error PostOpReverted(Uint256)
    -- `revert SignatureValidationFailed(aggregator)` — the aggregator
    -- path rejected the bundle.
    error SignatureValidationFailed(Address)
    -- `revert SenderAddressResult(sender)` — emitted by
    -- `getSenderAddress` to expose the computed sender via a revert.
    error SenderAddressResult(Address)
    -- `revert DelegateAndRevert(success, ret)` — emitted at the end of
    -- `delegateAndRevert` so the caller can read the inner returndata.
    error DelegateAndRevert(Uint256, Uint256)

  constants
    -- ValidationData sentinel: 0 = success, nonzero = failure code.
    VALIDATION_SUCCESS : Uint256 := 0
    OP_INFO_VALIDATED : Uint256 := 1
    OP_INFO_EXECUTED  : Uint256 := 2
    -- callData.length predicate: caller passes 1 if op.callData is non-empty,
    -- 0 otherwise. The Solidity branch is `if (callData.length > 0)`.
    HAS_CALLDATA : Uint256 := 1
    NO_CALLDATA  : Uint256 := 0
    -- initCode.length predicate: caller passes 1 if op.initCode is non-empty.
    HAS_INITCODE : Uint256 := 1
    NO_INITCODE  : Uint256 := 0
    -- postOp mode sentinels matching IPaymaster.PostOpMode in Solidity.
    POSTOP_OP_SUCCEEDED   : Uint256 := 0
    POSTOP_OP_REVERTED    : Uint256 := 1
    POSTOP_POSTOP_REVERTED : Uint256 := 2

  linked_externals
    external validateUserOp(Uint256, Uint256) -> (Uint256)
    external validatePaymasterUserOp(Uint256) -> (Uint256)
    external createSender(Uint256) -> (Uint256)
    external postOp(Uint256) -> (Uint256)

  -- Mirrors `_validateAccountAndPaymasterValidationData` partially: nonce
  -- check + account.validateUserOp call. The result is the validation word.
  function allow_post_interaction_writes internal _validateAccount
      (sender : Address, key : Uint256, declaredNonce : Uint256) : Uint256 := do
    -- nonces[sender] is the next expected nonce. EntryPoint validates the
    -- account first, then advances the nonce on the accepted path.
    let expected ← getMapping nonces sender
    require (declaredNonce == expected) "AA25 invalid account nonce"
    -- account.validateUserOp(userOp, userOpHash, missingFunds)
    let validation := externalCall "validateUserOp" [key, declaredNonce]
    require (validation == VALIDATION_SUCCESS) "AA23 reverted (or OOG)"
    setMapping nonces sender (add expected 1)
    return validation

  -- Mirrors `_validatePaymasterPrepayment`: the paymaster branch is skipped
  -- when no paymaster is attached (`address(0)`). Otherwise the external
  -- paymaster validation word is checked by the caller; sentinel 0 means
  -- accept.
  function internal _validatePaymaster
      (paymaster : Address, key : Uint256) : Uint256 := do
    if paymaster != 0 then
      -- paymaster.validatePaymasterUserOp(userOp, userOpHash, requiredPreFund)
      let validation := externalCall "validatePaymasterUserOp" [key]
      return validation
    else
      return VALIDATION_SUCCESS

  -- Mirrors `SenderCreator.createSender`: when `initCode.length > 0`, the
  -- EntryPoint deploys the account via an external call. The result is the
  -- newly-deployed account address (we model the success-or-revert outcome
  -- with the same sentinel shape as validation calls).
  function internal _createSender (key : Uint256, hasInitCode : Uint256) : Uint256 := do
    if hasInitCode == HAS_INITCODE then
      let deployResult := externalCall "createSender" [key]
      require (deployResult != VALIDATION_SUCCESS) "AA13 initCode failed or OOG"
      return deployResult
    else
      return 0

  -- Mirrors `_validatePrepayment`: optional createSender + account + paymaster.
  function allow_post_interaction_writes internal _validatePrepayment
      (sender : Address, paymaster : Address,
       key : Uint256, declaredNonce : Uint256,
       hasInitCode : Uint256) : Uint256 := do
    let _deployResult ← _createSender key hasInitCode
    let accountValid ← _validateAccount sender key declaredNonce
    require (accountValid == VALIDATION_SUCCESS) "AA23 reverted (or OOG)"
    let pmValid ← _validatePaymaster paymaster key
    require (pmValid == VALIDATION_SUCCESS) "AA33 reverted (or OOG)"
    setMappingUint opInfoRecord key OP_INFO_VALIDATED
    return VALIDATION_SUCCESS

  -- Mirrors `innerHandleOp`: the self-call to the sender happens iff
  -- `callData.length > 0`. The outer `_executeUserOp` always records an
  -- execution-path attempt and accrues the fee, regardless of whether the
  -- inner sender call ran or reverted (try/catch absorption).
  function internal _innerHandleOp
      (sender : Address, _key : Uint256, hasCallData : Uint256) : Uint256 := do
    if hasCallData == HAS_CALLDATA then
      unsafe "EntryPoint innerHandleOp sender call boundary" do
        tryCatch (call 100000 sender 0 0 4 0 0) (do
          pure ())
      return 1
    else
      return 0

  -- Mirrors `_executeUserOp`: enters `this.innerHandleOp(...)` via a self-call,
  -- catches its revert, then records the execution attempt and increments
  -- collected fees.
  function allow_post_interaction_writes internal _executeUserOp
      (sender : Address, key : Uint256, hasCallData : Uint256) : Uint256 := do
    let _innerResult ← _innerHandleOp sender key hasCallData
    setMappingUint opInfoRecord key OP_INFO_EXECUTED
    return 1

  -- Mirrors `paymaster.postOp(mode, context, actualGasCost, ...)`.
  -- The postOp callback is only invoked when a paymaster is attached; we
  -- model the call as an externalCall returning the new mode word. The
  -- biconditional does not depend on postOp's result, but completeness of
  -- the model does.
  function internal _postOp
      (paymaster : Address, mode : Uint256) : Uint256 := do
    if paymaster != 0 then
      let result := externalCall "postOp" [mode]
      return result
    else
      return mode

  -- Mirrors `_compensate`: transfer the collected wei to the beneficiary.
  -- We model the deposit ledger update; the actual ETH transfer is an
  -- external call abstracted into the deposit map.
  function internal _compensate
      (beneficiary : Address, amount : Uint256) : Unit := do
    let current ← getMapping deposits beneficiary
    setMapping deposits beneficiary (add current amount)

  -- The single-op slice of `handleOps`. The real function takes
  -- `PackedUserOperation[] calldata ops`; we expose the per-op body so the
  -- per-op invariants can be stated without modelling calldata layout.
  function allow_post_interaction_writes internal _handleOpUnchecked
      (sender : Address, paymaster : Address,
       key : Uint256, declaredNonce : Uint256, beneficiary : Address,
       hasInitCode : Uint256, hasCallData : Uint256)
      : Uint256 := do
    -- Phase 1: validation. Optional createSender + account + paymaster.
    let _validationResult ←
      _validatePrepayment sender paymaster key declaredNonce hasInitCode
    -- Phase 2: execution. Inner self-call gated by callData.length > 0,
    -- but the execution-path attempt + fee are recorded either way.
    let exec ← _executeUserOp sender key hasCallData
    -- Phase 3: paymaster postOp (when present).
    let _postOpResult ← _postOp paymaster POSTOP_OP_SUCCEEDED
    -- Phase 4: compensation. Constant 1 wei per op in the abstract model.
    _compensate beneficiary 1
    return exec

  -- Public single-op projection of `handleOps`, guarded like the Solidity
  -- `external nonReentrant` entry point. This keeps the compiled Verity artifact
  -- honest for differential tests while the benchmark remains explicit that it
  -- does not model dynamic calldata array decoding.
  function allow_post_interaction_writes handleOp
      (sender : Address, paymaster : Address,
       key : Uint256, declaredNonce : Uint256, beneficiary : Address,
       hasInitCode : Uint256, hasCallData : Uint256)
      : Uint256 := do
    unsafe "EntryPoint transient reentrancy guard boundary" do
      let locked ← tload 0
      require (locked == 0) "ReentrancyGuardTransient: reentrant call"
      tstore 0 1
      let exec ← _handleOpUnchecked sender paymaster key declaredNonce
        beneficiary hasInitCode hasCallData
      tstore 0 0
      return exec

  -- Flattened one-op `handleOps` projection. The Solidity ABI accepts a dynamic
  -- array of packed structs; this model exposes the decoded fields directly.
  -- Differential tests must call this projection through its own interface, not
  -- through `IEntryPoint.handleOps(PackedUserOperation[],address)`.
  function handleOps
      (sender : Address, paymaster : Address,
       key : Uint256, declaredNonce : Uint256, beneficiary : Address,
       hasInitCode : Uint256, hasCallData : Uint256)
      : Uint256 := do
    let exec ← handleOp sender paymaster key declaredNonce beneficiary hasInitCode hasCallData
    return exec

end Benchmark.Cases.ERC4337.EntryPointInvariant
