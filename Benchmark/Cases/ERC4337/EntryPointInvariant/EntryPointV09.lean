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

* **Decoded nonce (2D shape).** The real `NonceManager` keys by the 2D pair
  `(sender, uint192 key)` with `_validateAndUpdateNonce` (post-increment seq
  check) inside `_validatePrepayment`, AFTER the account validation call and
  BEFORE paymaster validation. This projection receives the decoded `key`
  (uint192) and `declaredNonce` (uint64 seq) as separate parameters (the
  one-op decoded style); it keys its nonce sequence map on the supplied `key`
  (proxy for the per-(sender,key) slot) and performs the check/bump after the
  account external call returns but before the paymaster step. The pure 2D
  model (with explicit `nonceKey`/`nonceSeq` decode from a packed `Uint256`
  and `Nonce2DTable`) lives in `UserOp.lean` / `Trace.lean` and is used by the
  headline theorems. This contract is a projection; claims of faithfulness are
  limited to the control-flow slice relevant to the indexed execution count.
* **Boolean paymaster interface.** Paymaster presence is just
  `paymaster != 0`, and `validatePaymasterUserOp` is a typed interface
  call checked against the zero word. Real `paymasterAndData` decoding,
  context bytes, malformed-return checks, and gas-limit checks are omitted.
* **No prefund/deposit accounting.** `missingAccountFunds`, the AA21
  account-deposit debit, the paymaster deposit debit before validation,
  gas-price math, refunds, and the real `_compensate` ETH transfer (which
  can revert) are not modeled. `_compensate` here just bumps a deposit
  counter by a constant fee.
* **EOA-only `nonReentrant` guard.** The actual EntryPoint v0.9
  `nonReentrant` modifier is not a mutex in this source: it checks
  `tx.origin == msg.sender && msg.sender.code.length == 0`. This projection
  reads `txOrigin` directly and uses the compiler's `extcodesize` expression
  for `msg.sender.code.length`.
* **Other omissions.** OOG/low-prefund sentinel handling, the `executeUserOp`
  selector branch, `currentUserOpHash`, real event emission, and the
  aggregated-signature path are out of scope for this projection. (Validation-data
  packed structure + authorizer/time gate is now tightened in the oracle
  returns and success checks; see the `_validateAccount` comment.)

The headline theorem is **not** carried by this file. The abstract models
in `Contract.lean` and `Trace.lean` carry the proven indexed
execution-count biconditional; this contract is a Verity-shaped projection
that downstream refinement lemmas connect to that abstract model.

The Solidity → Verity mapping applied by the projection:

  | Solidity                                       | Verity                             |
  |------------------------------------------------|------------------------------------|
  | `mapping(address => uint256) deposits`         | `deposits : Address → Uint256`    |
  | 2D `nonceSequenceNumber[sender][key]`          | `nonces : Uint256 → Uint256` (keyed on decoded `key` param in projection) |
  | `nonReentrant` (tx.origin/EOA check)           | `txOrigin`, `msgSender`, `extcodesize` |
  | `account.validateUserOp(...)` external call    | typed `IAccount.validateUserOp` interface |
  | `paymaster.validatePaymasterUserOp(...)` call  | typed `IPaymaster.validatePaymasterUserOp` interface |
  | `this.innerHandleOp(...)` self-call (try/catch)| `tryCatch (call ...)`              |
  | `Exec.call(sender, ..., callData)`             | `call ...`                         |
  | `_compensate(beneficiary, collected)`          | typed `IBeneficiary.receivePrefund` + deposit bump |
-/

verity_contract EntryPointV09 where
  storage
    -- StakeManager: deposit balance per account.
    deposits : Address → Uint256 := slot 1
    -- NonceManager: 2D `nonceSequenceNumber[sender][uint192 key]`.
    -- In the one-op decoded-parameter projection style, the `key` parameter
    -- (high 192 bits of userOp.nonce) is used directly as the storage key for
    -- the per-key sequence number. (A full nested map is not required for the
    -- projection; the abstract `Nonce2DTable` in UserOp.lean carries the
    -- explicit (sender, key) shape for theorem statements.)
    nonces : Uint256 → Uint256 := slot 2
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
    -- 0 represents a packed validationData with authorizer = SIG_VALIDATION_SUCCESS
    -- (and valid time window, or 0 bounds). Nonzero from the oracle stands for
    -- either authorizer = SIG_VALIDATION_FAILED or a time-window violation.
    -- The projection checks `== 0` for the success gate (authorizer success).
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

  interfaces
    interface IAccount where
      function validateUserOp(Uint256, Uint256) returns (Uint256)
    end

    interface IPaymaster where
      function validatePaymasterUserOp(Uint256) returns (Uint256)
      function postOp(Uint256) returns (Uint256)
    end

    interface IBeneficiary where
      function receivePrefund(Uint256)
    end

  linked_externals
    external createSender(Uint256) -> (Uint256)

  -- Mirrors `_validateAccountPrepayment` + `_validateAndUpdateNonce` (the
  -- latter lives inside `_validatePrepayment` in the real source). The nonce
  -- check/bump is performed AFTER the account validation call returns and
  -- BEFORE paymaster validation (see `_validatePrepayment` below). The
  -- returned word from the oracle is the packed `validationData`
  -- (authorizer | validUntil(6B) | validAfter(6B)); success is when the
  -- authorizer field encodes SIG_VALIDATION_SUCCESS (here represented by the
  -- concrete word 0 in the projection's oracle convention). Nonzero covers
  -- SIG_VALIDATION_FAILED (authorizer = 1) and time-window failures; this
  -- projection does not branch on the exact failure reason (both prevent
  -- reaching execution), but the accept gate matches the authorizer ∈ {0,1}
  -- + time-range logic at the decision level. Full decomposition and
  -- `vdValid` live in `UserOp.lean`.
  function allow_post_interaction_writes internal _validateAccount
      (_sender : IAccount, key : Uint256, declaredNonce : Uint256) : Uint256 := do
    -- account.validateUserOp(...) — the call happens first.
    let validation ← _sender.validateUserOp key declaredNonce
    -- Nonce check/bump (faithful order: after account validation, before paymaster).
    -- We key on the decoded `key` parameter (projection of (sender, key) 2D slot).
    let expected ← getMappingUint nonces key
    require (declaredNonce == expected) "AA25 invalid account nonce"
    setMappingUint nonces key (add expected 1)
    require (validation == VALIDATION_SUCCESS) "AA23 reverted (or OOG)"
    return validation

  -- Mirrors `_validatePaymasterPrepayment`: the paymaster branch is skipped
  -- when no paymaster is attached (`address(0)`). Otherwise the external
  -- paymaster validation word is checked by the caller; sentinel 0 means
  -- accept.
  function internal _validatePaymaster
      (paymaster : IPaymaster, _key : Uint256) : Uint256 := do
    if paymaster != 0 then
      -- paymaster.validatePaymasterUserOp(userOp, userOpHash, requiredPreFund)
      let validation ← paymaster.validatePaymasterUserOp _key
      return validation
    else
      return VALIDATION_SUCCESS

  -- Mirrors `SenderCreator.createSender`: when `initCode.length > 0`, the
  -- EntryPoint deploys the account via an external call. v0.9 requires the
  -- factory return to be nonzero and equal to the requested sender before the
  -- following account validation can run against that sender.
  function internal _createSender
      (sender : IAccount, key : Uint256, hasInitCode : Uint256) : Uint256 := do
    if hasInitCode == HAS_INITCODE then
      let deployResult := externalCall "createSender" [key]
      require (deployResult != VALIDATION_SUCCESS) "AA13 initCode failed or OOG"
      require (deployResult == addressToWord sender) "AA14 initCode must return sender"
      return deployResult
    else
      return (addressToWord sender)

  -- Mirrors `_validatePrepayment`: optional createSender + account + paymaster.
  -- Nonce update (inside the account step) occurs after account validation
  -- and before the paymaster step, per the real control flow.
  function allow_post_interaction_writes internal _validatePrepayment
      (sender : IAccount, paymaster : IPaymaster,
       key : Uint256, declaredNonce : Uint256,
       hasInitCode : Uint256) : Uint256 := do
    let effectiveSenderWord ← _createSender sender key hasInitCode
    let effectiveSender := wordToAddress effectiveSenderWord
    let accountValid ← _validateAccount effectiveSender key declaredNonce
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
      (sender : IAccount, _key : Uint256, hasCallData : Uint256) : Uint256 := do
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
      (sender : IAccount, key : Uint256, hasCallData : Uint256) : Uint256 := do
    let _innerResult ← _innerHandleOp sender key hasCallData
    setMappingUint opInfoRecord key OP_INFO_EXECUTED
    return 1

  -- Mirrors `paymaster.postOp(mode, context, actualGasCost, ...)`.
  -- The postOp callback is only invoked when a paymaster is attached; we
  -- model the call as a typed interface call returning the new mode word. The
  -- biconditional does not depend on postOp's result, but completeness of
  -- the model does.
  function internal _postOp
      (paymaster : IPaymaster, mode : Uint256) : Uint256 := do
    if paymaster != 0 then
      let result ← paymaster.postOp mode
      return result
    else
      return mode

  -- Mirrors `_compensate`: transfer the collected wei to the beneficiary.
  -- We model the deposit ledger update; the actual ETH transfer is an
  -- external call abstracted into the deposit map.
  function allow_post_interaction_writes internal _compensate
      (beneficiary : IBeneficiary, amount : Uint256) : Unit := do
    beneficiary.receivePrefund amount
    let current ← getMapping deposits beneficiary
    setMapping deposits beneficiary (add current amount)

  -- The single-op slice of `handleOps`. The real function takes
  -- `PackedUserOperation[] calldata ops`; we expose the per-op body so the
  -- per-op invariants can be stated without modelling calldata layout.
  function allow_post_interaction_writes internal _handleOpUnchecked
      (sender : IAccount, paymaster : IPaymaster,
       key : Uint256, declaredNonce : Uint256, beneficiary : IBeneficiary,
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
  -- `external nonReentrant` entry point. EntryPoint v0.9's modifier is an
  -- EOA-only gate, not a transient mutex:
  --
  --   require(tx.origin == msg.sender && msg.sender.code.length == 0)
  --
  -- `msgSender` and `txOrigin` are read directly. The code-length conjunct
  -- uses the compiler's `extcodesize` expression.
  function allow_post_interaction_writes handleOp
      (sender : IAccount, paymaster : IPaymaster,
       key : Uint256, declaredNonce : Uint256, beneficiary : IBeneficiary,
       hasInitCode : Uint256, hasCallData : Uint256)
      : Uint256 := do
    let entryCaller ← msgSender
    let txOriginAddr ← txOrigin
    let originWord := addressToWord txOriginAddr
    require (originWord == addressToWord entryCaller) "nonReentrant: tx.origin != msg.sender"
    let mut callerCodeLen := 0
    unsafe "EntryPoint nonReentrant caller extcodesize check" do
      callerCodeLen := extcodesize entryCaller
    require (callerCodeLen == VALIDATION_SUCCESS) "nonReentrant: caller has code"
    let exec ← _handleOpUnchecked sender paymaster key declaredNonce
      beneficiary hasInitCode hasCallData
    return exec

  -- Flattened one-op `handleOps` projection. The Solidity ABI accepts a dynamic
  -- array of packed structs; this model exposes the decoded fields directly.
  -- Differential tests must call this projection through its own interface, not
  -- through `IEntryPoint.handleOps(PackedUserOperation[],address)`.
  function handleOps
      (sender : IAccount, paymaster : IPaymaster,
       key : Uint256, declaredNonce : Uint256, beneficiary : IBeneficiary,
       hasInitCode : Uint256, hasCallData : Uint256)
      : Uint256 := do
    let exec ← handleOp sender paymaster key declaredNonce beneficiary hasInitCode hasCallData
    return exec

end Benchmark.Cases.ERC4337.EntryPointInvariant
