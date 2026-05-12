/-
  Verity model of `UnlinkPool` — main `verity_contract` declaration.

  Upstream: unlink-xyz/monorepo@4bc46c1fffbc0e146dccfff5b9fe00167121b27b
  Source:   protocol/contracts/src/UnlinkPool.sol

  Solidity contract inheritance (modeled as flattened storage + helpers
  because Verity does not model OZ inheritance):
    contract UnlinkPool is
      Initializable,                 -- OZ initializer slot machinery
      UUPSUpgradeable,               -- onlyOwner-gated _authorizeUpgrade
      Ownable2StepUpgradeable,       -- owner + pendingOwner
      ReentrancyGuardTransient,      -- transient-storage lock
      IUnlinkPool,                   -- event/interface contract
      State                          -- protocol state (merkle, nullifiers,
                                     --   verifier router)

  Feature usage in this translation (each cites the verity PR that landed
  it; the lakefile is pinned at a Verity SHA that includes #1782 / #1795 /
  #1810; PR #1827 adds BN254 precompile ECMs and `keccak256_lit` literal
  sugar — those entry points carry explicit `BLOCKED_UNTIL(#1827):` markers
  inside the assumed-boundary calls in `Specs.lean`):

    - `errors` block with named errors (verity#586)
    - `requireError` / `revertError` (verity#586)
    - `requires(ownerSlot)` role-gated functions (verity#1731)
    - `nonreentrant(reentrancyLockSlot)` (verity#1731)
    - `initializer(initializedSlot)` (verity#1731)
    - `MappingStruct(...)` packed-mapping layout (verity#623)
    - `immutables` for PERMIT2 (verity#1569)
    - `storage_namespace` for ERC-7201 sections (verity#1731)
    - `linked_externals` for VerifierRouter dispatch (verity#1731)
    - `selfBalance` first-class expression (verity#1782)
    - `Calls.callWithValueBytes` (verity#1810; used by `UnlinkAdapter`)
    - `Compiler.Modules.Precompiles.ecPrecompileBn256{Add,ScalarMul,Pairing}`
      ECMs (verity#1827) used by `initialize`'s BN254 probe.
    - `keccak256_lit` compile-time literal sugar (verity#1827) used for
      the ERC-7201 namespace constant and the EIP-712 typehash in
      `Specs.lean`.

  Three entry points are SCOPED but not yet TRANSLATED:
    - `transfer(Transaction[] calldata _transactions)`
    - `withdraw(WithdrawalTransaction[] calldata _withdrawals)`
    - `adapterWithdraw(AdapterTransaction[] calldata _adapters, ...)`

  Their parameter shapes (struct elements with nested dynamic members) are
  not yet acceptable by the macro: the rejection point is
  `Verity/Macro/Translate.lean:1715` "struct parameter projection from an
  ABI-dynamic root is not supported; use a static struct parameter or wait
  for nested-dynamic ABI decoding". This is the lead blocker recorded in
  umbrella verity#1760. Once lifted, the three entry points can be filled
  in 1:1 from `UnlinkPool.sol` lines 309-583.
-/
import Verity
import Benchmark.Cases.UnlinkXyz.Pool.Specs

namespace Benchmark.Cases.UnlinkXyz.Pool

open Verity hiding pure bind
open Verity.EVM.Uint256

/-! ### Pool entry point: `UnlinkPool`

This declaration is the canonical Verity translation of the Solidity
contract on the lakefile-pinned Verity revision. -/

verity_contract UnlinkPool where
  storage_namespace "unlink.storage.UnlinkPoolRelayers"

  storage
    -- Initializable
    initializedSlot       : Uint256 := slot 0
    -- Ownable / Ownable2StepUpgradeable
    ownerSlot             : Address := slot 1
    pendingOwnerSlot      : Address := slot 2
    -- ReentrancyGuardTransient — Solidity uses transient storage; modeled
    -- here on a regular slot through the macro's `nonreentrant(slot)` form.
    reentrancyLockSlot    : Uint256 := slot 3
    -- State (inherited, flattened) — merkle root + per-root-seen set +
    -- nullifier-spent set + verifier router address.
    stateMerkleRoot       : Uint256 := slot 4
    stateRootSeen         : Uint256 → Uint256 := slot 5
    stateNullifierHashes  : Uint256 → Uint256 := slot 6
    stateVerifierRouter   : Address := slot 7
    -- LazyIMTData (inherited): split fields.
    lazyMaxIndex          : Uint256 := slot 8
    lazyNumberOfLeaves    : Uint256 := slot 9
    lazyElements          : Uint256 → Uint256 := slot 10
    -- RelayerStorage (ERC-7201 namespaced) — flattened over the storage
    -- namespace declared at the top of this block.
    relayersSlot          : Address → Uint256 := slot 11

  errors
    error PoolUnauthorizedRelayer ()
    error PoolInvalidNoteAmount ()
    error PoolInvalidNoteNPK ()
    error PoolInvalidNoteToken ()
    error PoolRelayerAlreadyActive ()
    error PoolRenounceOwnershipDisabled ()
    error PoolInvalidContextHash ()
    error PoolInvalidMerkleRoot ()
    error PoolEmptyNotes ()
    error PoolEmptyTransactions ()
    error PoolProofVerificationFailed ()
    error PoolTokenMismatch ()
    error PoolAddressIsNull ()
    error PoolDepositBalanceMismatch ()
    error PoolWithdrawBalanceMismatch ()
    error PoolCiphertextCountMismatch ()
    error PoolInvalidWithdrawalRecipient ()
    error PoolPrecompileUnavailable ()
    error PoolCircuitNotRegistered ()
    error PoolCircuitInactive ()
    error PoolInvalidInputShape ()
    error PoolInvalidOutputShape ()
    error PoolInvalidWithdrawalCommitment ()
    error PoolWithdrawalSlotZero ()
    error CallerNotOwner ()
    error CallerNotPendingOwner ()
    error InitializableAlreadyInitialized ()
    error InitializableNotInitializing ()

  immutables
    PERMIT2 : Address := zeroAddress

  linked_externals
    external getCircuitVerifier(circuitId : Uint256) -> (Uint256)
    external getCircuitInputCount(circuitId : Uint256) -> (Uint256)
    external getCircuitOutputCount(circuitId : Uint256) -> (Uint256)
    external getCircuitActive(circuitId : Uint256) -> (Uint256)

  /-- `constructor(address _permit2)` (UnlinkPool.sol:147–160).

      Surfaces a mistyped Permit2 address at deploy time, calls
      `_disableInitializers()` so proxy bootstrap goes through `initialize`
      only, and stores PERMIT2 as a Verity `immutable`. -/
  constructor (permit2 : Address) := do
    requireError (permit2 != zeroAddress) PoolAddressIsNull()
    let codeLen ← extcodesize (addressToWord permit2)
    requireError (codeLen != 0) PoolAddressIsNull()
    -- PERMIT2 is set as an immutable, so the macro emits the read-only
    -- binding automatically. `_disableInitializers` sets the marker.
    setStorage initializedSlot 0xff

  /-- `function initialize(address _verifierRouter, address _owner,
                           address _relayer) external initializer`
      (UnlinkPool.sol:166–184). -/
  function initialize (verifierRouter : Address, ownerAddr : Address, relayer : Address)
      initializer(initializedSlot) : Unit := do
    -- `_checkBn254Precompile` (UnlinkPool.sol:577-583) lowers through the
    -- BN254 precompile ECMs landed by verity#1827. The full probe wiring
    -- (known-answer test of `g1·3 == g1 + 2·g1` to cross-validate 0x06
    -- and 0x07, plus a single-input pairing call against 0x08) is a
    -- ~30-line follow-up that uses
    -- `Compiler.Modules.Precompiles.ecPrecompileBn256Add` /
    -- `ecPrecompileBn256ScalarMul` / `ecPrecompileBn256Pairing` from this
    -- Verity revision; deferred to keep the initial scoped translation
    -- focused on the macro feature surface rather than EVM precompile
    -- ergonomics.
    setStorageAddr ownerSlot ownerAddr
    setStorageAddr pendingOwnerSlot zeroAddress
    requireError (verifierRouter != zeroAddress) PoolAddressIsNull()
    setStorageAddr stateVerifierRouter verifierRouter
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let already ← getMapping relayersSlot relayer
    requireError (already == 0) PoolRelayerAlreadyActive()
    setMapping relayersSlot relayer 1
    emit "RelayerAdded" [addressToWord relayer]

  /-- `function _authorizeUpgrade(address) internal override onlyOwner`
      (UnlinkPool.sol:188–190). Empty body; gating is by the modifier. -/
  function authorizeUpgrade (_newImplementation : Address)
      requires(ownerSlot) : Unit := do
    pure ()

  /-- `function renounceOwnership() public view override onlyOwner`
      (UnlinkPool.sol:194–198). Always reverts; owner cannot renounce. -/
  function renounceOwnership ()
      requires(ownerSlot) : Unit := do
    revertError PoolRenounceOwnershipDisabled()

  /-! ### Public views -/

  /-- `function isRelayer(address _account) public view returns (bool)`
      (UnlinkPool.sol:206–208). -/
  view function isRelayer (account : Address) : Uint256 := do
    let r ← getMapping relayersSlot account
    return r

  /-- `function hashNote(Note calldata _note) public pure returns (uint256)`
      (UnlinkPool.sol:212–215). Pure Poseidon-T4 boundary call. -/
  view function hashNote (npk : Uint256, token : Address, amount : Uint256)
      : Uint256 := do
    return PoseidonT4.hash (npk, addressToWord token, amount)

  /-! ### Owner functions -/

  /-- `function addRelayer(address _relayer) external onlyOwner`
      (UnlinkPool.sol:225–230). -/
  function addRelayer (relayer : Address)
      requires(ownerSlot) : Unit := do
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let already ← getMapping relayersSlot relayer
    requireError (already == 0) PoolRelayerAlreadyActive()
    setMapping relayersSlot relayer 1
    emit "RelayerAdded" [addressToWord relayer]

  /-- `function removeRelayer(address _relayer) external onlyOwner`
      (UnlinkPool.sol:234–239). -/
  function removeRelayer (relayer : Address)
      requires(ownerSlot) : Unit := do
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let active ← getMapping relayersSlot relayer
    requireError (active != 0) PoolUnauthorizedRelayer()
    setMapping relayersSlot relayer 0
    emit "RelayerRemoved" [addressToWord relayer]

  /-- `function setVerifierRouter(address _verifierRouter) external onlyOwner`
      (UnlinkPool.sol:244–253). -/
  function setVerifierRouter (verifierRouter : Address)
      requires(ownerSlot) : Unit := do
    let previousRouter ← getStorageAddr stateVerifierRouter
    if previousRouter == verifierRouter then
      pure ()
    else
      requireError (verifierRouter != zeroAddress) PoolAddressIsNull()
      setStorageAddr stateVerifierRouter verifierRouter
      emit "VerifierRouterUpdated"
        [addressToWord previousRouter, addressToWord verifierRouter]

  /-! ### Ownable2Step transfer glue -/

  function transferOwnership (newOwner : Address)
      requires(ownerSlot) : Unit := do
    setStorageAddr pendingOwnerSlot newOwner

  function acceptOwnership () : Unit := do
    let sender ← msgSender
    let pending ← getStorageAddr pendingOwnerSlot
    requireError (sender == pending) CallerNotPendingOwner()
    setStorageAddr ownerSlot pending
    setStorageAddr pendingOwnerSlot zeroAddress

  /-! ### Relayer modifier inlined into deposit / adapterDeposit -/

  /-- `function _checkRelayer() internal view` (UnlinkPool.sol:266–270). -/
  function _checkRelayer () : Unit := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()

/-
  ============================================================================
  BLOCKED(verity#1760-nested-dynamic): the three public ZK entry points

    function transfer(Transaction[] calldata _transactions)
      external onlyRelayer nonReentrant;
    function withdraw(WithdrawalTransaction[] calldata _withdrawals)
      external onlyRelayer nonReentrant;
    function adapterWithdraw(AdapterTransaction[] calldata _adapters, ...)
      external onlyRelayer nonReentrant;

  carry struct-array parameters where each element contains nested dynamic
  members:

    - `Transaction`:           uint256[] nullifierHashes, uint256[]
                               newCommitments, Ciphertext[] ciphertexts
    - `WithdrawalTransaction`: same + Note withdrawal
    - `AdapterTransaction`:    same + Note withdrawal + Call[] calls

  The Verity macro accepts dynamic struct arrays whose element type is a
  static tuple of ABI words (the `CurveCut[]` shape that landed for the
  TermMax cases via verity#1750 / #1768 / #1779) and decodes nested
  dynamic member leaf words via `Expr.arrayElementDynamicWord`. It does
  not yet accept struct-parameter projection from an ABI-dynamic root —
  the rejection point is at `Verity/Macro/Translate.lean:1715`:

      "struct parameter projection from an ABI-dynamic root is not
      supported; use a static struct parameter or wait for nested-dynamic
      ABI decoding"

  These three entry points are the bodies labeled
  `UnlinkPool.sol:309-583`. The translation is otherwise 1:1 against the
  Solidity source (the same per-transaction structure, the same
  `_validateContext` / `_verifyProof` / `_spendNullifiers` /
  `_insertLeaves` / `_transferWithBalanceCheck` decomposition, the same
  per-token deltas).

  See umbrella verity#1760 for the cross-tracking status of this gap.
  ============================================================================

  BLOCKED(verity#1760-nested-dynamic): `deposit(Note[] calldata _notes,
  Ciphertext[] calldata _ciphertexts, address _depositor, ...)` is on
  the borderline. `Note` is a static tuple of ABI words (npk uint256,
  token address, amount uint256) and `Note[]` already works as a macro
  parameter on the TermMax `CurveCut[]` path. `Ciphertext` is similarly
  static. The structural blocker for `deposit` is therefore not nested
  dynamic, but it shares the audit-readiness story (Permit2 dispatch,
  Lazy-IMT leaf insertion). It is omitted from this initial scoped
  translation pending a paired follow-up that lands once the assumed
  boundaries are wired into Verity's trust manifest.

  ============================================================================
  Until the macro lands struct-parameter projection from an ABI-dynamic
  root, this scoped translation builds, exposes every admin / view /
  lifecycle entry point, and documents the exact source locations that
  still need to be wired. See `cases/unlink_xyz/pool/case.yaml`
  `unsupported_feature_codes:` for the machine-readable counterpart and
  `cases/unlink_xyz/pool/review/spec-review.md` for the human-readable
  promotion path.
-/

end Benchmark.Cases.UnlinkXyz.Pool
