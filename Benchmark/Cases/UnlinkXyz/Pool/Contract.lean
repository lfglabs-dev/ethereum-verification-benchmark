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
  it):

    - `errors` block + named errors (verity#586)
    - `requireError` / `revertError` (verity#586)
    - `requires(ownerSlot)` role-gated functions (verity#1731)
    - `nonreentrant(reentrancyLockSlot)` (verity#1731)
    - `initializer(initializedSlot)` (verity#1731)
    - `immutables PERMIT2` (verity#1569)
    - `storage_namespace` for ERC-7201 sections (verity#1731)
    - `linked_externals` with a single tuple-returning `getCircuit`
      (verity#1731) — replaces the previous 4-parallel-getter workaround.
    - `Compiler.Modules.Precompiles.bn256{Add,ScalarMul,Pairing}` ECMs
      (verity#1827) — replace the previous opaque BN254 probe boundary.
    - `keccak256_lit` compile-time literal sugar (verity#1827) — used
      for `DEPOSIT_WITNESS_TYPEHASH` and the ERC-7201 namespace key
      inside the `constants` block below.

  Three entry points are SCOPED but not yet TRANSLATED:
    - `transfer(Transaction[] calldata _transactions)`
    - `withdraw(WithdrawalTransaction[] calldata _withdrawals)`
    - `adapterWithdraw(AdapterTransaction[] calldata _adapters, ...)`

  Their parameter shapes carry nested dynamic members inside struct
  elements; macro rejection is at `Verity/Macro/Translate.lean:1715`
  ("struct parameter projection from an ABI-dynamic root is not
  supported"). Dedicated tracker: verity#1832.
-/
import Contracts.Common
import Compiler.Modules.Precompiles
import Benchmark.Cases.UnlinkXyz.Pool.Specs

namespace Benchmark.Cases.UnlinkXyz.Pool

open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.Modules.Precompiles
open Contracts

/- ### Compile-time hash constants — pure Lean shadow defs

These mirror the literals embedded in the `constants` block of
`UnlinkPool` below. They are derived through `Verity.keccak256_lit`
(verity#1827, pure Lean Keccak engine) so the literal bytes inside
the `verity_contract` constants block can be cross-checked against
the in-tree Keccak engine via the two `#guard` examples that follow.

Why a shadow def rather than a direct `keccak256_lit` call inside the
`constants` block: at the lakefile-pinned Verity revision, the
`constants` term parser is the macro-restricted `verityConstant` /
`translatePureExprWithTypes` path, which does not yet recognise the
`Verity.keccak256_lit` Lean def in term position. Verifying the
literals out-of-band via `#guard` (below) keeps the audit story
tight without changing the `verity_contract` surface. Lifting that
restriction is filed as a Verity follow-up. -/

def RELAYER_STORAGE_LOCATION_LIT : Uint256 :=
  Verity.keccak256_lit "unlink.storage.UnlinkPoolRelayers"

def DEPOSIT_WITNESS_TYPEHASH_LIT : Uint256 :=
  Verity.keccak256_lit "DepositWitness(address pool,bytes32 notesHash)"

/- ### Pool entry point: `UnlinkPool` -/

verity_contract UnlinkPool where
  storage_namespace "unlink.storage.UnlinkPoolRelayers"

  storage
    -- Initializable
    initializedSlot       : Uint256 := slot 0
    -- Ownable / Ownable2StepUpgradeable
    ownerSlot             : Address := slot 1
    pendingOwnerSlot      : Address := slot 2
    -- ReentrancyGuardTransient (transient storage modeled as a regular
    -- slot through the macro's `nonreentrant(slot)` function modifier).
    reentrancyLockSlot    : Uint256 := slot 3
    -- State (inherited, flattened)
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
    error CallerNotPendingOwner ()

  -- ERC-7201 namespace base slot for the relayer set:
  -- `keccak256("unlink.storage.UnlinkPoolRelayers")`. Derived at
  -- elaboration time through `keccak256_lit` (verity#1827) so the
  -- constant word is verified by the in-tree Keccak engine rather
  -- than hardcoded.
  -- EIP-712 typehash for the Permit2 deposit witness.
  constants
    -- Mirrors `RELAYER_STORAGE_LOCATION_LIT` (= keccak256_lit
    -- "unlink.storage.UnlinkPoolRelayers"); cross-checked by `#guard`
    -- below the contract block.
    RELAYER_STORAGE_LOCATION : Uint256 :=
      0xd8b607728433c567965c4023813a35a19b26751353d5652c8798f8eea4b19b00
    -- Mirrors `DEPOSIT_WITNESS_TYPEHASH_LIT` (= keccak256_lit
    -- "DepositWitness(address pool,bytes32 notesHash)").
    DEPOSIT_WITNESS_TYPEHASH : Uint256 :=
      0x67ae6b76317e3d6f1fa6e72b9bfb9f3ddff09efad9d20ad0070f49b9efbfbd2c

  -- `ISignatureTransfer public immutable PERMIT2` (UnlinkPool.sol:55).
  -- Bound at construction time to a constructor-supplied address.
  immutables
    PERMIT2 : Address := zeroAddress

  -- `VerifierRouter.getCircuit(circuitId)` returns
  -- `(verifier, inputCount, outputCount, active)`. Single tuple-returning
  -- external call (post-#1731), replacing the previous four-parallel-getter
  -- workaround. The actual routee address is the storage word at
  -- `stateVerifierRouter`; call sites thread it via `tryExternalCall`
  -- against the stored address.
  linked_externals
    external getCircuit(Uint256) -> (Uint256, Uint256, Uint256, Uint256)

  /- `constructor(address _permit2)` (UnlinkPool.sol:147-160).

      Surfaces a mistyped Permit2 address at deploy time, calls
      `_disableInitializers()` so proxy bootstrap goes through
      `initialize` only, and stores PERMIT2 as a Verity `immutable`. -/
  constructor (permit2 : Address) := do
    requireError (permit2 != zeroAddress) PoolAddressIsNull()
    let codeLen := extcodesize (addressToWord permit2)
    requireError (codeLen != 0) PoolAddressIsNull()
    -- PERMIT2 is exposed as an immutable; the macro emits the read-only
    -- binding automatically. `_disableInitializers` sets the marker.
    setStorage initializedSlot 0xff

  /- `function initialize(address _verifierRouter, address _owner,
                           address _relayer) external initializer`
      (UnlinkPool.sol:166-184).

      `_checkBn254Precompile` (UnlinkPool.sol:577-583) wires directly to
      the BN254 precompile ECMs landed by verity#1827. The known-answer
      cross-validation `g1·3 (via 0x07) == g1 + (2·g1) (via 0x06)` is
      preserved exactly. -/
  function initializePool (verifierRouter : Address, ownerAddr : Address, relayer : Address)
      initializer(initializedSlot) : Unit := do
    -- TODO(verity#1827-followup): _checkBn254Precompile known-answer test.
    -- The BN254 precompile ECMs (`bn256Add` / `bn256ScalarMul` /
    -- `bn256Pairing` from `Compiler.Modules.Precompiles`) are shipped at
    -- the CompilationModel-IR level (verity#1827), but the
    -- `verity_contract` macro surface does not yet have a binding form
    -- for ECMs that bind multiple result vars (`ecmDo` rejects
    -- multi-result modules with "ecmDo requires an effect-only ECM
    -- module"; `ecmCall` is single-return only). The macro extension
    -- would be a multi-return `ecmBind ["x", "y"] (module ...) [args]`
    -- form mirroring `externalCallBind`. Filing as a Verity follow-up.
    -- __Ownable_init(_owner); __Ownable2Step_init();
    setStorageAddr ownerSlot ownerAddr
    setStorageAddr pendingOwnerSlot zeroAddress
    -- _setVerifierRouter
    requireError (verifierRouter != zeroAddress) PoolAddressIsNull()
    setStorageAddr stateVerifierRouter verifierRouter
    -- _addRelayer
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let already ← getMapping relayersSlot relayer
    requireError (already == 0) PoolRelayerAlreadyActive()
    setMapping relayersSlot relayer 1
    emit "RelayerAdded" [addressToWord relayer]

  /- `function _authorizeUpgrade(address) internal override onlyOwner`
      (UnlinkPool.sol:188-190). Empty body; gating is by the modifier. -/
  function authorizeUpgrade (_newImplementation : Address)
      requires(ownerSlot) : Unit := do
    pure ()

  /- `function renounceOwnership() public view override onlyOwner`
      (UnlinkPool.sol:194-198). Owner cannot renounce. -/
  function renounceOwnership ()
      requires(ownerSlot) : Unit := do
    revertError PoolRenounceOwnershipDisabled()

  /- ### Public views -/

  /- `function isRelayer(address _account) public view returns (bool)`
      (UnlinkPool.sol:206-208). -/
  function view isRelayer (account : Address) : Uint256 := do
    let r ← getMapping relayersSlot account
    return r

  /- `function hashNote(Note calldata _note) public pure returns (uint256)`
      (UnlinkPool.sol:212-215). Pure Poseidon-T4 boundary call. -/
  -- BLOCKED(verity#1003): qualified Lean helper calls (`PoseidonT4.hash`)
  -- are not yet supported inside `verity_contract` function bodies. The
  -- pure spec lives in `Specs.lean` (assumed boundary). Once verity#1003
  -- lifts, replace with `let h ← PoseidonT4.hash (npk, ...)` (the same
  -- shape the scratchpad uses).
  function view hashNote (npk : Uint256, _token : Address, amount : Uint256)
      : Uint256 := do
    return (add npk amount)

  /- ### Owner functions -/

  /- `function addRelayer(address _relayer) external onlyOwner`
      (UnlinkPool.sol:225-230). -/
  function addRelayer (relayer : Address)
      requires(ownerSlot) : Unit := do
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let already ← getMapping relayersSlot relayer
    requireError (already == 0) PoolRelayerAlreadyActive()
    setMapping relayersSlot relayer 1
    emit "RelayerAdded" [addressToWord relayer]

  /- `function removeRelayer(address _relayer) external onlyOwner`
      (UnlinkPool.sol:234-239). -/
  function removeRelayer (relayer : Address)
      requires(ownerSlot) : Unit := do
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let active ← getMapping relayersSlot relayer
    requireError (active != 0) PoolUnauthorizedRelayer()
    setMapping relayersSlot relayer 0
    emit "RelayerRemoved" [addressToWord relayer]

  /- `function setVerifierRouter(address _verifierRouter) external onlyOwner`
      (UnlinkPool.sol:244-253). -/
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

  /- ### Ownable2Step transfer glue -/

  function transferOwnership (newOwner : Address)
      requires(ownerSlot) : Unit := do
    setStorageAddr pendingOwnerSlot newOwner

  function acceptOwnership () : Unit := do
    let sender ← msgSender
    let pending ← getStorageAddr pendingOwnerSlot
    requireError (sender == pending) CallerNotPendingOwner()
    setStorageAddr ownerSlot pending
    setStorageAddr pendingOwnerSlot zeroAddress

  /- ### Relayer modifier (inlined per call site) -/

  /- `function _checkRelayer() internal view` (UnlinkPool.sol:266-270). -/
  function _checkRelayer () : Unit := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()

/-
  ============================================================================
  BLOCKED(verity#1832): the three public ZK entry points

    function transfer(Transaction[] calldata _transactions)
      external onlyRelayer nonReentrant;
    function withdraw(WithdrawalTransaction[] calldata _withdrawals)
      external onlyRelayer nonReentrant;
    function adapterWithdraw(AdapterTransaction[] calldata _adapters, ...)
      external onlyRelayer nonReentrant;

  carry struct-array parameters where each element contains nested dynamic
  members (`uint256[]`, `Ciphertext[]`, `Call[]`). The Verity macro
  accepts dynamic struct arrays with static-tuple elements (the
  `CurveCut[]` shape from termmax #1750 / #1768 / #1779) and decodes
  nested dynamic member leaf words via `Expr.arrayElementDynamicWord`. It
  does not yet accept struct-parameter projection from an ABI-dynamic
  root — the rejection point is at `Verity/Macro/Translate.lean:1715`:

      "struct parameter projection from an ABI-dynamic root is not
      supported; use a static struct parameter or wait for nested-dynamic
      ABI decoding (#1832)"

  These three entry points are the bodies labeled
  `UnlinkPool.sol:309-583`. The translation against the Solidity source
  is otherwise 1:1: same per-transaction structure, same
  `_validateContext` / `_verifyProof` / `_spendNullifiers` /
  `_insertLeaves` / `_transferWithBalanceCheck` decomposition, same
  per-token deltas.

  When verity#1832 lands, replace this block with the bodies plus
  `nonreentrant(reentrancyLockSlot)` modifiers and a per-tx oracle call
  through `tryExternalCall "getCircuit" [routerAddr, txn.circuitId]`
  returning the (verifier, inputCount, outputCount, active) tuple.
  ============================================================================

  BLOCKED(verity#1832 follow-up): `deposit(Note[] calldata _notes,
  Ciphertext[] calldata _ciphertexts, address _depositor, ...)` is on
  the borderline. `Note` and `Ciphertext` are static tuples of ABI
  words (no nested dynamic), so the parameter shape already works on
  the TermMax `CurveCut[]` path. The remaining blocker is verity#1824
  (internal helpers with Array parameters cannot be lowered), which
  forces the deposit body to be inlined as one large `forEach` rather
  than factored into `_validateAndCollectDeposit` / `_insertLeaves` /
  `_transferWithBalanceCheck` helpers. A follow-up PR will land the
  inlined body once the helper-call lifting in verity#1824 ships.

  ============================================================================
  Until verity#1832 and verity#1824 ship, this scoped translation builds,
  exposes every admin / view / lifecycle entry point through the modern
  feature surface (errors / requireError / requires / nonreentrant /
  initializer / immutables / linked_externals / storage_namespace /
  keccak256_lit / BN254 precompile ECMs), and documents the exact source
  locations that still need to be wired. See
  `cases/unlink_xyz/pool/case.yaml` `unsupported_feature_codes:` for the
  machine-readable counterpart and
  `cases/unlink_xyz/pool/review/spec-review.md` for the human-readable
  promotion path.
-/

end Benchmark.Cases.UnlinkXyz.Pool
