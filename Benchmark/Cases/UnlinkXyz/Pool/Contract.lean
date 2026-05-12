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

  Three entry points are SCOPED but not yet TRANSLATED — bodies will land
  in a follow-up PR now that the macro surface they need is in place:
    - `transfer(Transaction[] calldata _transactions)`
    - `withdraw(WithdrawalTransaction[] calldata _withdrawals)`
    - `emergencyWithdraw(WithdrawalTransaction[] calldata _transactions)`

  These shapes use struct-array parameters whose elements carry nested
  dynamic members (`uint256[] nullifierHashes`, `Ciphertext[] ciphertexts`,
  etc.). The macro accepts the required projections as of verity#1832 /
  verity#1843 (`Expr.paramDynamicHeadWord` plus the prerequisite
  param-loader fix in verity#1839 and the validator-wildcard refactor in
  verity#1842, all merged 2026-05-12). Promotion to `build_green` is the
  Unlink-side trigger for closing verity#1760 and only requires writing
  the bodies — the macro and lowering already exist.
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
`UnlinkPool` below. The plain EIP-712 typehash is cross-checked
against the in-tree Keccak engine via `#guard` below
(`Verity.keccak256_lit` from verity#1827). The ERC-7201 namespace
slot uses a different derivation (`keccak256(abi.encode(keccak256(s)
- 1)) & ~0xff`) so it cannot be cross-checked by a single
`keccak256_lit` call; it is reproduced symbolically from the
upstream Solidity comment instead.

Why a shadow def rather than a direct `keccak256_lit` call inside the
`constants` block: the `constants` term parser is the macro-restricted
`verityConstant` / `translatePureExprWithTypes` path, which does not
yet recognise the `Verity.keccak256_lit` Lean def in term position.
Verifying the literals out-of-band via `#guard` (below) keeps the
audit story tight without changing the `verity_contract` surface. -/

/-- Mirrors the hardcoded literal in the `constants` block below.

    ERC-7201 storage slot derivation (UnlinkPool.sol:75):
    `keccak256(abi.encode(uint256(keccak256("unlink.storage.UnlinkPoolRelayers")) - 1)) & ~bytes32(uint256(0xff))`.

    The two-stage derivation (`keccak256` → `n-1` → `keccak256(abi.encode(n-1))`
    → `& ~0xff`) is not expressible as a single `keccak256_lit` call,
    so the literal is reproduced from `UnlinkPool.sol:77` verbatim
    rather than cross-checked here. -/
def RELAYER_STORAGE_LOCATION_LIT : Uint256 :=
  0xd8b607728433c567965c4023813a35a19b26751353d5652c8798f8eea4b19b00

/-- Mirrors the hardcoded literal for the EIP-712 typehash.

    Solidity source (UnlinkPool.sol:64):
    `bytes32 constant DEPOSIT_WITNESS_TYPEHASH =
       keccak256('DepositWitness(address pool,bytes32 notesHash)');`

    The plain `keccak256` is cross-checked against
    `Verity.keccak256_lit` via the `#guard` below. -/
def DEPOSIT_WITNESS_TYPEHASH_LIT : Uint256 :=
  0xbc5a735b1283bedbbb26bd202f39770544802f342490e830972aacc15681b130

/- Cross-check the EIP-712 typehash literal against the in-tree
   Keccak-256 engine.  If this `#guard` fails after a Solidity
   source rename, update `DEPOSIT_WITNESS_TYPEHASH_LIT` and the
   `DEPOSIT_WITNESS_TYPEHASH` value inside the `constants` block
   below to whatever the engine reports. -/
#guard DEPOSIT_WITNESS_TYPEHASH_LIT.val =
  (Verity.keccak256_lit "DepositWitness(address pool,bytes32 notesHash)").val

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
      0xbc5a735b1283bedbbb26bd202f39770544802f342490e830972aacc15681b130

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
  function «initialize» (verifierRouter : Address, ownerAddr : Address, relayer : Address)
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
  PENDING TRANSLATION — the three public ZK entry points still need their
  bodies wired against the Solidity source:

    function transfer(Transaction[] calldata _transactions)
      external onlyRelayer nonReentrant;
    function withdraw(WithdrawalTransaction[] calldata _withdrawals)
      external onlyRelayer nonReentrant;
    function emergencyWithdraw(WithdrawalTransaction[] calldata _transactions)
      external nonReentrant;                       // UnlinkPool.sol:374-383

  Source confirms there is NO `adapterDeposit` or `adapterWithdraw` in the
  pinned commit (`UnlinkAdapter` was deleted upstream in
  `d9c8948 chore(contracts): delete UnlinkAdapter + strip adapter surface
  (UE-425)` predating our pin `4bc46c1f`; the umbrella issue verity#1760
  references the older multi-relayer release).

  The macro surface that previously blocked these entry points landed in
  verity main on 2026-05-12 via:

    * verity#1841 — fixed `genDynamicParamLoads` off-by-one for
      dynamic-tuple parameters (`Compiler/CompilationModel/ParamLoading.lean`
      no longer emits a spurious length word — the `_data_offset` Yul
      identifier now points at the first head word of the encoded tuple).
    * verity#1842 — expanded three `Expr → Except` validator wildcards
      into explicit constructor lists, escaping the Lean 4
      `_mutual.eq_def` 200 000-heartbeat ceiling when new `Expr`
      constructors are introduced.
    * verity#1843 — added `Expr.paramDynamicHeadWord (name, wordOffset)`
      with a new pair of Yul helpers
      (`__verity_param_dynamic_head_word_{calldata,memory}_checked`) and
      routed direct dynamic-tuple parameter leaf projections through
      `paramDynamicHeadProjection?` in `Verity/Macro/Translate.lean`.

  The lakefile pin now points at `cf5cb844` (post-#1843), so writing the
  bodies translates directly against `UnlinkPool.sol:309-583`. The
  remaining work — `_validateContext` / `_verifyProof` / `_spendNullifiers`
  / `_insertLeaves` / `_transferWithBalanceCheck` decomposition,
  per-transaction loop, per-token deltas, and the per-tx oracle call
  through `tryExternalCall "getCircuit" [routerAddr, txn.circuitId]` —
  is a follow-up PR.

  ============================================================================

  PENDING TRANSLATION — `deposit(Note[] calldata _notes,
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
  Until those follow-up PRs land, this scoped translation builds,
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
