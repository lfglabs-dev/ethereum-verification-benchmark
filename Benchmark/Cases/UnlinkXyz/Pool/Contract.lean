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

  The relayer/permissionless ZK entry points are now wired through the modern
  array and dynamic struct-array surfaces:
    - `deposit(address, Note[] calldata, Ciphertext[] calldata, ...)`
    - `transfer(Transaction[] calldata _transactions)`
    - `withdraw(WithdrawalTransaction[] calldata _withdrawals)`
    - `emergencyWithdraw(WithdrawalTransaction[] calldata _transactions)`

  The transfer/withdraw shapes use struct-array parameters whose elements
  carry nested dynamic members (`uint256[] nullifierHashes`,
  `Ciphertext[] ciphertexts`, etc.). The remaining fidelity gaps are the parts
  that still need first-class source equivalents in Verity or this model: the
  LazyIMT insertion body behind `_insertLeaves` and the external cryptographic
  / Permit2 boundaries tracked in the case manifest.
-/
import Contracts.Common
import Compiler.ECM
import Compiler.Modules.Hashing
import Compiler.Modules.Precompiles
import Benchmark.Cases.UnlinkXyz.Pool.Specs

namespace Benchmark.Cases.UnlinkXyz.Pool

open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.Modules.Hashing
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

namespace DepositHash

open Compiler.Yul
open Compiler.ECM
open Compiler.Constants (freeMemoryPointer)

/-- Keccak-256 over `abi.encode(arrayA, arrayB)` for two direct dynamic-array
    calldata parameters whose elements have fixed static word widths. -/
def abiEncodeTwoStaticArraysModule
    (resultVar arrayA arrayB : String) (elementWordsA elementWordsB : Nat) :
    ExternalCallModule where
  name := "abiEncodeTwoStaticArrays"
  numArgs := 2
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm",
    "abi_standard_two_dynamic_arrays_static_element_layout"]
  compile := fun ctx args => do
    let (lenA, lenB) ← match args with
      | [lenA, lenB] => pure (lenA, lenB)
      | _ => throw s!"abiEncodeTwoStaticArrays expects 2 length arguments, got {args.length}"
    if arrayA.isEmpty || arrayB.isEmpty then
      throw "abiEncodeTwoStaticArrays requires non-empty array parameter names"
    if elementWordsA == 0 || elementWordsB == 0 then
      throw "abiEncodeTwoStaticArrays requires positive element word widths"
    let ptrName := s!"__{resultVar}_abi_two_arrays_ptr"
    let aDataBytesName := s!"__{resultVar}_abi_array_a_data_bytes"
    let bDataBytesName := s!"__{resultVar}_abi_array_b_data_bytes"
    let aTailBytesName := s!"__{resultVar}_abi_array_a_tail_bytes"
    let bTailBytesName := s!"__{resultVar}_abi_array_b_tail_bytes"
    let bHeadOffsetName := s!"__{resultVar}_abi_array_b_head_offset"
    let totalBytesName := s!"__{resultVar}_abi_two_arrays_total_bytes"
    let paddedTotalName := s!"__{resultVar}_abi_two_arrays_padded_total"
    let ptr := YulExpr.ident ptrName
    let aDataBytes := YulExpr.ident aDataBytesName
    let bDataBytes := YulExpr.ident bDataBytesName
    let bHeadOffset := YulExpr.ident bHeadOffsetName
    let totalBytes := YulExpr.ident totalBytesName
    pure [
      YulStmt.block ([
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.let_ aDataBytesName (YulExpr.call "mul" [
          lenA, YulExpr.lit (elementWordsA * 32)
        ]),
        YulStmt.let_ bDataBytesName (YulExpr.call "mul" [
          lenB, YulExpr.lit (elementWordsB * 32)
        ]),
        YulStmt.let_ aTailBytesName (YulExpr.call "add" [YulExpr.lit 32, aDataBytes]),
        YulStmt.let_ bTailBytesName (YulExpr.call "add" [YulExpr.lit 32, bDataBytes]),
        YulStmt.let_ bHeadOffsetName (YulExpr.call "add" [
          YulExpr.lit 64, YulExpr.ident aTailBytesName
        ]),
        YulStmt.let_ totalBytesName (YulExpr.call "add" [
          bHeadOffset, YulExpr.ident bTailBytesName
        ]),
        YulStmt.expr (YulExpr.call "mstore" [ptr, YulExpr.lit 64]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, YulExpr.lit 32], bHeadOffset
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, YulExpr.lit 64], lenA
        ])
      ] ++ dynamicCopyData ctx
        (YulExpr.call "add" [ptr, YulExpr.lit 96])
        (YulExpr.ident s!"{arrayA}_data_offset")
        aDataBytes ++ [
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, bHeadOffset], lenB
        ])
      ] ++ dynamicCopyData ctx
        (YulExpr.call "add" [YulExpr.call "add" [ptr, bHeadOffset], YulExpr.lit 32])
        (YulExpr.ident s!"{arrayB}_data_offset")
        bDataBytes ++ [
        YulStmt.let_ paddedTotalName (YulExpr.call "and" [
          YulExpr.call "add" [totalBytes, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [ptr, YulExpr.ident paddedTotalName]
        ]),
        YulStmt.let_ resultVar (YulExpr.call "keccak256" [ptr, totalBytes])
      ])
    ]

end DepositHash

open DepositHash

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

  struct Proof where
    pA : FixedArray Uint256 2,
    pB : FixedArray (FixedArray Uint256 2) 2,
    pC : FixedArray Uint256 2

  struct Note where
    npk : Uint256,
    token : Address,
    amount : Uint256

  struct Ciphertext where
    ephemeralKey : Uint256,
    data : FixedArray Uint256 3

  struct TokenPermissions where
    token : Address,
    amount : Uint256

  struct PermitTransferFrom where
    permitted : TokenPermissions,
    nonce : Uint256,
    deadline : Uint256

  struct Transaction where
    proof : Proof,
    circuitId : Uint256,
    merkleRoot : Uint256,
    nullifierHashes : Array Uint256,
    newCommitments : Array Uint256,
    contextHash : Uint256,
    ciphertexts : Array Ciphertext

  struct WithdrawalTransaction where
    proof : Proof,
    circuitId : Uint256,
    merkleRoot : Uint256,
    nullifierHashes : Array Uint256,
    newCommitments : Array Uint256,
    contextHash : Uint256,
    withdrawal : Note,
    ciphertexts : Array Ciphertext

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

  event_defs
    event Deposited(@indexed depositor : Address, newRoot : Uint256, startIndex : Uint256,
      notes : Array Note, ciphertexts : Array Ciphertext)
    event Transferred(@indexed newRoot : Uint256, startIndex : Uint256,
      commitments : Array Uint256, nullifierHashes : Array Uint256, ciphertexts : Array Ciphertext)
    event Withdrawn(@indexed «to» : Address, note : Note, @indexed newRoot : Uint256,
      startIndex : Uint256, commitments : Array Uint256, nullifierHashes : Array Uint256,
      ciphertexts : Array Ciphertext)
    event EmergencyWithdrawn(@indexed «to» : Address, note : Note, @indexed newRoot : Uint256,
      startIndex : Uint256, commitments : Array Uint256, nullifierHashes : Array Uint256,
      ciphertexts : Array Ciphertext)
    event RelayerAdded(@indexed relayer : Address)
    event RelayerRemoved(@indexed relayer : Address)
    event VerifierRouterUpdated(@indexed previousRouter : Address, @indexed newRouter : Address)

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
  -- `(verifier, inputCount, outputCount, active)`. The first argument is the
  -- stored router address that Solidity obtains through `_getVerifierRouter()`.
  linked_externals
    external getCircuit(Address, Uint256) -> (Uint256, Uint256, Uint256, Uint256)
    external verifySpend(
      Uint256, Uint256, Uint256, Uint256, Uint256, Uint256, Uint256, Uint256,
      Uint256, Uint256, Uint256, Array Uint256, Array Uint256) -> (Bool)
    external permitWitnessTransferFrom(
      Address, Address, Uint256, Uint256, Uint256, Address, Uint256, Address,
      Uint256, Bytes) -> (Bool)

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
  function allow_post_interaction_writes «initialize» (verifierRouter : Address, ownerAddr : Address, relayer : Address)
      initializer(initializedSlot) : Unit := do
    let qMinusG1Y := 21888242871839275222246405745257275088696311157297823662689037894645226208581
    let g2x1 := 11559732032986387107991004021392285783925812861821192530917403151452391805634
    let g2x2 := 10857046999023057135944570762232829481370756359578518086990519993285655852781
    let g2y1 := 4082367875863433681332203403145435568316851327593401208105741076214120093531
    let g2y2 := 8495653923123431417604973247489272438418190587263600148770280649306958101930
    unsafe "_probePairing calldata buffer" do
      mstore 0 1
      mstore 32 2
      mstore 64 g2x1
      mstore 96 g2x2
      mstore 128 g2y1
      mstore 160 g2y2
      mstore 192 1
      mstore 224 qMinusG1Y
      mstore 256 g2x1
      mstore 288 g2x2
      mstore 320 g2y1
      mstore 352 g2y2
    let pairA ← ecmCall Compiler.Modules.Precompiles.bn256PairingModule [0, 384, 0]
    requireError (pairA == 1) PoolPrecompileUnavailable()
    unsafe "_probePairing calldata buffer restore" do
      mstore 0 1
      mstore 32 2
    let pairB ← ecmCall Compiler.Modules.Precompiles.bn256PairingModule [0, 192, 0]
    requireError (pairB == 0) PoolPrecompileUnavailable()
    let twoG1x := 1368015179489954701390400359078579693043519447331113978918064868415326638035
    let twoG1y := 9918110051302171585080402603319702774565515993150576347155970296011118125764
    ecmBind [mul2x, mul2y]
      (Compiler.Modules.Precompiles.bn256ScalarMulModule "mul2x" "mul2y")
      [1, 2, 2]
    requireError (mul2x == twoG1x) PoolPrecompileUnavailable()
    requireError (mul2y == twoG1y) PoolPrecompileUnavailable()
    ecmBind [mul3x, mul3y]
      (Compiler.Modules.Precompiles.bn256ScalarMulModule "mul3x" "mul3y")
      [1, 2, 3]
    requireError ((mul3x != twoG1x) || (mul3y != twoG1y)) PoolPrecompileUnavailable()
    ecmBind [add2x, add2y]
      (Compiler.Modules.Precompiles.bn256AddModule "add2x" "add2y")
      [1, 2, 1, 2]
    requireError (add2x == twoG1x) PoolPrecompileUnavailable()
    requireError (add2y == twoG1y) PoolPrecompileUnavailable()
    ecmBind [add3x, add3y]
      (Compiler.Modules.Precompiles.bn256AddModule "add3x" "add3y")
      [1, 2, twoG1x, twoG1y]
    requireError ((add3x != twoG1x) || (add3y != twoG1y)) PoolPrecompileUnavailable()
    requireError (mul3x == add3x) PoolPrecompileUnavailable()
    requireError (mul3y == add3y) PoolPrecompileUnavailable()
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

  /- `function nextLeafIndex() public view returns (uint256)`
      (State.sol:35-37). -/
  function view nextLeafIndex () : Uint256 := do
    let n ← getStorage lazyNumberOfLeaves
    return n

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

  function validateNoteFields (npk : Uint256, token : Address, amount : Uint256) : Unit := do
    requireError (token != zeroAddress) PoolInvalidNoteToken()
    requireError ((amount != 0) &&
      (amount <=
        100000000000000000000000000000000000000000000000000000000000000000000))
      PoolInvalidNoteAmount()
    requireError ((npk != 0) &&
      (npk <
        21888242871839275222246405745257275088548364400416034343698204186575808495617))
      PoolInvalidNoteNPK()

  function sumNoteAmounts (notes : Array Note) : Uint256 := do
    let mut totalAmount := 0
    forEach "i" (arrayLength notes) (do
      let amount := abiHeadWord (arrayElement notes i) 2
      totalAmount := add totalAmount amount)
    return totalAmount

  function validateAndCollectDeposit
      (notes : Array Note, permitToken : Address) : Array Uint256 := do
    let notesLen := arrayLength notes
    let newLeaves ← allocArray notesLen
    forEach "i" notesLen (do
      let npk := abiHeadWord (arrayElement notes i) 0
      let token := wordToAddress (abiHeadWord (arrayElement notes i) 1)
      let amount := abiHeadWord (arrayElement notes i) 2
      validateNoteFields npk token amount
      requireError (token == permitToken) PoolTokenMismatch()
      let leaf ← hashNote npk token amount
      setMemoryArrayElement newLeaves i leaf)
    returnArray newLeaves

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

  function countNonZero (values : Array Uint256, excludeIndex : Uint256) : Uint256 := do
    let mut count := 0
    forEach "j" (arrayLength values) (do
      if j != excludeIndex then
        let value := arrayElement values j
        if value != 0 then
          count := add count 1
        else
          pure ()
      else
        pure ())
    return count

  function spendNullifiers (nullifierHashes : Array Uint256) : Unit := do
    forEach "k" (arrayLength nullifierHashes) (do
      let nullifierHash := arrayElement nullifierHashes k
      if nullifierHash != 0 then
        setMappingWord stateNullifierHashes nullifierHash 0 1
      else
        pure ())

  function realCommitments
      (newCommitments : Array Uint256, excludeIndex : Uint256)
      : Array Uint256 := do
    let len := arrayLength newCommitments
    let mut count := 0
    forEach "i" len (do
      let commitment := arrayElement newCommitments i
      if i != excludeIndex then
        if commitment != 0 then
          count := add count 1
        else
          pure ()
      else
        pure ())
    let leaves ← allocArray count
    let mut j := 0
    forEach "i" len (do
      let commitment := arrayElement newCommitments i
      if i != excludeIndex then
        if commitment != 0 then
          setMemoryArrayElement leaves j commitment
          j := add j 1
        else
          pure ()
      else
        pure ())
    returnArray leaves

  function realNullifiers (nullifierHashes : Array Uint256) : Array Uint256 := do
    let len := arrayLength nullifierHashes
    let mut count := 0
    forEach "i" len (do
      let nullifierHash := arrayElement nullifierHashes i
      if nullifierHash != 0 then
        count := add count 1
      else
        pure ())
    let real ← allocArray count
    let mut j := 0
    forEach "i" len (do
      let nullifierHash := arrayElement nullifierHashes i
      if nullifierHash != 0 then
        setMemoryArrayElement real j nullifierHash
        j := add j 1
      else
        pure ())
    returnArray real

  /- Source shape: `_insertLeaves(uint256[] memory _leafHashes)`.
     The LazyIMT update is still represented by the existing lightweight
     accumulator used by this scoped benchmark model. -/
  function insertLeaves (leafHashes : Array Uint256) : Uint256 := do
    let startIndex ← nextLeafIndex
    let mut newRoot := startIndex
    forEach "m" (arrayLength leafHashes) (do
      let leaf := arrayElement leafHashes m
      if leaf != 0 then
        newRoot := add newRoot leaf
      else
        pure ())
    setStorage stateMerkleRoot newRoot
    setMappingWord stateRootSeen newRoot 0 1
    setStorage lazyNumberOfLeaves (add startIndex (arrayLength leafHashes))
    return newRoot

  function view computeContextHash (ciphertexts : Array Ciphertext) : Uint256 := do
    let cid ← Verity.chainid
    let selfAddr ← Verity.contractAddress
    let ciphertextsHash ← ecmCall
      (fun resultVar => abiEncodeStaticArrayModule resultVar "ciphertexts" 4)
      [arrayLength ciphertexts]
    -- For these three 32-byte ABI words, `abi.encode` and the static-word
    -- packed layout are byte-identical.
    let rawContext ← ecmCall
      (fun resultVar => abiEncodePackedWordsModule resultVar 3)
      [cid, addressToWord selfAddr, ciphertextsHash]
    return (mod rawContext
      21888242871839275222246405745257275088548364400416034343698204186575808495617)

  function view validateContext
      (merkleRoot : Uint256, contextHash : Uint256, expectedContext : Uint256)
      : Unit := do
    requireError (contextHash == expectedContext) PoolInvalidContextHash()
    let rootSeen ← getMappingWord stateRootSeen merkleRoot 0
    requireError (rootSeen != 0) PoolInvalidMerkleRoot()

  function settleWithdrawalTransfer
      (token : Address, recipient : Address, amount : Uint256) : Unit := do
    let selfAddr ← Verity.contractAddress
    let poolBefore ← balanceOf token selfAddr
    let recipientBefore ← balanceOf token recipient
    safeTransfer token recipient amount
    let poolAfter ← balanceOf token selfAddr
    let recipientAfter ← balanceOf token recipient
    requireError ((sub poolBefore poolAfter) == amount) PoolWithdrawBalanceMismatch()
    requireError ((sub recipientAfter recipientBefore) == amount) PoolWithdrawBalanceMismatch()

  /- `function deposit(address _depositor, Note[] calldata _notes,
      Ciphertext[] calldata _ciphertexts, PermitTransferFrom calldata _permit,
      bytes calldata _signature) external onlyRelayer nonReentrant`
      (UnlinkPool.sol:306-324). -/
  function nonreentrant(reentrancyLockSlot) deposit
      (depositor : Address, notes : Array Note, ciphertexts : Array Ciphertext,
       permit : PermitTransferFrom, signature : Bytes) : Unit := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()
    let notesLen := arrayLength notes
    requireError (notesLen != 0) PoolEmptyNotes()
    requireError ((arrayLength ciphertexts) == notesLen)
      PoolCiphertextCountMismatch()
    let newLeaves ← validateAndCollectDeposit notes permit.permitted.token
    let totalAmount ← sumNoteAmounts notes
    let selfAddr ← Verity.contractAddress
    let notesHash ← ecmCall
      (fun resultVar =>
        abiEncodeTwoStaticArraysModule resultVar "notes" "ciphertexts" 3 4)
      [notesLen, arrayLength ciphertexts]
    let witness ← ecmCall
      (fun resultVar => abiEncodePackedWordsModule resultVar 3)
      [DEPOSIT_WITNESS_TYPEHASH, addressToWord selfAddr, notesHash]
    let token := permit.permitted.token
    let balBefore ← balanceOf token selfAddr
    let (permitCallOk, permitAccepted) ← tryExternalCall "permitWitnessTransferFrom"
      [PERMIT2,
       token,
       permit.permitted.amount,
       permit.nonce,
       permit.deadline,
       selfAddr,
       totalAmount,
       depositor,
       witness,
       signature]
    requireError permitCallOk PoolDepositBalanceMismatch()
    requireError permitAccepted PoolDepositBalanceMismatch()
    let balAfter ← balanceOf token selfAddr
    requireError ((sub balAfter balBefore) == totalAmount)
      PoolDepositBalanceMismatch()
    let startIndex ← nextLeafIndex
    let newRoot ← insertLeaves newLeaves
    emit "Deposited"
      [addressToWord depositor, newRoot, startIndex, notes, ciphertexts]

  /- `function transfer(Transaction[] calldata _transactions) external
      onlyRelayer nonReentrant` (UnlinkPool.sol:328-363). -/
  function nonreentrant(reentrancyLockSlot) transfer (transactions : Array Transaction)
      : Unit := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      let txn := arrayElement transactions i
      let verifierRouter ← getStorageAddr stateVerifierRouter
      let (success, verifier, inputCount, outputCount, active) ←
        tryExternalCall "getCircuit"
          [verifierRouter, txn.circuitId]
      let verifierWord := add verifier 0
      let activeWord := add active 0
      requireError success PoolCircuitNotRegistered()
      requireError (verifierWord != 0) PoolCircuitNotRegistered()
      requireError (activeWord != 0) PoolCircuitInactive()
      requireError ((arrayLength txn.nullifierHashes) == inputCount)
        PoolInvalidInputShape()
      requireError ((arrayLength txn.newCommitments) == outputCount)
        PoolInvalidOutputShape()
      let ciphertextCount ← countNonZero txn.newCommitments
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      requireError ((arrayLength txn.ciphertexts) == ciphertextCount)
        PoolCiphertextCountMismatch()
      let computedContext ← computeContextHash txn.ciphertexts
      validateContext txn.merkleRoot txn.contextHash computedContext
      let (proofOk, ok) ← tryExternalCall "verifySpend"
        [verifierWord,
         abiHeadWord txn 0,
         abiHeadWord txn 1,
         abiHeadWord txn 2,
         abiHeadWord txn 3,
         abiHeadWord txn 4,
         abiHeadWord txn 5,
         abiHeadWord txn 6,
         abiHeadWord txn 7,
         txn.merkleRoot,
         txn.contextHash,
         txn.nullifierHashes,
         txn.newCommitments]
      requireError proofOk PoolProofVerificationFailed()
      requireError ok PoolProofVerificationFailed()
      spendNullifiers txn.nullifierHashes
      let leaves ← realCommitments txn.newCommitments
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      let startIndex ← nextLeafIndex
      let newRoot ← insertLeaves leaves
      let realNullifierHashes ← realNullifiers txn.nullifierHashes
      emit "Transferred"
        [newRoot, startIndex, leaves, realNullifierHashes, txn.ciphertexts])

  /- `_executeWithdrawal(WithdrawalTransaction calldata _txn, bool _emergency)`
      (UnlinkPool.sol:614-666). -/
  function executeWithdrawal (txn : WithdrawalTransaction, emergency : Bool) : Unit := do
    let recipient := wordToAddress txn.withdrawal.npk
    requireError (txn.withdrawal.amount != 0)
      PoolInvalidNoteAmount()
    requireError (txn.withdrawal.npk != 0)
      PoolInvalidNoteNPK()
    requireError (txn.withdrawal.token != zeroAddress)
      PoolInvalidNoteToken()
    requireError (txn.withdrawal.npk <= 0xffffffffffffffffffffffffffffffffffffffff)
      PoolInvalidWithdrawalRecipient()
    let selfAddr ← Verity.contractAddress
    requireError (recipient != selfAddr) PoolInvalidWithdrawalRecipient()
    let verifierRouter ← getStorageAddr stateVerifierRouter
    let (success, verifier, inputCount, outputCount, active) ←
      tryExternalCall "getCircuit" [verifierRouter, txn.circuitId]
    let verifierWord := add verifier 0
    let activeWord := add active 0
    requireError success PoolCircuitNotRegistered()
    requireError (verifierWord != 0) PoolCircuitNotRegistered()
    requireError (activeWord != 0) PoolCircuitInactive()
    requireError ((arrayLength txn.nullifierHashes) == inputCount)
      PoolInvalidInputShape()
    requireError ((arrayLength txn.newCommitments) == outputCount)
      PoolInvalidOutputShape()
    let wSlot := sub outputCount 1
    let withdrawalCommitment := arrayElement txn.newCommitments wSlot
    requireError (withdrawalCommitment != 0) PoolWithdrawalSlotZero()
    let noteHash := add txn.withdrawal.npk txn.withdrawal.amount
    requireError (withdrawalCommitment == noteHash) PoolInvalidWithdrawalCommitment()
    let ciphertextCount ← countNonZero txn.newCommitments wSlot
    requireError ((arrayLength txn.ciphertexts) == ciphertextCount)
      PoolCiphertextCountMismatch()
    let computedContext ← computeContextHash txn.ciphertexts
    validateContext txn.merkleRoot txn.contextHash computedContext
    let (proofOk, ok) ← tryExternalCall "verifySpend"
      [verifierWord,
       abiHeadWord txn 0,
       abiHeadWord txn 1,
       abiHeadWord txn 2,
       abiHeadWord txn 3,
       abiHeadWord txn 4,
       abiHeadWord txn 5,
       abiHeadWord txn 6,
       abiHeadWord txn 7,
       txn.merkleRoot,
       txn.contextHash,
       txn.nullifierHashes,
       txn.newCommitments]
    requireError proofOk PoolProofVerificationFailed()
    requireError ok PoolProofVerificationFailed()
    spendNullifiers txn.nullifierHashes
    let leaves ← realCommitments txn.newCommitments wSlot
    let startIndex ← nextLeafIndex
    let newRoot ← insertLeaves leaves
    settleWithdrawalTransfer txn.withdrawal.token recipient txn.withdrawal.amount
    let realNullifierHashes ← realNullifiers txn.nullifierHashes
    if emergency then
      emit "EmergencyWithdrawn"
        [addressToWord recipient, txn.withdrawal, newRoot, startIndex, leaves,
         realNullifierHashes, txn.ciphertexts]
    else
      emit "Withdrawn"
        [addressToWord recipient, txn.withdrawal, newRoot, startIndex, leaves,
         realNullifierHashes, txn.ciphertexts]

  /- `function withdraw(WithdrawalTransaction[] calldata _transactions)
      external onlyRelayer nonReentrant` (UnlinkPool.sol:365-372). -/
  function nonreentrant(reentrancyLockSlot) withdraw (transactions : Array WithdrawalTransaction)
      : Unit := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      executeWithdrawal (arrayElement transactions i) false)

  /- `function emergencyWithdraw(WithdrawalTransaction[] calldata _transactions)
      external nonReentrant` (UnlinkPool.sol:376-383). -/
  function nonreentrant(reentrancyLockSlot) emergencyWithdraw
      (transactions : Array WithdrawalTransaction) : Unit := do
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      executeWithdrawal (arrayElement transactions i) true)

end Benchmark.Cases.UnlinkXyz.Pool
