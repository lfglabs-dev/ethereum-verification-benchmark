/-
  Verity model of `UnlinkPool` — main `verity_contract` declaration.

  Upstream: unlink-xyz/monorepo@7617b3eebcf37ab42124fe570eb7e065cf8c8461
  Source:   protocol/contracts/src/UnlinkPool.sol

  Solidity contract inheritance (modeled as inherited storage roots + helpers
  because Verity does not model OZ inheritance dispatch):
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
    - `requires(ownable_owner)` role-gated functions (verity#1731),
      where `ownable_owner` is the generated role label for
      `ownable.owner`
    - `nonreentrant(reentrancyLockSlot)` (verity#1731)
    - `initializer(initializable.initialized)` (verity#1731)
    - `immutables PERMIT2` (verity#1569)
    - multiple `storage_namespace erc7201` sections for ERC-7201 roots
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
  external cryptographic / Permit2 boundaries tracked in the case manifest.
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
`UnlinkPool` below and the inherited OpenZeppelin upgradeable storage
roots. The plain EIP-712 typehash is cross-checked against the in-tree
Keccak engine via `#guard` below (`Verity.keccak256_lit` from
verity#1827). The ERC-7201 namespace slots use the standard two-stage
derivation (`keccak256(abi.encode(keccak256(s) - 1)) & ~0xff`). They
are guarded below against the Verity macro's derived `.slot` constants.

Why a shadow def rather than a direct `keccak256_lit` call inside the
`constants` block: the `constants` term parser is the macro-restricted
`verityConstant` / `translatePureExprWithTypes` path, which does not
yet recognise the `Verity.keccak256_lit` Lean def in term position.
Verifying the literals out-of-band via `#guard` (below) keeps the
audit story tight without changing the `verity_contract` surface. -/

/-- Mirrors the hardcoded literal in the `constants` block below.

    ERC-7201 storage slot derivation (UnlinkPool.sol:75):
    `keccak256(abi.encode(uint256(keccak256("unlink.storage.UnlinkPoolRelayers")) - 1)) & ~bytes32(uint256(0xff))`.

    This literal is guarded below against the storage namespace used by
    `relayersSlot`. -/
def RELAYER_STORAGE_LOCATION_LIT : Uint256 :=
  0xd8b607728433c567965c4023813a35a19b26751353d5652c8798f8eea4b19b00

/-- ERC-7201 storage root for OZ `InitializableStorage`.

    `keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.Initializable")) - 1)) & ~bytes32(uint256(0xff))`. -/
def INITIALIZABLE_STORAGE_LOCATION_LIT : Uint256 :=
  0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00

/-- ERC-7201 storage root for OZ `OwnableStorage`.

    `keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.Ownable")) - 1)) & ~bytes32(uint256(0xff))`. -/
def OWNABLE_STORAGE_LOCATION_LIT : Uint256 :=
  0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300

/-- ERC-7201 storage root for OZ `Ownable2StepStorage`.

    `keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.Ownable2Step")) - 1)) & ~bytes32(uint256(0xff))`. -/
def OWNABLE2STEP_STORAGE_LOCATION_LIT : Uint256 :=
  0x237e158222e3e6968b72b9db0d8043aacf074ad9f650f0d1606b4d82ee432c00

/-- ERC-7201 storage root for protocol `StateStorage`.

    `keccak256(abi.encode(uint256(keccak256("unlink.storage.State")) - 1)) & ~bytes32(uint256(0xff))`. -/
def STATE_STORAGE_LOCATION_LIT : Uint256 :=
  0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000

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

namespace BoundaryCalls

open Compiler.Yul
open Compiler.ECM
open Compiler.Constants (freeMemoryPointer)

private def permitWitnessTypeStringWords : List Nat := [
  0x4465706f7369745769746e657373207769746e657373294465706f7369745769,
  0x746e657373286164647265737320706f6f6c2c62797465733332206e6f746573,
  0x4861736829546f6b656e5065726d697373696f6e73286164647265737320746f,
  0x6b656e2c75696e7432353620616d6f756e742900000000000000000000000000
]

def permitWitnessTransferFromModule (resultVar : String) : ExternalCallModule where
  name := "permitWitnessTransferFrom"
  numArgs := 11
  resultVars := [resultVar]
  writesState := true
  readsState := true
  axioms := ["permit2_witness_transfer_abi_interface"]
  compile := fun ctx args => do
    let (permit2, token, permittedAmount, nonce, deadline, spender, amount, depositor, witness, signature, signatureLength) ←
      match args with
      | [permit2, token, permittedAmount, nonce, deadline, spender, amount, depositor, witness, signature, signatureLength] =>
          pure (permit2, token, permittedAmount, nonce, deadline, spender, amount, depositor, witness, signature, signatureLength)
      | _ => throw s!"permitWitnessTransferFrom expects 10 source arguments expanding to 11 Yul arguments, got {args.length}"
    let ptrName := s!"__{resultVar}_permit2_ptr"
    let ptr := YulExpr.ident ptrName
    let stringPtrName := s!"__{resultVar}_witness_type_ptr"
    let signaturePtrName := s!"__{resultVar}_signature_ptr"
    let paddedSignatureLengthName := s!"__{resultVar}_signature_padded"
    let totalSizeName := s!"__{resultVar}_total_size"
    let successName := s!"__{resultVar}_success"
    let rdsName := s!"__{resultVar}_rds"
    let staticStores := [
      (0, YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x137c29fe]),
      (4, token),
      (36, permittedAmount),
      (68, nonce),
      (100, deadline),
      (132, spender),
      (164, amount),
      (196, depositor),
      (228, witness),
      (260, YulExpr.lit 320),
      (292, YulExpr.lit 480)
    ].map fun (offset, value) =>
      YulStmt.expr (YulExpr.call "mstore" [
        if offset == 0 then ptr else YulExpr.call "add" [ptr, YulExpr.lit offset],
        value
      ])
    let stringPtr := YulExpr.ident stringPtrName
    let signaturePtr := YulExpr.ident signaturePtrName
    let copySignature := dynamicCopyData ctx
      (YulExpr.call "add" [signaturePtr, YulExpr.lit 32]) signature signatureLength
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block ([
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
      ] ++ staticStores ++ [
        YulStmt.let_ stringPtrName (YulExpr.call "add" [ptr, YulExpr.lit 324]),
        YulStmt.expr (YulExpr.call "mstore" [stringPtr, YulExpr.lit 115])
      ] ++ (permitWitnessTypeStringWords.zipIdx.map fun (word, idx) =>
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [stringPtr, YulExpr.lit (32 * (idx + 1))],
          YulExpr.hex word
        ])) ++ [
        YulStmt.let_ signaturePtrName (YulExpr.call "add" [ptr, YulExpr.lit 484]),
        YulStmt.expr (YulExpr.call "mstore" [signaturePtr, signatureLength])
      ] ++ copySignature ++ [
        YulStmt.let_ paddedSignatureLengthName (YulExpr.call "and" [
          YulExpr.call "add" [signatureLength, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.let_ totalSizeName (YulExpr.call "add" [YulExpr.lit 516, YulExpr.ident paddedSignatureLengthName]),
        YulStmt.let_ successName (YulExpr.call "call" [
          YulExpr.call "gas" [], permit2, YulExpr.lit 0, ptr,
          YulExpr.ident totalSizeName, YulExpr.lit 0, YulExpr.lit 0
        ]),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident successName]) [
          YulStmt.let_ rdsName (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident rdsName]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident rdsName])
        ],
        YulStmt.assign resultVar (YulExpr.lit 1),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "and" [
            YulExpr.call "add" [
              YulExpr.call "add" [ptr, YulExpr.ident totalSizeName],
              YulExpr.lit 31
            ],
            YulExpr.call "not" [YulExpr.lit 31]
          ]
        ])
      ])
    ]

def getCircuitTryModule
    (successVar verifierVar inputCountVar outputCountVar activeVar : String) :
    ExternalCallModule where
  name := "getCircuitTry"
  numArgs := 2
  resultVars := [successVar, verifierVar, inputCountVar, outputCountVar, activeVar]
  writesState := false
  readsState := true
  axioms := ["verifier_router_get_circuit_abi_interface"]
  compile := fun _ctx args => do
    let (verifierRouter, circuitId) ← match args with
      | [verifierRouter, circuitId] => pure (verifierRouter, circuitId)
      | _ => throw s!"getCircuitTry expects 2 arguments, got {args.length}"
    let ptrName := s!"__{successVar}_get_circuit_ptr"
    let ptr := YulExpr.ident ptrName
    pure [
      YulStmt.let_ successVar (YulExpr.lit 0),
      YulStmt.let_ verifierVar (YulExpr.lit 0),
      YulStmt.let_ inputCountVar (YulExpr.lit 0),
      YulStmt.let_ outputCountVar (YulExpr.lit 0),
      YulStmt.let_ activeVar (YulExpr.lit 0),
      YulStmt.block [
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.expr (YulExpr.call "mstore" [ptr, YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x753d1941]]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptr, YulExpr.lit 4], circuitId]),
        YulStmt.assign successVar (YulExpr.call "staticcall" [
          YulExpr.call "gas" [], verifierRouter, ptr, YulExpr.lit 36, ptr, YulExpr.lit 128
        ]),
        YulStmt.assign verifierVar (YulExpr.call "and" [
          YulExpr.call "mload" [ptr],
          YulExpr.hex 0xffffffffffffffffffffffffffffffffffffffff
        ]),
        YulStmt.assign inputCountVar (YulExpr.call "mload" [YulExpr.call "add" [ptr, YulExpr.lit 32]]),
        YulStmt.assign outputCountVar (YulExpr.call "mload" [YulExpr.call "add" [ptr, YulExpr.lit 64]]),
        YulStmt.assign activeVar (YulExpr.call "mload" [YulExpr.call "add" [ptr, YulExpr.lit 96]]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit freeMemoryPointer, YulExpr.call "add" [ptr, YulExpr.lit 128]])
      ]
    ]

def verifySpendTryModule (successVar okVar : String) : ExternalCallModule where
  name := "verifySpendTry"
  numArgs := 15
  resultVars := [successVar, okVar]
  writesState := false
  readsState := true
  axioms := ["spend_verifier_verify_proof_abi_interface", "sha256_public_signal_packing"]
  compile := fun ctx args => do
    let (verifier, pA0, pA1, pB00, pB01, pB10, pB11, pC0, pC1, merkleRoot,
        contextHash, nullifierHashesOffset, nullifierHashesLength, newCommitmentsOffset, newCommitmentsLength) ←
      match args with
      | [verifier, pA0, pA1, pB00, pB01, pB10, pB11, pC0, pC1, merkleRoot,
          contextHash, nullifierHashesOffset, nullifierHashesLength, newCommitmentsOffset, newCommitmentsLength] =>
          pure (verifier, pA0, pA1, pB00, pB01, pB10, pB11, pC0, pC1, merkleRoot,
            contextHash, nullifierHashesOffset, nullifierHashesLength, newCommitmentsOffset, newCommitmentsLength)
      | _ => throw s!"verifySpendTry expects 6 source arguments expanding to 15 Yul arguments, got {args.length}"
    let ptrName := s!"__{successVar}_verify_spend_ptr"
    let packedCursorName := s!"__{successVar}_packed_cursor"
    let hashOutName := s!"__{successVar}_hash_out"
    let pubSignalName := s!"__{successVar}_pub_signal"
    let callPtrName := s!"__{successVar}_proof_call_ptr"
    let ptr := YulExpr.ident ptrName
    let packedCursor := YulExpr.ident packedCursorName
    let hashOut := YulExpr.ident hashOutName
    let callPtr := YulExpr.ident callPtrName
    let nullifierCopy := dynamicCopyData ctx packedCursor nullifierHashesOffset
      (YulExpr.call "mul" [nullifierHashesLength, YulExpr.lit 32])
    let newCommitmentsDest := YulExpr.call "add" [
      packedCursor,
      YulExpr.call "mul" [nullifierHashesLength, YulExpr.lit 32]
    ]
    let newCommitmentsCopy := dynamicCopyData ctx newCommitmentsDest newCommitmentsOffset
      (YulExpr.call "mul" [newCommitmentsLength, YulExpr.lit 32])
    let packedEnd := YulExpr.call "add" [
      newCommitmentsDest,
      YulExpr.call "mul" [newCommitmentsLength, YulExpr.lit 32]
    ]
    let proofWords := [pA0, pA1, pB00, pB01, pB10, pB11, pC0, pC1, YulExpr.ident pubSignalName]
    pure [
      YulStmt.let_ successVar (YulExpr.lit 0),
      YulStmt.let_ okVar (YulExpr.lit 0),
      YulStmt.block ([
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.expr (YulExpr.call "mstore" [ptr, merkleRoot]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptr, YulExpr.lit 32], contextHash]),
        YulStmt.let_ packedCursorName (YulExpr.call "add" [ptr, YulExpr.lit 64])
      ] ++ nullifierCopy ++ newCommitmentsCopy ++ [
        YulStmt.let_ hashOutName packedEnd,
        YulStmt.assign successVar (YulExpr.call "staticcall" [
          YulExpr.call "gas" [], YulExpr.lit 2, ptr,
          YulExpr.call "sub" [packedEnd, ptr], hashOut, YulExpr.lit 32
        ]),
        YulStmt.if_ (YulExpr.ident successVar) ([
          YulStmt.let_ pubSignalName (YulExpr.call "shr" [YulExpr.lit 3, YulExpr.call "mload" [hashOut]]),
          YulStmt.let_ callPtrName (YulExpr.call "add" [hashOut, YulExpr.lit 32]),
          YulStmt.expr (YulExpr.call "mstore" [callPtr, YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x43753b4d]])
        ] ++ (proofWords.zipIdx.map fun (value, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.call "add" [callPtr, YulExpr.lit (4 + 32 * idx)],
            value
          ])) ++ [
          YulStmt.assign successVar (YulExpr.call "staticcall" [
            YulExpr.call "gas" [], verifier, callPtr, YulExpr.lit 292, callPtr, YulExpr.lit 32
          ]),
          YulStmt.if_ (YulExpr.ident successVar) [
            YulStmt.assign okVar (YulExpr.call "mload" [callPtr])
          ],
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.lit freeMemoryPointer,
            YulExpr.call "and" [
              YulExpr.call "add" [
                YulExpr.call "add" [callPtr, YulExpr.lit 292],
                YulExpr.lit 31
              ],
              YulExpr.call "not" [YulExpr.lit 31]
            ]
          ])
        ])
      ])
    ]

end BoundaryCalls

open BoundaryCalls

/- ### Pool entry point: `UnlinkPool` -/

verity_contract UnlinkPool where
  storage
    -- Initializable (ERC-7201 namespaced at openzeppelin.storage.Initializable).
    storage_namespace erc7201 "openzeppelin.storage.Initializable"
    initializable_initialized : Uint256 := slot 0
    -- OwnableUpgradeable (ERC-7201 namespaced at openzeppelin.storage.Ownable).
    storage_namespace erc7201 "openzeppelin.storage.Ownable"
    ownable_owner : Address := slot 0
    -- Ownable2StepUpgradeable (ERC-7201 namespaced at openzeppelin.storage.Ownable2Step).
    storage_namespace erc7201 "openzeppelin.storage.Ownable2Step"
    ownable2Step_pendingOwner : Address := slot 0
    -- ReentrancyGuardTransient (transient storage modeled as a regular
    -- slot through the macro's `nonreentrant(slot)` function modifier).
    reentrancyLockSlot    : Uint256 := slot 3
    -- StateStorage (ERC-7201 namespaced at unlink.storage.State).
    storage_namespace erc7201 "unlink.storage.State"
    state : StorageStruct [
      merkleRoot : Uint256 @word 0,
      merkleTree : StorageStruct [
        maxIndex : Uint256 @word 0 packed(0,40),
        numberOfLeaves : Uint256 @word 0 packed(40,40),
        elements : Uint256 → Uint256 @word 1
      ] @word 1,
      rootSeen : Uint256 → Uint256 @word 3,
      nullifierHashes : Uint256 → Uint256 @word 4,
      verifierRouter : Address @word 5
    ] := slot 0
    -- RelayerStorage (ERC-7201 namespaced at unlink.storage.UnlinkPoolRelayers).
    storage_namespace erc7201 "unlink.storage.UnlinkPoolRelayers"
    relayersSlot          : Address → Uint256 := slot 0

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

  struct Circuit where
    verifier : Uint256,
    inputCount : Uint256,
    outputCount : Uint256,
    active : Uint256

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
    error StateNullifierAlreadySpent ()
    error StateNullifierOutOfField ()
    error ReentrancyGuardReentrantCall ()

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
    SNARK_SCALAR_FIELD : Uint256 :=
      0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
    MAX_LAZY_INDEX : Uint256 := 0xffffffff
    MAX_NOTE_VALUE : Uint256 :=
      1329227995784915872903807060280344575
    REENTRANCY_GUARD_STORAGE : Uint256 :=
      0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00
    Z_0  : Uint256 := 0
    Z_1  : Uint256 := 14744269619966411208579211824598458697587494354926760081771325075741142829156
    Z_2  : Uint256 := 7423237065226347324353380772367382631490014989348495481811164164159255474657
    Z_3  : Uint256 := 11286972368698509976183087595462810875513684078608517520839298933882497716792
    Z_4  : Uint256 := 3607627140608796879659380071776844901612302623152076817094415224584923813162
    Z_5  : Uint256 := 19712377064642672829441595136074946683621277828620209496774504837737984048981
    Z_6  : Uint256 := 20775607673010627194014556968476266066927294572720319469184847051418138353016
    Z_7  : Uint256 := 3396914609616007258851405644437304192397291162432396347162513310381425243293
    Z_8  : Uint256 := 21551820661461729022865262380882070649935529853313286572328683688269863701601
    Z_9  : Uint256 := 6573136701248752079028194407151022595060682063033565181951145966236778420039
    Z_10 : Uint256 := 12413880268183407374852357075976609371175688755676981206018884971008854919922
    Z_11 : Uint256 := 14271763308400718165336499097156975241954733520325982997864342600795471836726
    Z_12 : Uint256 := 20066985985293572387227381049700832219069292839614107140851619262827735677018
    Z_13 : Uint256 := 9394776414966240069580838672673694685292165040808226440647796406499139370960
    Z_14 : Uint256 := 11331146992410411304059858900317123658895005918277453009197229807340014528524
    Z_15 : Uint256 := 15819538789928229930262697811477882737253464456578333862691129291651619515538
    Z_16 : Uint256 := 19217088683336594659449020493828377907203207941212636669271704950158751593251
    Z_17 : Uint256 := 21035245323335827719745544373081896983162834604456827698288649288827293579666
    Z_18 : Uint256 := 6939770416153240137322503476966641397417391950902474480970945462551409848591
    Z_19 : Uint256 := 10941962436777715901943463195175331263348098796018438960955633645115732864202
    Z_20 : Uint256 := 15019797232609675441998260052101280400536945603062888308240081994073687793470
    Z_21 : Uint256 := 11702828337982203149177882813338547876343922920234831094975924378932809409969
    Z_22 : Uint256 := 11217067736778784455593535811108456786943573747466706329920902520905755780395
    Z_23 : Uint256 := 16072238744996205792852194127671441602062027943016727953216607508365787157389
    Z_24 : Uint256 := 17681057402012993898104192736393849603097507831571622013521167331642182653248
    Z_25 : Uint256 := 21694045479371014653083846597424257852691458318143380497809004364947786214945
    Z_26 : Uint256 := 8163447297445169709687354538480474434591144168767135863541048304198280615192
    Z_27 : Uint256 := 14081762237856300239452543304351251708585712948734528663957353575674639038357
    Z_28 : Uint256 := 16619959921569409661790279042024627172199214148318086837362003702249041851090
    Z_29 : Uint256 := 7022159125197495734384997711896547675021391130223237843255817587255104160365
    Z_30 : Uint256 := 4114686047564160449611603615418567457008101555090703535405891656262658644463
    Z_31 : Uint256 := 12549363297364877722388257367377629555213421373705596078299904496781819142130
    Z_32 : Uint256 := 21443572485391568159800782191812935835534334817699172242223315142338162256601

  -- `ISignatureTransfer public immutable PERMIT2` (UnlinkPool.sol:55).
  -- Bound at construction time to a constructor-supplied address.
  immutables
    PERMIT2 : Address := zeroAddress

  -- `VerifierRouter.getCircuit(circuitId)` returns
  -- `(verifier, inputCount, outputCount, active)`. The first argument is the
  -- stored router address that Solidity obtains through `_getVerifierRouter()`.
  linked_externals
    external poseidonT3(Uint256, Uint256) -> (Uint256)
    external poseidonT4(Uint256, Uint256, Uint256) -> (Uint256)

  /- `constructor(address _permit2)` (UnlinkPool.sol:147-160).

      Surfaces a mistyped Permit2 address at deploy time, calls
      `_disableInitializers()` so proxy bootstrap goes through
      `initialize` only, and stores PERMIT2 as a Verity `immutable`. -/
  constructor (permit2 : Address)
      local_obligations [permit2_code_existence := assumed "extcodesize Permit2 checks must match the Solidity code-existence boundary."] := do
    requireError (permit2 != zeroAddress) PoolAddressIsNull()
    let codeLen := extcodesize (addressToWord permit2)
    requireError (codeLen != 0) PoolAddressIsNull()
    -- PERMIT2 is exposed as an immutable; the macro emits the read-only
    -- binding automatically. `_disableInitializers` sets the marker.
    setStorage initializable_initialized 0xff

  /- Solidity's `onlyRelayer` modifier delegates to `_checkRelayer()`
      (UnlinkPool.sol:266-270). -/
  modifier onlyRelayer := do
    let sender ← msgSender
    let isR ← getMapping relayersSlot sender
    requireError (isR != 0) PoolUnauthorizedRelayer()

  /- `function initialize(address _verifierRouter, address _owner,
                           address _relayer) external initializer`
      (UnlinkPool.sol:166-184).

      `_checkBn254Precompile` (UnlinkPool.sol:577-583) wires directly to
      the BN254 precompile ECMs landed by verity#1827. The known-answer
      cross-validation `g1·3 (via 0x07) == g1 + (2·g1) (via 0x06)` is
      preserved exactly. -/
  function allow_post_interaction_writes «initialize» (verifierRouter : Address, ownerAddr : Address, relayer : Address)
      initializer(initializable_initialized) : Unit := do
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
    unsafe "_probePairing free memory pointer restore" do
      mstore 64 128
    requireError (pairB == 0) PoolPrecompileUnavailable()
    let twoG1x := 1368015179489954701390400359078579693043519447331113978918064868415326638035
    let twoG1y := 9918110051302171585080402603319702774565515993150576347155970296011118125764
    ecmBind [mul2x, mul2y]
      (Compiler.Modules.Precompiles.bn256ScalarMulModule "mul2x" "mul2y")
      [1, 2, 2]
    unsafe "_probeScalarMul free memory pointer restore" do
      mstore 64 128
    requireError (mul2x == twoG1x) PoolPrecompileUnavailable()
    requireError (mul2y == twoG1y) PoolPrecompileUnavailable()
    ecmBind [mul3x, mul3y]
      (Compiler.Modules.Precompiles.bn256ScalarMulModule "mul3x" "mul3y")
      [1, 2, 3]
    unsafe "_probeScalarMul free memory pointer restore" do
      mstore 64 128
    requireError ((mul3x != twoG1x) || (mul3y != twoG1y)) PoolPrecompileUnavailable()
    ecmBind [add2x, add2y]
      (Compiler.Modules.Precompiles.bn256AddModule "add2x" "add2y")
      [1, 2, 1, 2]
    unsafe "_probeAdd free memory pointer restore" do
      mstore 64 128
    requireError (add2x == twoG1x) PoolPrecompileUnavailable()
    requireError (add2y == twoG1y) PoolPrecompileUnavailable()
    ecmBind [add3x, add3y]
      (Compiler.Modules.Precompiles.bn256AddModule "add3x" "add3y")
      [1, 2, twoG1x, twoG1y]
    unsafe "_probeAdd free memory pointer restore" do
      mstore 64 128
    requireError ((add3x != twoG1x) || (add3y != twoG1y)) PoolPrecompileUnavailable()
    requireError (mul3x == add3x) PoolPrecompileUnavailable()
    requireError (mul3y == add3y) PoolPrecompileUnavailable()
    -- __Ownable_init(_owner); __Ownable2Step_init();
    setStorageAddr ownable_owner ownerAddr
    setStorageAddr ownable2Step_pendingOwner zeroAddress
    -- _initializeState: InternalLazyIMT._init($.data, 32), then cache/mark
    -- the depth-32 default zero root.
    setStorage state.merkleRoot Z_32
    setStorage state.merkleTree.maxIndex 0xffffffff
    setStorage state.merkleTree.numberOfLeaves 0
    setMappingWord state.rootSeen Z_32 0 1
    -- _setVerifierRouter
    requireError (verifierRouter != zeroAddress) PoolAddressIsNull()
    setStorageAddr state.verifierRouter verifierRouter
    -- _addRelayer
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let already ← getMapping relayersSlot relayer
    requireError (already == 0) PoolRelayerAlreadyActive()
    setMapping relayersSlot relayer 1
    emit "RelayerAdded" [addressToWord relayer]

  /- `function _authorizeUpgrade(address) internal override onlyOwner`
      (UnlinkPool.sol:188-190). Empty body; gating is by the modifier. -/
  function authorizeUpgrade (_newImplementation : Address)
      requires(ownable_owner) : Unit := do
    pure ()

  /- `function renounceOwnership() public view override onlyOwner`
      (UnlinkPool.sol:194-198). Owner cannot renounce. -/
  function renounceOwnership ()
      requires(ownable_owner) : Unit := do
    revertError PoolRenounceOwnershipDisabled()

  /- ### Public views -/

  function view owner () : Address := do
    let current ← getStorageAddr ownable_owner
    return current

  function view pendingOwner () : Address := do
    let pending ← getStorageAddr ownable2Step_pendingOwner
    return pending

  /- `function isRelayer(address _account) public view returns (bool)`
      (UnlinkPool.sol:206-208). -/
  function view isRelayer (account : Address) : Uint256 := do
    let r ← getMapping relayersSlot account
    return r

  /- `function nextLeafIndex() public view returns (uint256)`
      (State.sol:35-37). -/
  function view merkleRoot () : Uint256 := do
    let root ← getStorage state.merkleRoot
    return root

  function view nextLeafIndex () : Uint256 := do
    let n ← getStorage state.merkleTree.numberOfLeaves
    return n

  function view rootSeen (root : Uint256) : Bool := do
    let seen ← getMappingWord state.rootSeen root 0
    return (seen != 0)

  function view nullifierHashes (nullifierHash : Uint256) : Bool := do
    let spent ← getMappingWord state.nullifierHashes nullifierHash 0
    return (spent != 0)

  function view verifierRouter () : Address := do
    let router ← getStorageAddr state.verifierRouter
    return router

  function view MAX_TREE_DEPTH () : Uint256 := do
    return 32

  /- `function hashNote(Note calldata _note) public pure returns (uint256)`
      (UnlinkPool.sol:212-215). The Poseidon-T4 boundary is modeled as an
      external oracle call, so the compiler cannot classify this helper as
      `view` even though the Solidity source is pure. -/
  function hashNoteFields (npk : Uint256, _token : Address, amount : Uint256)
      : Uint256 := do
    return externalCall "poseidonT4" [npk, addressToWord _token, amount]

  function hashNote (_note : Note) : Uint256 := do
    return externalCall "poseidonT4"
      [_note.npk, addressToWord _note.token, _note.amount]

  function poseidon2 (lhs : Uint256, rhs : Uint256) : Uint256 := do
    return externalCall "poseidonT3" [lhs, rhs]

  function validateNoteFields (npk : Uint256, token : Address, amount : Uint256) : Unit := do
    requireError (token != zeroAddress) PoolInvalidNoteToken()
    requireError ((amount != 0) && (amount <= MAX_NOTE_VALUE))
      PoolInvalidNoteAmount()
    requireError ((npk != 0) && (npk < SNARK_SCALAR_FIELD))
      PoolInvalidNoteNPK()

  function sumNoteAmounts (notes : Array Note)
      local_obligations [abi_head_word_layout := assumed "abiHeadWord over Note[] elements must match the Solidity ABI head-word layout."]
      : Uint256 := do
    let mut totalAmount := 0
    forEach "i" (arrayLength notes) (do
      let amount := abiHeadWord (arrayElement notes i) 2
      totalAmount := add totalAmount amount)
    return totalAmount

  function allow_post_interaction_writes validateAndCollectDeposit
      (notes : Array Note, permitToken : Address)
      local_obligations [abi_head_word_layout := assumed "abiHeadWord over Note[] elements must match the Solidity ABI head-word layout."]
      : Array Uint256 := do
    let notesLen := arrayLength notes
    let newLeaves ← allocArray notesLen
    forEach "i" notesLen (do
      let npk := abiHeadWord (arrayElement notes i) 0
      let token := wordToAddress (abiHeadWord (arrayElement notes i) 1)
      let amount := abiHeadWord (arrayElement notes i) 2
      validateNoteFields npk token amount
      requireError (token == permitToken) PoolTokenMismatch()
      let leaf ← hashNoteFields npk token amount
      setMemoryArrayElement newLeaves i leaf)
    returnArray newLeaves

  /- ### Owner functions -/

  /- `function addRelayer(address _relayer) external onlyOwner`
      (UnlinkPool.sol:225-230). -/
  function addRelayer (relayer : Address)
      requires(ownable_owner) : Unit := do
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let already ← getMapping relayersSlot relayer
    requireError (already == 0) PoolRelayerAlreadyActive()
    setMapping relayersSlot relayer 1
    emit "RelayerAdded" [addressToWord relayer]

  /- `function removeRelayer(address _relayer) external onlyOwner`
      (UnlinkPool.sol:234-239). -/
  function removeRelayer (relayer : Address)
      requires(ownable_owner) : Unit := do
    requireError (relayer != zeroAddress) PoolAddressIsNull()
    let active ← getMapping relayersSlot relayer
    requireError (active != 0) PoolUnauthorizedRelayer()
    setMapping relayersSlot relayer 0
    emit "RelayerRemoved" [addressToWord relayer]

  /- `function setVerifierRouter(address _verifierRouter) external onlyOwner`
      (UnlinkPool.sol:244-253). -/
  function setVerifierRouter (verifierRouter : Address)
      requires(ownable_owner) : Unit := do
    let previousRouter ← getStorageAddr state.verifierRouter
    if previousRouter == verifierRouter then
      pure ()
    else
      requireError (verifierRouter != zeroAddress) PoolAddressIsNull()
      setStorageAddr state.verifierRouter verifierRouter
      emit "VerifierRouterUpdated"
        [addressToWord previousRouter, addressToWord verifierRouter]

  /- ### Ownable2Step transfer glue -/

  function transferOwnership (newOwner : Address)
      requires(ownable_owner) : Unit := do
    setStorageAddr ownable2Step_pendingOwner newOwner

  function acceptOwnership () : Unit := do
    let sender ← msgSender
    let pending ← getStorageAddr ownable2Step_pendingOwner
    requireError (sender == pending) CallerNotPendingOwner()
    setStorageAddr ownable_owner pending
    setStorageAddr ownable2Step_pendingOwner zeroAddress

  function countNonZero (values : Array Uint256, excludeIndex : Uint256)
      local_obligations [memory_array_layout := assumed "Memory-array element loads must match the Solidity ABI/runtime array layout."]
      : Uint256 := do
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

  function spendNullifiers (nullifierHashes : Array Uint256)
      local_obligations [memory_array_layout := assumed "Memory-array element loads must match the Solidity ABI/runtime array layout."]
      : Unit := do
    forEach "k" (arrayLength nullifierHashes) (do
      let nullifierHash := arrayElement nullifierHashes k
      if nullifierHash != 0 then
        requireError (nullifierHash < SNARK_SCALAR_FIELD)
          StateNullifierOutOfField()
        let spent ← getMappingWord state.nullifierHashes nullifierHash 0
        requireError (spent == 0) StateNullifierAlreadySpent()
        setMappingWord state.nullifierHashes nullifierHash 0 1
      else
        pure ())

  function realCommitments
      (newCommitments : Array Uint256, excludeIndex : Uint256)
      local_obligations [memory_array_layout := assumed "Memory-array element loads and writes must match the Solidity ABI/runtime array layout."]
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

  function realNullifiers (nullifierHashes : Array Uint256)
      local_obligations [memory_array_layout := assumed "Memory-array element loads and writes must match the Solidity ABI/runtime array layout."]
      : Array Uint256 := do
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

  function lazyDefaultZero (index : Uint256) : Uint256 := do
    let mut zero := Z_0
    if index == 1 then zero := Z_1 else pure ()
    if index == 2 then zero := Z_2 else pure ()
    if index == 3 then zero := Z_3 else pure ()
    if index == 4 then zero := Z_4 else pure ()
    if index == 5 then zero := Z_5 else pure ()
    if index == 6 then zero := Z_6 else pure ()
    if index == 7 then zero := Z_7 else pure ()
    if index == 8 then zero := Z_8 else pure ()
    if index == 9 then zero := Z_9 else pure ()
    if index == 10 then zero := Z_10 else pure ()
    if index == 11 then zero := Z_11 else pure ()
    if index == 12 then zero := Z_12 else pure ()
    if index == 13 then zero := Z_13 else pure ()
    if index == 14 then zero := Z_14 else pure ()
    if index == 15 then zero := Z_15 else pure ()
    if index == 16 then zero := Z_16 else pure ()
    if index == 17 then zero := Z_17 else pure ()
    if index == 18 then zero := Z_18 else pure ()
    if index == 19 then zero := Z_19 else pure ()
    if index == 20 then zero := Z_20 else pure ()
    if index == 21 then zero := Z_21 else pure ()
    if index == 22 then zero := Z_22 else pure ()
    if index == 23 then zero := Z_23 else pure ()
    if index == 24 then zero := Z_24 else pure ()
    if index == 25 then zero := Z_25 else pure ()
    if index == 26 then zero := Z_26 else pure ()
    if index == 27 then zero := Z_27 else pure ()
    if index == 28 then zero := Z_28 else pure ()
    if index == 29 then zero := Z_29 else pure ()
    if index == 30 then zero := Z_30 else pure ()
    if index == 31 then zero := Z_31 else pure ()
    if index == 32 then zero := Z_32 else pure ()
    return zero

  function lazyIndexForElement (level : Uint256, index : Uint256) : Uint256 := do
    return (add (mul MAX_LAZY_INDEX level) index)

  function allow_post_interaction_writes lazyInsert (leaf : Uint256) : Unit := do
    let startIndex ← getStorage state.merkleTree.numberOfLeaves
    let maxIndex ← getStorage state.merkleTree.maxIndex
    requireError (leaf < SNARK_SCALAR_FIELD) PoolInvalidOutputShape()
    requireError (startIndex < maxIndex) PoolInvalidOutputShape()
    setStorage state.merkleTree.numberOfLeaves (add startIndex 1)
    let mut index := startIndex
    let mut hash := leaf
    let mut active := 1
    forEach "level" 32 (do
      if active != 0 then
        let elementKey ← lazyIndexForElement level index
        setMappingWord state.merkleTree.elements elementKey 0 hash
        if bitAnd index 1 == 0 then
          active := 0
        else
          let siblingKey ← lazyIndexForElement level (sub index 1)
          let sibling ← getMappingWord state.merkleTree.elements siblingKey 0
          let parent ← poseidon2 sibling hash
          hash := parent
          index := shr 1 index
      else
        pure ())

  function lazyRootWithDepth32 ()
      local_obligations [memory_array_layout := assumed "Memory-array element loads and writes must match the Solidity ABI/runtime array layout."]
      : Uint256 := do
    let numberOfLeaves ← getStorage state.merkleTree.numberOfLeaves
    if numberOfLeaves == 0 then
      return Z_32
    else
      let levels ← allocArray 33
      let mut index := sub numberOfLeaves 1
      if bitAnd index 1 == 0 then
        let elementKey ← lazyIndexForElement 0 index
        let element ← getMappingWord state.merkleTree.elements elementKey 0
        setMemoryArrayElement levels 0 element
      else
        setMemoryArrayElement levels 0 Z_0
      forEach "level" 32 (do
        let current := arrayElement levels level
        if bitAnd index 1 == 0 then
          let z ← lazyDefaultZero level
          let parent ← poseidon2 current z
          setMemoryArrayElement levels (add level 1) parent
        else
          let levelCount := shr (add level 1) numberOfLeaves
          let parentIndex := shr 1 index
          if levelCount > parentIndex then
            let parentKey ← lazyIndexForElement (add level 1) parentIndex
            let parent ← getMappingWord state.merkleTree.elements parentKey 0
            setMemoryArrayElement levels (add level 1) parent
          else
            let siblingKey ← lazyIndexForElement level (sub index 1)
            let sibling ← getMappingWord state.merkleTree.elements siblingKey 0
            let parent ← poseidon2 sibling current
            setMemoryArrayElement levels (add level 1) parent
        index := shr 1 index)
      return (arrayElement levels 32)

  /- Source shape: `_insertLeaves(uint256[] memory _leafHashes)`.
     Appends each leaf through the nested LazyIMT spine and recomputes the
     depth-32 root, matching `InternalLazyIMT._insert` / `_root(self, 32)`. -/
  function allow_post_interaction_writes insertLeaves (leafHashes : Array Uint256)
      local_obligations [memory_array_layout := assumed "Memory-array element loads must match the Solidity ABI/runtime array layout."]
      : Uint256 := do
    let count := arrayLength leafHashes
    if count == 0 then
      let currentRoot ← getStorage state.merkleRoot
      return currentRoot
    else
      forEach "m" count (do
        let leaf := arrayElement leafHashes m
        lazyInsert leaf)
      let newRoot ← lazyRootWithDepth32
      setStorage state.merkleRoot newRoot
      setMappingWord state.rootSeen newRoot 0 1
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
    return (mod rawContext SNARK_SCALAR_FIELD)

  function view validateContext
      (merkleRoot : Uint256, contextHash : Uint256, expectedContext : Uint256)
      : Unit := do
    requireError (contextHash == expectedContext) PoolInvalidContextHash()
    let rootSeen ← getMappingWord state.rootSeen merkleRoot 0
    requireError (rootSeen != 0) PoolInvalidMerkleRoot()

  function allow_post_interaction_writes settleWithdrawalTransfer
      (token : Address, recipient : Address, amount : Uint256) : Unit := do
    let selfAddr ← Verity.contractAddress
    let poolBefore ← balanceOf token selfAddr
    let recipientBefore ← balanceOf token recipient
    safeTransfer token recipient amount
    let poolAfter ← balanceOf token selfAddr
    let recipientAfter ← balanceOf token recipient
    requireError (poolAfter <= poolBefore) PoolWithdrawBalanceMismatch()
    requireError ((sub poolBefore poolAfter) == amount) PoolWithdrawBalanceMismatch()
    requireError (recipientAfter >= recipientBefore) PoolWithdrawBalanceMismatch()
    requireError ((sub recipientAfter recipientBefore) == amount) PoolWithdrawBalanceMismatch()

  function allow_post_interaction_writes transferWithBalanceCheck
      (permit : PermitTransferFrom, depositor : Address, signature : Bytes,
       totalAmount : Uint256, witness : Bytes32) : Unit := do
    let selfAddr ← Verity.contractAddress
    let token := permit.permitted.token
    let balBefore ← balanceOf token selfAddr
    let permitAccepted ← ecmCall
      (fun resultVar => permitWitnessTransferFromModule resultVar)
      [addressToWord PERMIT2,
       addressToWord token,
       permit.permitted.amount,
       permit.nonce,
       permit.deadline,
       addressToWord selfAddr,
       totalAmount,
       addressToWord depositor,
       witness,
       abiHeadWord signature 0,
       0]
    requireError (permitAccepted != 0) PoolDepositBalanceMismatch()
    let balAfter ← balanceOf token selfAddr
    requireError (balAfter >= balBefore) PoolDepositBalanceMismatch()
    requireError ((sub balAfter balBefore) == totalAmount)
      PoolDepositBalanceMismatch()

  /- `function deposit(address _depositor, Note[] calldata _notes,
      Ciphertext[] calldata _ciphertexts, PermitTransferFrom calldata _permit,
      bytes calldata _signature) external onlyRelayer nonReentrant`
      (UnlinkPool.sol:306-324). -/
  function allow_post_interaction_writes deposit
      (depositor : Address, notes : Array Note, ciphertexts : Array Ciphertext,
       permit : PermitTransferFrom, signature : Bytes)
      local_obligations [
        abi_head_word_layout := assumed "abiHeadWord over Note[] elements must match the Solidity ABI head-word layout.",
        transient_reentrancy_guard := assumed "Transient reentrancy guard tload/tstore must refine OpenZeppelin ReentrancyGuardTransient behavior."
      ]
      : Unit := do
    let sender ← msgSender
    let isRelayer ← getMapping relayersSlot sender
    requireError (isRelayer != 0) PoolUnauthorizedRelayer()
    let guard := tload REENTRANCY_GUARD_STORAGE
    requireError (guard == 0) ReentrancyGuardReentrantCall()
    tstore REENTRANCY_GUARD_STORAGE 1
    let notesLen := arrayLength notes
    requireError (notesLen != 0) PoolEmptyNotes()
    requireError ((arrayLength ciphertexts) == notesLen)
      PoolCiphertextCountMismatch()
    let newLeaves ← allocArray notesLen
    forEach "noteIndex" notesLen (do
      let npk := abiHeadWord (arrayElement notes noteIndex) 0
      let token := wordToAddress (abiHeadWord (arrayElement notes noteIndex) 1)
      let amount := abiHeadWord (arrayElement notes noteIndex) 2
      validateNoteFields npk token amount
      requireError (token == permit.permitted.token) PoolTokenMismatch()
      let leaf ← hashNoteFields npk token amount
      setMemoryArrayElement newLeaves noteIndex leaf)
    let totalAmount ← sumNoteAmounts notes
    let selfAddr ← Verity.contractAddress
    let notesHash ← ecmCall
      (fun resultVar =>
        abiEncodeTwoStaticArraysModule resultVar "notes" "ciphertexts" 3 4)
      [notesLen, arrayLength ciphertexts]
    let witness ← ecmCall
      (fun resultVar => abiEncodePackedWordsModule resultVar 3)
      [DEPOSIT_WITNESS_TYPEHASH, addressToWord selfAddr, notesHash]
    transferWithBalanceCheck permit depositor signature totalAmount witness
    let startIndex ← nextLeafIndex
    let newRoot ← insertLeaves newLeaves
    emit "Deposited"
      [addressToWord depositor, newRoot, startIndex, notes, ciphertexts]
    tstore REENTRANCY_GUARD_STORAGE 0

  /- `function transfer(Transaction[] calldata _transactions) external
      onlyRelayer nonReentrant` (UnlinkPool.sol:328-363). -/
  function allow_post_interaction_writes transfer (transactions : Array Transaction)
      local_obligations [
        memory_array_layout := assumed "Memory-array element loads and writes must match the Solidity ABI/runtime array layout.",
        transient_reentrancy_guard := assumed "Transient reentrancy guard tload/tstore must refine OpenZeppelin ReentrancyGuardTransient behavior."
      ]
      : Unit := do
    let sender ← msgSender
    let isRelayer ← getMapping relayersSlot sender
    requireError (isRelayer != 0) PoolUnauthorizedRelayer()
    let guard := tload REENTRANCY_GUARD_STORAGE
    requireError (guard == 0) ReentrancyGuardReentrantCall()
    tstore REENTRANCY_GUARD_STORAGE 1
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      let txn := arrayElement transactions i
      let verifierRouter ← getStorageAddr state.verifierRouter
      ecmBind [success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active]
        (getCircuitTryModule "success" "circuit_verifier" "circuit_inputCount" "circuit_outputCount" "circuit_active")
        [addressToWord verifierRouter, txn.circuitId]
      requireError (success != 0) PoolCircuitNotRegistered()
      requireError (circuit_verifier != 0) PoolCircuitNotRegistered()
      requireError (circuit_active != 0) PoolCircuitInactive()
      requireError ((arrayLength txn.nullifierHashes) == circuit_inputCount)
        PoolInvalidInputShape()
      requireError ((arrayLength txn.newCommitments) == circuit_outputCount)
        PoolInvalidOutputShape()
      forEach "commitBoundsIndex" (arrayLength txn.newCommitments) (do
        let commitment := arrayElement txn.newCommitments commitBoundsIndex
        if commitment != 0 then
          require (commitment < SNARK_SCALAR_FIELD)
            "LazyIMT: leaf must be < SNARK_SCALAR_FIELD"
        else
          pure ())
      let ciphertextCount ← countNonZero txn.newCommitments
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      requireError ((arrayLength txn.ciphertexts) == ciphertextCount)
        PoolCiphertextCountMismatch()
      let computedContext ← computeContextHash txn.ciphertexts
      validateContext txn.merkleRoot txn.contextHash computedContext
      ecmBind [proofOk, ok]
        (verifySpendTryModule "proofOk" "ok")
        [circuit_verifier,
         abiEncode txn.proof,
         txn.merkleRoot,
         txn.contextHash,
         abiHeadWord txn 3,
         arrayLength txn.nullifierHashes,
         abiHeadWord txn 4,
         arrayLength txn.newCommitments]
      requireError (proofOk != 0) PoolProofVerificationFailed()
      requireError (ok != 0) PoolProofVerificationFailed()
      spendNullifiers txn.nullifierHashes
      let mut leavesCount := 0
      forEach "commitCountIndex" (arrayLength txn.newCommitments) (do
        let commitment := arrayElement txn.newCommitments commitCountIndex
        if commitment != 0 then
          leavesCount := add leavesCount 1
        else
          pure ())
      let leaves ← allocArray leavesCount
      let mut leafWriteIndex := 0
      forEach "commitWriteIndex" (arrayLength txn.newCommitments) (do
        let commitment := arrayElement txn.newCommitments commitWriteIndex
        if commitment != 0 then
          setMemoryArrayElement leaves leafWriteIndex commitment
          leafWriteIndex := add leafWriteIndex 1
        else
          pure ())
      let mut nullifierCount := 0
      forEach "nullifierCountIndex" (arrayLength txn.nullifierHashes) (do
        let nullifierHash := arrayElement txn.nullifierHashes nullifierCountIndex
        if nullifierHash != 0 then
          nullifierCount := add nullifierCount 1
        else
          pure ())
      let realNulls ← allocArray nullifierCount
      let mut nullifierWriteIndex := 0
      forEach "nullifierWriteIndexLoop" (arrayLength txn.nullifierHashes) (do
        let nullifierHash := arrayElement txn.nullifierHashes nullifierWriteIndexLoop
        if nullifierHash != 0 then
          setMemoryArrayElement realNulls nullifierWriteIndex nullifierHash
          nullifierWriteIndex := add nullifierWriteIndex 1
        else
          pure ())
      let startIndex ← nextLeafIndex
      let newRoot ← insertLeaves leaves
      emit "Transferred"
        [newRoot, startIndex, leaves, realNulls, txn.ciphertexts])
    tstore REENTRANCY_GUARD_STORAGE 0

  /- `_executeWithdrawal(WithdrawalTransaction calldata _txn, bool _emergency)`
      (UnlinkPool.sol:614-666). -/
  function allow_post_interaction_writes executeWithdrawal
      (txn : WithdrawalTransaction, emergency : Bool)
      local_obligations [memory_array_layout := assumed "Memory-array element loads and writes must match the Solidity ABI/runtime array layout."]
      : Unit := do
    requireError (txn.withdrawal.amount != 0)
      PoolInvalidNoteAmount()
    requireError (txn.withdrawal.npk != 0)
      PoolInvalidNoteNPK()
    requireError (txn.withdrawal.token != zeroAddress)
      PoolInvalidNoteToken()
    requireError (txn.withdrawal.npk <= 0xffffffffffffffffffffffffffffffffffffffff)
      PoolInvalidWithdrawalRecipient()
    let recipient := wordToAddress txn.withdrawal.npk
    let selfAddr ← Verity.contractAddress
    requireError (recipient != selfAddr) PoolInvalidWithdrawalRecipient()
    let verifierRouter ← getStorageAddr state.verifierRouter
    ecmBind [success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active]
      (getCircuitTryModule "success" "circuit_verifier" "circuit_inputCount" "circuit_outputCount" "circuit_active")
      [addressToWord verifierRouter, txn.circuitId]
    requireError (success != 0) PoolCircuitNotRegistered()
    requireError (circuit_verifier != 0) PoolCircuitNotRegistered()
    requireError (circuit_active != 0) PoolCircuitInactive()
    requireError ((arrayLength txn.nullifierHashes) == circuit_inputCount)
      PoolInvalidInputShape()
    requireError ((arrayLength txn.newCommitments) == circuit_outputCount)
      PoolInvalidOutputShape()
    let wSlot := sub circuit_outputCount 1
    let withdrawalCommitment := arrayElement txn.newCommitments wSlot
    requireError (withdrawalCommitment != 0) PoolWithdrawalSlotZero()
    let noteHash ← hashNoteFields txn.withdrawal.npk txn.withdrawal.token txn.withdrawal.amount
    requireError (withdrawalCommitment == noteHash) PoolInvalidWithdrawalCommitment()
    forEach "withdrawCommitBoundsIndex" (arrayLength txn.newCommitments) (do
      let commitment := arrayElement txn.newCommitments withdrawCommitBoundsIndex
      if withdrawCommitBoundsIndex != wSlot then
        if commitment != 0 then
          require (commitment < SNARK_SCALAR_FIELD)
            "LazyIMT: leaf must be < SNARK_SCALAR_FIELD"
        else
          pure ()
      else
        pure ())
    let ciphertextCount ← countNonZero txn.newCommitments wSlot
    requireError ((arrayLength txn.ciphertexts) == ciphertextCount)
      PoolCiphertextCountMismatch()
    let computedContext ← computeContextHash txn.ciphertexts
    validateContext txn.merkleRoot txn.contextHash computedContext
    ecmBind [proofOk, ok]
      (verifySpendTryModule "proofOk" "ok")
      [circuit_verifier,
       abiEncode txn.proof,
       txn.merkleRoot,
       txn.contextHash,
       abiHeadWord txn 3,
       arrayLength txn.nullifierHashes,
       abiHeadWord txn 4,
       arrayLength txn.newCommitments]
    requireError (proofOk != 0) PoolProofVerificationFailed()
    requireError (ok != 0) PoolProofVerificationFailed()
    spendNullifiers txn.nullifierHashes
    let mut leavesCount := 0
    forEach "withdrawCommitCountIndex" (arrayLength txn.newCommitments) (do
      let commitment := arrayElement txn.newCommitments withdrawCommitCountIndex
      if withdrawCommitCountIndex != wSlot then
        if commitment != 0 then
          leavesCount := add leavesCount 1
        else
          pure ()
      else
        pure ())
    let leaves ← allocArray leavesCount
    let mut leafWriteIndex := 0
    forEach "withdrawCommitWriteIndex" (arrayLength txn.newCommitments) (do
      let commitment := arrayElement txn.newCommitments withdrawCommitWriteIndex
      if withdrawCommitWriteIndex != wSlot then
        if commitment != 0 then
          setMemoryArrayElement leaves leafWriteIndex commitment
          leafWriteIndex := add leafWriteIndex 1
        else
          pure ()
      else
        pure ())
    let mut nullifierCount := 0
    forEach "withdrawNullifierCountIndex" (arrayLength txn.nullifierHashes) (do
      let nullifierHash := arrayElement txn.nullifierHashes withdrawNullifierCountIndex
      if nullifierHash != 0 then
        nullifierCount := add nullifierCount 1
      else
        pure ())
    let realNulls ← allocArray nullifierCount
    let mut nullifierWriteIndex := 0
    forEach "withdrawNullifierWriteIndexLoop" (arrayLength txn.nullifierHashes) (do
      let nullifierHash := arrayElement txn.nullifierHashes withdrawNullifierWriteIndexLoop
      if nullifierHash != 0 then
        setMemoryArrayElement realNulls nullifierWriteIndex nullifierHash
        nullifierWriteIndex := add nullifierWriteIndex 1
      else
        pure ())
    let startIndex ← nextLeafIndex
    let newRoot ← insertLeaves leaves
    settleWithdrawalTransfer txn.withdrawal.token recipient txn.withdrawal.amount
    if emergency then
      emit "EmergencyWithdrawn"
        [addressToWord recipient, txn.withdrawal, newRoot, startIndex, leaves,
         realNulls, txn.ciphertexts]
    else
      emit "Withdrawn"
        [addressToWord recipient, txn.withdrawal, newRoot, startIndex, leaves,
         realNulls, txn.ciphertexts]

  /- `function withdraw(WithdrawalTransaction[] calldata _transactions)
      external onlyRelayer nonReentrant` (UnlinkPool.sol:365-372). -/
  function allow_post_interaction_writes withdraw (transactions : Array WithdrawalTransaction)
      local_obligations [
        transient_reentrancy_guard := assumed "Transient reentrancy guard tload/tstore must refine OpenZeppelin ReentrancyGuardTransient behavior."
      ]
      : Unit := do
    let sender ← msgSender
    let isRelayer ← getMapping relayersSlot sender
    requireError (isRelayer != 0) PoolUnauthorizedRelayer()
    let guard := tload REENTRANCY_GUARD_STORAGE
    requireError (guard == 0) ReentrancyGuardReentrantCall()
    tstore REENTRANCY_GUARD_STORAGE 1
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      executeWithdrawal (arrayElement transactions i) false)
    tstore REENTRANCY_GUARD_STORAGE 0

  /- `function emergencyWithdraw(WithdrawalTransaction[] calldata _transactions)
      external nonReentrant` (UnlinkPool.sol:376-383). -/
  function allow_post_interaction_writes emergencyWithdraw
      (transactions : Array WithdrawalTransaction)
      local_obligations [
        transient_reentrancy_guard := assumed "Transient reentrancy guard tload/tstore must refine OpenZeppelin ReentrancyGuardTransient behavior."
      ]
      : Unit := do
    let guard := tload REENTRANCY_GUARD_STORAGE
    requireError (guard == 0) ReentrancyGuardReentrantCall()
    tstore REENTRANCY_GUARD_STORAGE 1
    let txLen := arrayLength transactions
    requireError (txLen != 0) PoolEmptyTransactions()
    forEach "i" txLen (do
      executeWithdrawal (arrayElement transactions i) true)
    tstore REENTRANCY_GUARD_STORAGE 0

namespace ownable

/-- Alias for the generated storage field label corresponding to OZ's
    `OwnableStorage._owner` member. -/
def owner : StorageSlot Address := UnlinkPool.ownable_owner

end ownable

namespace ownable2Step

/-- Alias for the generated storage field label corresponding to OZ's
    `Ownable2StepStorage._pendingOwner` member. -/
def pendingOwner : StorageSlot Address := UnlinkPool.ownable2Step_pendingOwner

end ownable2Step

/- Guard the ERC-7201 namespace roots used by the model against the
   manifest literals derived from the Solidity/OZ namespace strings. -/
#guard UnlinkPool.initializable_initialized.slot = INITIALIZABLE_STORAGE_LOCATION_LIT.val
#guard ownable.owner.slot = OWNABLE_STORAGE_LOCATION_LIT.val
#guard ownable2Step.pendingOwner.slot = OWNABLE2STEP_STORAGE_LOCATION_LIT.val
#guard UnlinkPool.state.merkleRoot.slot = STATE_STORAGE_LOCATION_LIT.val
#guard UnlinkPool.relayersSlot.slot = RELAYER_STORAGE_LOCATION_LIT.val

end Benchmark.Cases.UnlinkXyz.Pool
