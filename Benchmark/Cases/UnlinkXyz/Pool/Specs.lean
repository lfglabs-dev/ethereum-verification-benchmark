/-
  Verity model of `UnlinkPool` — assumed boundaries and pure structural specs.

  Upstream: unlink-xyz/monorepo@4bc46c1fffbc0e146dccfff5b9fe00167121b27b
  Solidity files:
    - protocol/contracts/src/lib/Models.sol            (struct shapes)
    - protocol/contracts/src/lib/Poseidon.sol          (PoseidonT3 / PoseidonT4)
    - protocol/contracts/src/lib/InternalLazyIMT.sol   (append-only IMT)
    - protocol/contracts/src/VerifierRouter.sol        (Groth16 verifier registry)

  Protocol-specific cryptographic primitives belong in the `unlink-verity`
  package per the package-split policy documented in
  `lfglabs-dev/verity:docs/ROADMAP.md` "Unlink Audit Readiness". This file
  declares them locally as `opaque` / `axiom` boundaries with the
  `unlink_verity_*` axiom naming convention so a future trust manifest can
  list them in one place.

  BN254 precompile probes are NO LONGER declared here: `_checkBn254Precompile`
  is wired directly to `Compiler.Modules.Precompiles.bn256Add` /
  `bn256ScalarMul` / `bn256Pairing` (verity#1827, shipped).

  The `DEPOSIT_WITNESS_TYPEHASH` and `RELAYER_STORAGE_LOCATION` constants
  are NO LONGER declared here either: they live inside the `verity_contract`
  `constants` block in `Contract.lean`, derived through `keccak256_lit`.
-/
import Verity

namespace Benchmark.Cases.UnlinkXyz.Pool

open Verity hiding pure bind
open Verity.EVM.Uint256

/-! ### Numeric constants (mirror `library Constants` in Models.sol) -/

namespace PoolConstants
  /-- BN254 scalar field order (Fr modulus). Identical to the Rust and SDK
      copies; drift is enforced by `just check-constants` upstream. -/
  def SNARK_SCALAR_FIELD : Uint256 :=
    21888242871839275222246405745257275088548364400416034343698204186575808495617

  /-- Output note values are circuit-bounded to 120 bits. -/
  def MAX_NOTE_VALUE : Uint256 :=
    Verity.Core.Uint256.sub (Verity.Core.Uint256.shl 120 1) 1

  /-- Canonical circuit identifier for the single PR-B variant.
      Equals `keccak256("unlink.circuit.spend_10x4_v1")`. -/
  def CIRCUIT_SPEND_10X4_V1 : Uint256 :=
    0x2cb863b71d9ceea7b2f7bbfafe12dc3c8758d42ec2005fce3e00914779e5bd21
end PoolConstants

/-! ### Solidity struct mirrors

`Proof` carries the Groth16 components as Lean product types
(`Uint256 × Uint256` etc.) rather than the macro-level `fixedArray Uint256 N`,
because the macro grammar at the lakefile-pinned Verity revision does not
yet surface `fixedArray` as a parameter type — only the
`CompilationModel.ParamType.fixedArray` IR constructor exists. Product
types are observably equivalent for n=2 / n=2x2. -/

structure Proof where
  pA : Uint256 × Uint256
  pB : (Uint256 × Uint256) × (Uint256 × Uint256)
  pC : Uint256 × Uint256
  deriving Inhabited

structure Note where
  npk    : Uint256
  token  : Address
  amount : Uint256
  deriving Inhabited

structure Ciphertext where
  ephemeralKey : Uint256
  data         : Uint256 × Uint256 × Uint256
  deriving Inhabited

structure Transaction where
  proof            : Proof
  circuitId        : Uint256
  merkleRoot       : Uint256
  nullifierHashes  : Array Uint256
  newCommitments   : Array Uint256
  contextHash      : Uint256
  ciphertexts      : Array Ciphertext
  deriving Inhabited

structure WithdrawalTransaction where
  proof            : Proof
  circuitId        : Uint256
  merkleRoot       : Uint256
  nullifierHashes  : Array Uint256
  newCommitments   : Array Uint256
  contextHash      : Uint256
  withdrawal       : Note
  ciphertexts      : Array Ciphertext
  deriving Inhabited

structure Call where
  target : Address
  value  : Uint256
  data   : Array UInt8
  deriving Inhabited

structure AdapterTransaction where
  proof            : Proof
  circuitId        : Uint256
  merkleRoot       : Uint256
  nullifierHashes  : Array Uint256
  newCommitments   : Array Uint256
  contextHash      : Uint256
  withdrawal       : Note
  calls            : Array Call
  ciphertexts      : Array Ciphertext
  deriving Inhabited

/-! ### Assumed boundary: Poseidon T3 / T4 (vendored poseidon-solidity@v0.0.5)

`PoseidonT3.hash(uint[2])` and `PoseidonT4.hash(uint[3])` are the BN254
scalar-field hashes used inside the ZK circuit. Modeled opaquely; result
lives in the scalar field. -/

namespace PoseidonT3
  opaque hash : (Uint256 × Uint256) → Uint256
  /-- Axiom name: `unlink_verity_poseidon_t3_in_field`. -/
  axiom hash_in_field (xy : Uint256 × Uint256) :
    (hash xy : Nat) < (PoolConstants.SNARK_SCALAR_FIELD : Nat)
end PoseidonT3

namespace PoseidonT4
  opaque hash : (Uint256 × Uint256 × Uint256) → Uint256
  /-- Axiom name: `unlink_verity_poseidon_t4_in_field`. -/
  axiom hash_in_field (xyz : Uint256 × Uint256 × Uint256) :
    (hash xyz : Nat) < (PoolConstants.SNARK_SCALAR_FIELD : Nat)
end PoseidonT4

/-! ### Assumed boundary: Permit2.permitWitnessTransferFrom

Modeled as an opaque effect on the pool's token balance. The signature /
witness checks happen inside Permit2; the pool observes only the post-call
balance delta (`_transferWithBalanceCheck`). -/

namespace Permit2Spec
  /-- Axiom name: `unlink_verity_permit2_permit_witness_transfer_from`. -/
  opaque permitWitnessTransferFromEffect
    (permit2 : Address) (token : Address) (depositor : Address)
    (totalAmount : Uint256) (witness : Uint256) : Uint256
end Permit2Spec

/-! ### Assumed boundary: Lazy-IMT append-only state

`InternalLazyIMT._insert` updates the lazy Merkle-tree state. Modeled as
an opaque step function so callers can write the leaf and re-read the
root through the pool's storage fields. -/

namespace LazyImtSpec
  /-- Axiom name: `unlink_verity_lazy_imt_root_after_inserts`. -/
  opaque rootAfterInserts (prevRoot prevNumberOfLeaves : Uint256)
    (leaves : Array Uint256) : Uint256
end LazyImtSpec

/-! ### Assumed boundary: Groth16 verifier dispatch

`VerifierRouter.getCircuit(circuitId)` returns
`(verifier, inputCount, outputCount, active)`. The verifier contract's
`verifyProof` is called with the proof and the SHA-256-derived public
signal. Both calls are modeled as opaque pure Lean specs here, but at
the contract layer `getCircuit` is exposed as a single tuple-returning
`linked_externals` declaration (see `Contract.lean`) and the dispatch
itself runs through Verity's external-call machinery. -/

namespace VerifierRouterSpec
  /-- Axiom name: `unlink_verity_groth16_verify_proof`. -/
  opaque verifyProof
    (verifier : Address)
    (pA : Uint256 × Uint256)
    (pB : (Uint256 × Uint256) × (Uint256 × Uint256))
    (pC : Uint256 × Uint256)
    (publicSignal : Uint256) : Bool
end VerifierRouterSpec

/-! ### Assumed boundary: ABI keccak / sha256 composites

The pool builds two composite keccak hashes (the deposit witness and the
ciphertexts-context hash) and one composite sha256 (the public-signals
hash). The composition itself is byte-faithful Solidity; Verity expresses
each as a pure boundary so the trust report records exactly three named
opaque hashes rather than threading raw `abi.encode` byte layout. -/

namespace AbiSpec
  /-- `keccak256(abi.encode(DEPOSIT_WITNESS_TYPEHASH, address(this),
                            keccak256(abi.encode(notes, ciphertexts))))` -/
  opaque depositWitnessHash
    (typehash : Uint256) (poolAddress : Address)
    (notes : Array Note) (ciphertexts : Array Ciphertext) : Uint256

  /-- `keccak256(abi.encode(block.chainid, address(this),
                            keccak256(abi.encode(ciphertexts))))` -/
  opaque ciphertextsContextHash
    (chainId : Uint256) (poolAddress : Address)
    (ciphertexts : Array Ciphertext) : Uint256

  /-- `sha256(abi.encodePacked(merkleRoot, contextHash,
                               nullifierHashes, newCommitments))` -/
  opaque publicSignalsSha256
    (merkleRoot contextHash : Uint256)
    (nullifierHashes newCommitments : Array Uint256) : Uint256
end AbiSpec

end Benchmark.Cases.UnlinkXyz.Pool
