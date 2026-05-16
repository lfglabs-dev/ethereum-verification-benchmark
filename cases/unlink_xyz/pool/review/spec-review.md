# Spec review

The Verity model of the Unlink pool slice exposes four classes of declarations.

## 1. Pure Lean specs

- `Specs.lean` — opaque protocol boundaries (Poseidon T3 / T4, Permit2
  `permitWitnessTransferFrom`, Lazy-IMT root, Groth16 `verifyProof`,
  three ABI composite hashes). These are trust-boundary declarations, not
  Lean `axiom` declarations.
- `InternalLazyIMT.lean` — full LazyIMT spec (Z_0..Z_32 default-zero
  tower, `_init` / `_insert` / `_update` / `_root` / `_rootWithDepth` /
  `_levels` / `_merkleProofElements`). Pure Lean spec consumed by the
  pool's `_insertLeaves` path; trusted as the algorithmic ground truth.
- `State.lean` — `StateStorage` record + `_initializeState`,
  `_insertLeaves`, `_spend`, `_setVerifierRouter` helpers. Renders
  Solidity's `abstract contract State` as a namespace of pure helpers.

## 2. Pool contract surface (`Contract.lean`)

Mirrors the Solidity source structure: storage layout (flattened over
the ERC-7201 namespace), custom errors block, immutables `PERMIT2`,
typed `linked_externals getCircuit`, constructor, initializer-modifier
`initialize`, owner / relayer admin functions, Ownable2Step transfer
glue, public views (`isRelayer`, `hashNote`).

## 3. Verifier router contract surface (`VerifierRouter.lean`)

Real `verity_contract VerifierRouter` declaration for the sibling
Groth16 circuit registry. It models Ownable2Step state, circuit
activation, circuit pause, event/error metadata, and the
`mapping(bytes32 => Circuit)` slot layout as
`MappingStruct(Uint256, [...])`; bytes32 circuit ids are carried as
`Uint256` because Verity's mapping key support is word-shaped at this
translation surface. The pool still dispatches to the router through its
typed `linked_externals getCircuit` boundary, matching the cross-contract
call shape in the source.

## 4. Remaining boundary surface

The public ZK entry points carrying `Transaction[] calldata` /
`WithdrawalTransaction[] calldata` parameters are now translated through
source-shaped dynamic-array projections. Poseidon T3/T4, Permit2, the
external Groth16 verifier contracts reached by `VerifierRouter`, and
host-level UUPS proxy storage rotation are documented modeling
boundaries rather than unsupported Verity translation features.

The pool's top-level inherited `StateStorage` / `LazyIMTData` storage
structs remain represented by explicit namespaced fields at their source
slots. This is the only intentional source-shape storage exclusion in the
case and is tracked upstream by verity#1758.

### Source confirmation: no UnlinkAdapter at this pin

`UnlinkAdapter`, `adapterDeposit`, and `adapterWithdraw` were deleted
upstream in `d9c8948 chore(contracts): delete UnlinkAdapter + strip
adapter surface (UE-425)`, which predates our pin
`4bc46c1fffbc0e146dccfff5b9fe00167121b27b`. The umbrella verity#1760
references the older multi-relayer release that still carried the
adapter; at the current pin, the case scope is `UnlinkPool` plus
`VerifierRouter`.

`deposit` is translated with source-shaped note validation, Permit2
witness transfer through the linked boundary, LazyIMT leaf insertion, and
the source-shaped `Deposited` event payload.

## Build status

Case stage: `build_green`. `lake build Benchmark.Cases.UnlinkXyz.Pool.Compile`
green locally. The build-green target is:

1. `unsupported_feature_codes: []` in the case and task manifests.
2. No pool-local Lean `axiom`, `sorry`, or `admit` declarations.
3. The lakefile points at the Verity revision required by the translation.

## Next milestones

- `proof_partial` after a target invariant is selected (likely:
  per-token conservation across `deposit + withdraw` once nullifier
  spend is gated, modeled with the explicit boundaries).
