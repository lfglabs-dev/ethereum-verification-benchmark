# Spec review

The Verity model of `UnlinkPool` exposes four classes of declarations.

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

## 2. Verity contract surface (`Contract.lean`)

Mirrors the Solidity source structure: storage layout (flattened over
the ERC-7201 namespace), custom errors block, immutables `PERMIT2`,
typed `linked_externals getCircuit`, constructor, initializer-modifier
`initialize`, owner / relayer admin functions, Ownable2Step transfer
glue, public views (`isRelayer`, `hashNote`).

## 3. Sibling contract stub (`VerifierRouter.lean`)

Documented placeholder for the canonical `verity_contract VerifierRouter`
declaration using `MappingStruct(Uint256, [...])` for the Solidity
`mapping(bytes32 => Circuit)` slot layout. Two framework limitations
gate the full landing (literal value writes + `Uint256`-keyed reads
both fail typeclass synthesis in the macro path); the pool dispatches
to the router through typed `linked_externals` rather than direct
references, so the missing sibling is a translation completeness gap,
not a wire-up gap.

## 4. Remaining boundary surface

The public ZK entry points carrying `Transaction[] calldata` /
`WithdrawalTransaction[] calldata` parameters are now translated through
source-shaped dynamic-array projections. Poseidon T3/T4, Permit2, Groth16
verifier dispatch, and host-level UUPS proxy storage rotation are documented
modeling boundaries rather than unsupported Verity translation features.

### Source confirmation: no UnlinkAdapter at this pin

`UnlinkAdapter`, `adapterDeposit`, and `adapterWithdraw` were deleted
upstream in `d9c8948 chore(contracts): delete UnlinkAdapter + strip
adapter surface (UE-425)`, which predates our pin
`4bc46c1fffbc0e146dccfff5b9fe00167121b27b`. The umbrella verity#1760
references the older multi-relayer release that still carried the
adapter; at the current pin, the case scope is `UnlinkPool` only.

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
