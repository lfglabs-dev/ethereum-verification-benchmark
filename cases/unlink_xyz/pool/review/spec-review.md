# Spec review

The Verity model of `UnlinkPool` exposes four classes of declarations.

## 1. Pure Lean specs

- `Specs.lean` — assumed protocol boundaries (Poseidon T3 / T4, Permit2
  `permitWitnessTransferFrom`, Lazy-IMT root, Groth16 `verifyProof`,
  three ABI composite hashes) declared via `opaque` + `axiom` with the
  `unlink_verity_*` axiom-naming convention.
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

## 4. Blocked surface (`Contract.lean`, `BLOCKED(verity#1832):` markers)

The public ZK entry points carrying `Transaction[] calldata` /
`WithdrawalTransaction[] calldata` parameters are documented but not
translated, because their struct elements contain nested dynamic
members (`uint256[]`, `Ciphertext[]`). The macro rejects struct
parameter projection from an ABI-dynamic-root at
`Verity/Macro/Translate.lean:1715`. Tracked dedicated under verity#1832
(umbrella: verity#1760). Once that lands, the following land 1:1 from
`UnlinkPool.sol`:

- `transfer(Transaction[] calldata _transactions)`
  (UnlinkPool.sol:309 ff.)
- `withdraw(WithdrawalTransaction[] calldata _withdrawals)`
- `emergencyWithdraw(WithdrawalTransaction[] calldata _transactions)`
  (UnlinkPool.sol:374-383)

### Source confirmation: no UnlinkAdapter at this pin

`UnlinkAdapter`, `adapterDeposit`, and `adapterWithdraw` were deleted
upstream in `d9c8948 chore(contracts): delete UnlinkAdapter + strip
adapter surface (UE-425)`, which predates our pin
`4bc46c1fffbc0e146dccfff5b9fe00167121b27b`. The umbrella verity#1760
references the older multi-relayer release that still carried the
adapter; at the current pin, the case scope is `UnlinkPool` only.

`deposit` translation is gated by verity#1824 (Array-param helper
lowering), not verity#1832: `Note[]` is a static-tuple-element array
the macro already accepts, but the natural deposit translation needs
internal helpers (`_validateAndCollectDeposit`, `_insertLeaves`,
`_transferWithBalanceCheck`) accepting `Array Note` / `Array Uint256`
parameters — which verity#1824 documents as unsupported in current
macro helper lowering.

## Build status

Case stage: `scoped`. `lake build Benchmark.Cases.UnlinkXyz.Pool.Compile`
green locally. Promotion to `build_green` happens when:

1. verity#1832 lands (struct parameter projection from an ABI-dynamic
   root).
2. verity#1824 lands (Array-param helper lowering) — for the
   helper-factored `deposit` body.
3. The lakefile in this repo bumps to the resulting verity commit.
4. The three blocked entry points (`transfer`, `withdraw`,
   `emergencyWithdraw`) and `deposit` are wired through.

## Next milestones

- `build_green` once `deposit` + the three blocked entries elaborate.
- `proof_partial` after a target invariant is selected (likely:
  per-token conservation across `deposit + withdraw` once nullifier
  spend is gated, modeled with the four assumed boundaries).
