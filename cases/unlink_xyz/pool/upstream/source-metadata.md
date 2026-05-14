# Upstream metadata

- Repository: https://github.com/unlink-xyz/monorepo
- Pinned commit: `4bc46c1fffbc0e146dccfff5b9fe00167121b27b`
- Contract file: `protocol/contracts/src/UnlinkPool.sol`
- Source ref: `https://github.com/unlink-xyz/monorepo@4bc46c1fffbc0e146dccfff5b9fe00167121b27b:protocol/contracts/src/UnlinkPool.sol`

## Companion files

The translation also references the following Solidity files at the same
commit:

- `protocol/contracts/src/lib/Models.sol` — `Note`, `Ciphertext`, `Proof`,
  `Transaction`, `WithdrawalTransaction`, `AdapterTransaction` struct shapes.
- `protocol/contracts/src/State.sol` — inherited state container (merkle
  root + nullifier-spent set + verifier router).
- `protocol/contracts/src/lib/InternalLazyIMT.sol` — append-only Lazy-IMT
  state mutated by `_insertLeaves`. Verity models this directly in the pool
  helper path.
- `protocol/contracts/src/VerifierRouter.sol` — Groth16 verifier circuit
  registry, accessed through `linked_externals`.
- `protocol/contracts/src/lib/Poseidon.sol` and `PoseidonT4.sol` —
  Poseidon hashes, routed through package-local opaque boundaries.

## Modeling boundaries

These external dependencies are routed through opaque helpers, ECMs, or
linked-external declarations per the `unlink-verity` package-split policy
documented in `lfglabs-dev/verity:docs/ROADMAP.md` "Unlink Audit Readiness":

| External | Treatment | Boundary / module name |
|----------|-----------|---------------------|
| Poseidon T3 / T4 | Opaque hash boundary | `poseidonT3` / `poseidonT4` |
| Permit2 `permitWitnessTransferFrom` | Linked external with balance-delta checks | `permitWitnessTransferFrom` |
| Lazy-IMT `_insert` | Source-shaped Lean helper over pool storage | `lazyInsert` / `insertLeaves` |
| Groth16 verifier dispatch | `linked_externals` against `VerifierRouter` | `getCircuit` + `verifySpend` |
| BN254 precompiles (0x06 / 0x07 / 0x08) | First-class Verity ECMs | `evm_bn256_add_precompile` / `evm_bn256_scalar_mul_precompile` / `evm_bn256_pairing_precompile` |
