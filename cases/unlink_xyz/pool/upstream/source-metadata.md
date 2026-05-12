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
  state mutated by `_insertLeaves`. Verity routes this as an assumed-status
  external library boundary.
- `protocol/contracts/src/VerifierRouter.sol` — Groth16 verifier circuit
  registry, accessed through `linked_externals`.
- `protocol/contracts/src/lib/Poseidon.sol` and `PoseidonT4.sol` —
  Poseidon T4 hash, assumed as a package-local axiom.

## Modeling boundaries

These external dependencies are routed through assumed-status ECMs or
linked-external declarations per the `unlink-verity` package-split policy
documented in `lfglabs-dev/verity:docs/ROADMAP.md` "Unlink Audit Readiness":

| External | Treatment | Axiom / module name |
|----------|-----------|---------------------|
| Poseidon T4 | Pure assumed axiom | `unlink_verity_poseidon_t4` |
| Permit2 `permitWitnessTransferFrom` | Assumed-status ECM with bubble-revert | `unlink_verity_permit2_permit_witness_transfer_from` |
| Lazy-IMT `_insert` | Assumed-status state-mutating helper | `unlink_verity_lazy_imt_insert` |
| Groth16 verifier dispatch | `linked_externals` against `VerifierRouter` | `unlink_verity_verifier_router_get_circuit` + `unlink_verity_groth16_verify_proof` |
| BN254 precompiles (0x06 / 0x07 / 0x08) | First-class Verity ECMs | `evm_bn256_add_precompile` / `evm_bn256_scalar_mul_precompile` / `evm_bn256_pairing_precompile` |
