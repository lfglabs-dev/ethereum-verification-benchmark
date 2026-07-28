# Upstream metadata

- Repository: https://github.com/zama-ai/protocol-apps
- Branch at capture: `main`
- Commit: `2f88eef1d0b545438b1f74e21cdff7ea771805da`
- Contract path: `contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol`
- Git blob: `c24aea5237bf34db183ec0c72c4180f96a1777ea`
- SHA-256: `c504d7a7000e7bc188b5ae35d3fbe3f80ceddd219e87c8d049d66f3a11273b74`
- Source language: Solidity `^0.8.27`

The retained `ERC7984Upgradeable.sol` is a byte-for-byte copy of the file at the
commit above. Reproduce the provenance checks with:

```sh
git clone https://github.com/zama-ai/protocol-apps.git
git -C protocol-apps checkout --detach 2f88eef1d0b545438b1f74e21cdff7ea771805da
git -C protocol-apps rev-parse HEAD
git -C protocol-apps rev-parse HEAD:contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol
sha256sum protocol-apps/contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol
```

The selected source says it was ported from OpenZeppelin Confidential Contracts
commit `f0914b66f9f3766915403587b1ef1432d53054d3`. This benchmark's comparison
point is the repository's separately retained OpenZeppelin reference case at
commit `83364738f0d2b1655c60627588e3493099c359f7`; do not conflate those pins.

## Scoped FHESafeMath dependency provenance

At the captured protocol-apps commit, the selected Solidity source imports
`@openzeppelin/confidential-contracts/utils/FHESafeMath.sol`. Its sibling
`contracts/confidential-wrapper/package-lock.json` resolves
`@openzeppelin/confidential-contracts` to `0.4.0`; the locked package tarball
SHA-512 is
`adb82557ec166323756dcea8828a80ad087ee6bc108f33ad53bfbf02baf5a559394f9ad6f48b803c2e88125f3cacd6f446e022ba92b6cadaaef42c084e5660f2`.
The package's `utils/FHESafeMath.sol` has SHA-256
`72eb2b13fc6799ab5ff91241bc6f07c4536e9a120522720f0e0cdef5940188bd`.

This provenance supports only the initialized `tryDecrease` call site in the
selected `_update` branch. In that dependency version, after the selected
source guard establishes an initialized `oldValue`, `tryDecrease` computes
`success = FHE.ge(oldValue, delta)` and selects either
`FHE.sub(oldValue, delta)` or `oldValue`. The Lean slice preserves this branch
and the caller's preceding initialization guard. It does not claim to model
the dependency's uninitialized-handle branches or other FHESafeMath functions.

Reason for selection:

- `_update` requires `FHE.isInitialized(fromBalance)` before `tryDecrease` and
  before balance writes;
- this makes an uninitialized sender a reverting case even when the requested
  amount is zero;
- an initialized insufficient sender still follows the silent zero-transfer
  behavior after earlier wrapper and plaintext checks pass.
