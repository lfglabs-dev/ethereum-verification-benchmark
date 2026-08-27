# interop_commitment_tree_order

Source:
- `matter-labs/era-contracts`
- commit `e5f6e004a09f667c6109e44c4fe1f81658127631`
- file `l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol`

Focus:
- `setup`
- `insert`
- one covering ordered chain from sentinel 0 (`IMTOrder`)
- physical append order is not sorted order
- leaves-only append frame
- `valueToIndex` is a separate map fact, not in the public theorem

Out of scope:
- FullMerkle hashing and root bytes
- `verifyInclusion` / `verifyNonInclusion`
- wrapper appender hook, events, gas burn
