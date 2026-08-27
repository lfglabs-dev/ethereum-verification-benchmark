# interop_commitment_tree_order

Source:
- `matter-labs/era-contracts`
- commit `e5f6e004a09f667c6109e44c4fe1f81658127631`
- file `l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol`

Focus:
- `setup`
- `insert`
- linked-list order from sentinel 0 (`IMTOrder`)
- nonzero-domain `valueToIndex`
- leaves-only append frame

Out of scope:
- FullMerkle hashing and root bytes
- `verifyInclusion` / `verifyNonInclusion`
- wrapper appender hook, events, gas burn
