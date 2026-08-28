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
- `IMTValidState` combines central `IMTOrder` with the minimal `valueToIndex`
  relation needed for its exact duplicate guard to derive real leaf-value absence

Out of scope:
- FullMerkle hashing and root bytes
- `verifyInclusion` / `verifyNonInclusion`
- wrapper appender hook, events, gas burn
