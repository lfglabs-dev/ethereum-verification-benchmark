import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256

/-- `setup` on fresh-zero storage establishes the ordered chain and
    `valueToIndex` consistency (`IMTValidState`). -/
theorem setup_establishes_valid_state (s : ContractState)
    (hFresh : freshZeroStorage s) :
    IMTValidState (IndexedMerkleTree.setup.run s).snd := by
  exact ?_

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
