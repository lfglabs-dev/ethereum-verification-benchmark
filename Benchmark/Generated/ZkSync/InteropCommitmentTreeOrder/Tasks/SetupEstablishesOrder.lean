import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256

/-- `setup` on fresh-zero storage establishes `IMTOrder`. -/
theorem setup_establishes_order (s : ContractState)
    (hFresh : freshZeroStorage s) :
    IMTOrder (IndexedMerkleTree.setup.run s).snd := by
  exact ?_

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
