import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256

/-- Successful `insert` mutates only the predecessor link, the fresh leaf,
    `valueToIndex[value]`, and `leafNumber`. -/
theorem insert_leaf_frame
    (value lowHint : Uint256) (s s' : ContractState) :
    insert_leaf_frame_spec value lowHint s s' := by
  exact ?_

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
