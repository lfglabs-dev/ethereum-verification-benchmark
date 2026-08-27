import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256

/-- A successful `insert` preserves `IMTOrder`. -/
theorem insert_preserves_order
    (value lowHint : Uint256) (s : ContractState) :
    insert_preserves_spec value lowHint s := by
  exact ?_

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
