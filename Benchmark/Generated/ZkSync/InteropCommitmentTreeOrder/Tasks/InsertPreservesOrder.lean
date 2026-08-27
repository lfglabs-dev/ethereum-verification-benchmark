import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256

/-- A successful `insert` preserves `IMTOrder`. -/
theorem insert_preserves_order
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    IMTOrder ((IndexedMerkleTree.insert value lowHint).run s).snd := by
  exact ?_

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
