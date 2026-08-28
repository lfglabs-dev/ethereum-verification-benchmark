import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Contract
import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Proofs

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

def caseReady : Bool := true

-- Terminal-proof audit: these declarations must have no custom or `sorry` axioms.
#print axioms setup_establishes_valid_state
#print axioms insert_preserves_order

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
