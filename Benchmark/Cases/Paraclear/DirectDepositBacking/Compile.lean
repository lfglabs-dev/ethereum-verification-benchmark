import Benchmark.Cases.Paraclear.DirectDepositBacking.Contract
import Benchmark.Cases.Paraclear.DirectDepositBacking.Specs
import Benchmark.Cases.Paraclear.DirectDepositBacking.Proofs
import Benchmark.Cases.Paraclear.DirectDepositBacking.SourceExecution
import Benchmark.Cases.Paraclear.DirectDepositBacking.Regression

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

def caseReady : Bool := true

#print axioms directDeposit_preservesBackingSlack
#print axioms directDeposit_preservesNonnegativeBacking
#print axioms source_success_refines
#print axioms source_success_preservesBackingSlack
#print axioms updateRecord_represents
#print axioms rejected_source_preserves_projection
#print axioms ordered_eq_source
#print axioms ordered_success_preservesBackingSlack
#print axioms reachableRecord_wellFormed
#print axioms ordered_success_storage_represents

end Benchmark.Cases.Paraclear.DirectDepositBacking
