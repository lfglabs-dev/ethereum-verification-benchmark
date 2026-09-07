import Benchmark.Cases.Paraclear.DirectDepositBacking.Contract
import Benchmark.Cases.Paraclear.DirectDepositBacking.Specs
import Benchmark.Cases.Paraclear.DirectDepositBacking.Proofs
import Benchmark.Cases.Paraclear.DirectDepositBacking.Tests

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

def caseReady : Bool := true

#print axioms directDeposit_preservesBackingSlack
#print axioms directDeposit_preservesNonnegativeBacking

end Benchmark.Cases.Paraclear.DirectDepositBacking

