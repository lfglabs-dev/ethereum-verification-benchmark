import Benchmark.Cases.Paraclear.DirectDepositBacking.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

/--
A successful modeled Paraclear direct deposit cannot reduce backing slack for the
deposited token. Replace the placeholder with a complete proof.
-/
theorem directDeposit_preservesBackingSlack
    {Account Token : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Token]
    [Zero Account] [Zero Token]
    (state state' : State Account Token)
    (input : DirectDepositInput Account Token) :
    DirectDepositPreservesBackingSlack state state' input := by
  exact ?_

end Benchmark.Cases.Paraclear.DirectDepositBacking
