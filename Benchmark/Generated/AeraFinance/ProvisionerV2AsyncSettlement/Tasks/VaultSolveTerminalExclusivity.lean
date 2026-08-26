import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

theorem vault_solve_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    vault_solve_terminal_exclusivity_spec requestKey s := by
  exact ?_

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
