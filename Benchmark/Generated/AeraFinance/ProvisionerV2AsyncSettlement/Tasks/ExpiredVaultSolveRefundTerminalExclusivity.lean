import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

/-- Prove that an expired vault-solve entry takes the refund branch and consumes
    deposit or redeem escrow at most once. -/
theorem expired_vault_solve_refund_terminal_exclusivity
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    expired_vault_solve_refund_terminal_exclusivity_spec requestKey s := by
  exact ?_

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
