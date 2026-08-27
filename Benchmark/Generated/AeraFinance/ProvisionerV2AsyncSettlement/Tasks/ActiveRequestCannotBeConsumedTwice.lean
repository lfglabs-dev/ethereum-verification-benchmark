import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

theorem active_request_cannot_be_consumed_twice
    (requestKey : Address) (s : ContractState)
    (hActive : activeOf s requestKey = 1)
    (hKind : requestKindOf s requestKey = depositKind ∨
      requestKindOf s requestKey = redeemKind)
    (hCovered : activeEscrowCovered s requestKey) :
    active_request_cannot_be_consumed_twice_spec requestKey s := by
  exact ?_

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
