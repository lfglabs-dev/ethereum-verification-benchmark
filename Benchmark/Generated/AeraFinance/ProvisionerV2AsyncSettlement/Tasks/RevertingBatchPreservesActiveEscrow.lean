import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

theorem reverting_batch_preserves_active_escrow
    (requestKey otherKey : Address) (s : ContractState)
    (hDistinct : requestKey ≠ otherKey)
    (hActive : activeOf s requestKey = 1)
    (hOtherActive : activeOf s otherKey = 1)
    (hKinds :
      (requestKindOf s requestKey = depositKind ∧
        requestKindOf s otherKey = redeemKind) ∨
      (requestKindOf s requestKey = redeemKind ∧
        requestKindOf s otherKey = depositKind))
    (hCovered : activeEscrowCovered s requestKey)
    (hOtherCovered : activeEscrowCovered s otherKey) :
    reverting_batch_preserves_active_escrow_spec requestKey otherKey s := by
  exact ?_

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
