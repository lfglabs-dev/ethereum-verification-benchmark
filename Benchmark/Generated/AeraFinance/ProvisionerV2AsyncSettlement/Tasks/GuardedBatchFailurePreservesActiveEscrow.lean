import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

theorem guarded_batch_failure_preserves_active_escrow
    (firstKey secondKey : Address) (firstAmount secondAmount : Uint256)
    (s : ContractState)
    (hDistinct : firstKey ≠ secondKey)
    (hFirstActive : activeOf s firstKey = 1)
    (hSecondActive : activeOf s secondKey = 1)
    (hKinds :
      (requestKindOf s firstKey = depositKind ∧
        requestKindOf s secondKey = depositKind) ∨
      (requestKindOf s firstKey = redeemKind ∧
        requestKindOf s secondKey = redeemKind))
    (hFirstAmount : escrowAmountOf s firstKey = firstAmount)
    (hSecondAmount : escrowAmountOf s secondKey = secondAmount)
    (hSecondCovered : activeEscrowCovered s secondKey)
    (hRemaining :
      firstAmount <=
        sub (escrowBalanceOf s (requestKindOf s firstKey)) secondAmount) :
    guarded_batch_failure_preserves_active_escrow_spec
      firstKey secondKey firstAmount secondAmount s := by
  exact ?_

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
