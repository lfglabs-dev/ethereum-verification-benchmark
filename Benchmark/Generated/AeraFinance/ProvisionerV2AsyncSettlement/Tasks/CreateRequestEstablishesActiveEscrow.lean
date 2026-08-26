import Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement

open Verity
open Verity.EVM.Uint256

/-- Request creation establishes the reachable active-escrow premise used by all
    terminal settlement theorems. -/
theorem create_request_establishes_active_escrow
    (requestKey : Address) (kind amount : Uint256) (isFixedPrice : Bool)
    (s : ContractState)
    (hKind : kind = depositKind ∨ kind = redeemKind)
    (hInactive : activeOf s requestKey = 0)
    (hBalanceGrows :
      escrowBalanceOf s kind <= add (escrowBalanceOf s kind) amount)
    (hAmountCovered :
      amount <= add (escrowBalanceOf s kind) amount) :
    create_request_establishes_active_escrow_spec requestKey kind amount isFixedPrice s := by
  exact ?_

end Benchmark.Cases.AeraFinance.ProvisionerV2AsyncSettlement
