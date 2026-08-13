import Benchmark.Cases.Hypernova.SettledPayoutSafety.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Hypernova.SettledPayoutSafety

open Verity
open Verity.EVM.Uint256

/-- A valid settled payout applies the exact guarded accounting transition. -/
theorem validSettledPayout_is_safe
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool)
    (hValid : validSettledPayoutRequest s trader fundedAccountId amount deadline
      v r signatureS transferSucceeds) :
    settledPayoutSafety s trader fundedAccountId amount deadline v r signatureS
      transferSucceeds := by
  exact ?_

end Benchmark.Cases.Hypernova.SettledPayoutSafety
