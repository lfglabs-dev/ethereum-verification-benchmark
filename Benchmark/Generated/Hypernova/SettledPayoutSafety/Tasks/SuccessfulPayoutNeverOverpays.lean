import Benchmark.Cases.Hypernova.SettledPayoutSafety.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Hypernova.SettledPayoutSafety

open Verity
open Verity.EVM.Uint256

/-- Every successful payout transfers no more than its authorized gross amount. -/
theorem successfulPayout_never_overpays
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) :
    successfulPayoutNeverOverpays s trader fundedAccountId amount deadline v r signatureS
      transferSucceeds := by
  exact ?_

end Benchmark.Cases.Hypernova.SettledPayoutSafety
