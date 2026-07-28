import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- From a positive two-sided record, source-permitted `(0,0)` fulfillment and
    cancellation both succeed while EVM-observable storage remains unchanged. -/
theorem zero_component_lifecycle
    (receiver : Address) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    zero_component_lifecycle_spec receiver s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
