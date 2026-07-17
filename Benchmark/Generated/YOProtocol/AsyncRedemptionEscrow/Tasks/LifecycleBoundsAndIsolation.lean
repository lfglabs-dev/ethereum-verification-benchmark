import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Under the explicit no-callback-state-mutation assumption, a successful
    fulfillment directly changes only the selected receiver record. -/
theorem lifecycle_bounds_and_isolation
    (receiver other : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hPendingShares : pendingSharesOf s receiver != 0)
    (hPendingAssets : pendingAssetsOf s receiver != 0)
    (hShareBound : shares <= pendingSharesOf s receiver)
    (hAssetBound : grossAssets <= pendingAssetsOf s receiver)
    (hGlobalBound : grossAssets <= totalPendingAssetsOf s)
    (hVaultShares : shares <= shareBalanceOf s (vaultAddress s))
    (hErc20 : erc20WellFormed s)
    (hUnpaused : pausedOf s = 0)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    let result :=
      (YoAsyncRedemptionEscrow.fulfillRedeem receiver shares grossAssets true true true true).run s
    lifecycle_bounds_and_isolation_spec shares grossAssets receiver other s result := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
