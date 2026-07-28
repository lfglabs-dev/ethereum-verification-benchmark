import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Successful fulfillment independently bounds/decrements gross assets and
    shares, burns pooled shares, and uses the current fee split. -/
theorem fulfill_redeem_accounting
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
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
    fulfill_redeem_accounting_spec shares grossAssets receiver s result := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
