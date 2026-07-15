import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Public ERC-4626 `redeem` performs its own pause check before faithfully
    delegating to the successful queued `requestRedeem` branch. -/
theorem redeem_wrapper
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (s : ContractState)
    (hVault : vaultAddress s != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hUnpaused : pausedOf s = 0)
    (hSharesPositive : shares > 0)
    (hGrossPositive : grossAssets > 0)
    (hOwnerShares : shareBalanceOf s owner >= shares)
    (hQueued : availableUnderlyingOf s externalUnderlyingBalance < grossAssets)
    (hErc20 : erc20WellFormed s)
    (hTotalAdd : checkedAddFits (totalPendingAssetsOf s) grossAssets)
    (hSharesAdd : checkedAddFits (pendingSharesOf s receiver) shares)
    (hAssetsAdd : checkedAddFits (pendingAssetsOf s receiver) grossAssets)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    redeem_wrapper_spec shares grossAssets externalUnderlyingBalance receiver owner s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
