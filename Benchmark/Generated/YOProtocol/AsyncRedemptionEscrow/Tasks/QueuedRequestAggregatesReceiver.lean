import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- A positive-gross, successful queued request moves shares into pooled vault
    custody and aggregates the receiver-keyed pair. -/
theorem queued_request_aggregation
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (previewSucceeds balanceReadSucceeds : Bool) (s : ContractState)
    (hUnpaused : pausedOf s = 0)
    (hVault : vaultAddress s != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hShares : shares > 0)
    (hGross : grossAssets > 0)
    (hOwnerShares : shareBalanceOf s owner >= shares)
    (hQueued : availableUnderlyingOf s externalUnderlyingBalance < grossAssets)
    (hErc20 : erc20WellFormed s)
    (hTotalAdd : checkedAddFits (totalPendingAssetsOf s) grossAssets)
    (hSharesAdd : checkedAddFits (pendingSharesOf s receiver) shares)
    (hAssetsAdd : checkedAddFits (pendingAssetsOf s receiver) grossAssets)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s)
    (hPreviewSucceeds : previewSucceeds = true)
    (hBalanceReadSucceeds : balanceReadSucceeds = true) :
    let result :=
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
        externalUnderlyingBalance previewSucceeds balanceReadSucceeds true true).run s
    queued_request_aggregation_spec shares grossAssets receiver owner s result := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
