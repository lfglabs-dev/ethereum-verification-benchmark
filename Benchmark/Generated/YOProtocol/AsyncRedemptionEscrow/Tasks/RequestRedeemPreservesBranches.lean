import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Successful preview and balance-read outcomes are explicit assumptions. The
    theorem distinguishes the source instant and queued request transitions. -/
theorem request_redeem_branching
    (shares grossAssets externalUnderlyingBalance : Uint256) (receiver owner : Address)
    (previewSucceeds balanceReadSucceeds : Bool) (s : ContractState)
    (hUnpaused : pausedOf s = 0)
    (hVault : vaultAddress s != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwnerIsSender : owner = s.sender)
    (hShares : shares > 0)
    (hOwnerShares : shareBalanceOf s owner >= shares)
    (hErc20 : erc20WellFormed s)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s)
    (hPreviewSucceeds : previewSucceeds = true)
    (hBalanceReadSucceeds : balanceReadSucceeds = true)
    (hQueuedAdds : availableUnderlyingOf s externalUnderlyingBalance < grossAssets →
      checkedAddFits (totalPendingAssetsOf s) grossAssets ∧
      checkedAddFits (pendingSharesOf s receiver) shares ∧
      checkedAddFits (pendingAssetsOf s receiver) grossAssets) :
    let result :=
      (YoAsyncRedemptionEscrow.requestRedeem shares receiver owner grossAssets
        externalUnderlyingBalance previewSucceeds balanceReadSucceeds true true).run s
    request_redeem_branching_spec shares grossAssets externalUnderlyingBalance receiver owner s result := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
