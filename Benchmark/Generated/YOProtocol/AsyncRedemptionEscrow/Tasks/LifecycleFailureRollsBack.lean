import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Every rollback branch reaches its intended boundary: a reverting authority
    blocks the owner, pause is reached inside `_update`, and the receiver/fee
    failures respectively reach the first and conditional second SafeERC20 call. -/
theorem lifecycle_rollback
    (receiver : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hOwnerContext : s.sender = ownerOf s)
    (hOwner : ownerOf s != zeroAddress)
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
    (hPositiveFee : feeAmountOf s grossAssets > 0)
    (hFeeRecipient : feeRecipientOf s != zeroAddress)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    lifecycle_rollback_spec receiver shares grossAssets s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
