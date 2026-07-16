import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Full clear rejects immediate replay; a distinct, funded request owner can
    queue the pair again, with capacity for both source-permitted burns. -/
theorem full_clear_requeue_replay
    (receiver requestOwner : Address) (shares grossAssets : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hRequestOwner : requestOwner != zeroAddress)
    (hRequestOwnerNotVault : requestOwner != vaultAddress s)
    (hSharesPositive : shares > 0)
    (hGrossPositive : grossAssets > 0)
    (hUnpaused : pausedOf s = 0)
    (hPendingShares : pendingSharesOf s receiver = shares)
    (hPendingAssets : pendingAssetsOf s receiver = grossAssets)
    (hGlobal : totalPendingAssetsOf s >= grossAssets)
    (hVaultShares : shareBalanceOf s (vaultAddress s) >= shares)
    (hRequestShares : shareBalanceOf s requestOwner >= shares)
    (hErc20 : erc20WellFormed s)
    (hTwoBurnCapacity : 2 * (shares : Nat) <= (totalSupplyOf s : Nat))
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    full_clear_requeue_replay_spec receiver requestOwner shares grossAssets s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
