import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- One-sided records are produced by real zero-component settlements from a
    queued pair; both dormant directions are then repaired by a positive queue. -/
theorem malformed_pair_lifecycle
    (receiver owner repairOwner : Address)
    (queuedShares queuedGross repairShares repairGross : Uint256) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hRepairOwner : repairOwner != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hRepairOwnerNotVault : repairOwner != vaultAddress s)
    (hDistinctOwners : owner != repairOwner)
    (hUnpaused : pausedOf s = 0)
    (hQueuedSharesPositive : queuedShares > 0)
    (hQueuedGrossPositive : queuedGross > 0)
    (hRepairSharesPositive : repairShares > 0)
    (hRepairGrossPositive : repairGross > 0)
    (hInitialPendingShares : pendingSharesOf s receiver = 0)
    (hInitialPendingAssets : pendingAssetsOf s receiver = 0)
    (hInitialPendingTotal : totalPendingAssetsOf s = 0)
    (hOwnerShares : shareBalanceOf s owner >= queuedShares)
    (hRepairOwnerShares : shareBalanceOf s repairOwner >= repairShares)
    (hErc20 : erc20WellFormed s)
    (hVaultSequentialCapacity :
      (shareBalanceOf s (vaultAddress s) : Nat) + (queuedShares : Nat) + (repairShares : Nat) <=
        (totalSupplyOf s : Nat))
    (hQueuedCancelReceiverFit :
      (shareBalanceOf s receiver : Nat) + (queuedShares : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hRepairSharesAdd :
      (queuedShares : Nat) + (repairShares : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hRepairAssetsAdd :
      (queuedGross : Nat) + (repairGross : Nat) <= Verity.Stdlib.Math.MAX_UINT256)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    malformed_pair_lifecycle_spec receiver owner repairOwner queuedShares queuedGross repairShares repairGross s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
