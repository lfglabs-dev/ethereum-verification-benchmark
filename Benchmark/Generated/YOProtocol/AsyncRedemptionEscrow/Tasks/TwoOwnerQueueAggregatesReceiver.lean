import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Distinct non-vault owners make two positive-gross queued requests under
    separate sender contexts and aggregate into one receiver record. -/
theorem two_owner_queue_aggregation
    (firstShares firstGross secondShares secondGross : Uint256)
    (firstOwner secondOwner receiver : Address) (s : ContractState)
    (hDistinctOwners : firstOwner != secondOwner)
    (hVault : vaultAddress s != zeroAddress)
    (hFirstOwner : firstOwner != zeroAddress)
    (hSecondOwner : secondOwner != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hFirstNotVault : firstOwner != vaultAddress s)
    (hSecondNotVault : secondOwner != vaultAddress s)
    (hFirstPositive : firstShares > 0)
    (hSecondPositive : secondShares > 0)
    (hFirstGrossPositive : firstGross > 0)
    (hSecondGrossPositive : secondGross > 0)
    (hUnpaused : pausedOf s = 0)
    (hFirstShares : shareBalanceOf s firstOwner >= firstShares)
    (hSecondShares : shareBalanceOf s secondOwner >= secondShares)
    (hErc20 : erc20WellFormed s)
    (hVaultSequentialCapacity :
      (shareBalanceOf s (vaultAddress s) : Nat) + (firstShares : Nat) + (secondShares : Nat) <=
        (totalSupplyOf s : Nat))
    (hTotalCapacity :
      (totalPendingAssetsOf s : Nat) + (firstGross : Nat) + (secondGross : Nat) <=
        Verity.Stdlib.Math.MAX_UINT256)
    (hSharesCapacity :
      (pendingSharesOf s receiver : Nat) + (firstShares : Nat) + (secondShares : Nat) <=
        Verity.Stdlib.Math.MAX_UINT256)
    (hAssetsCapacity :
      (pendingAssetsOf s receiver : Nat) + (firstGross : Nat) + (secondGross : Nat) <=
        Verity.Stdlib.Math.MAX_UINT256)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    two_owner_queue_aggregation_spec firstShares firstGross secondShares secondGross
      firstOwner secondOwner receiver s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
