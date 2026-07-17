import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Source-reachable Candidate G trace from a queued `(100,200)` pair. It
    proves all six zero-component settlement shapes and the positive,
    non-proportional `(1,199)` fulfillment remain accepted. -/
theorem candidate_g_source_reachability
    (receiver owner : Address) (s : ContractState)
    (hAuthority : authorityOf s != zeroAddress)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hReceiverNotOwner : receiver != owner)
    (hReceiverNotVault : receiver != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hUnpaused : pausedOf s = 0)
    (hInitialPendingShares : pendingSharesOf s receiver = 0)
    (hInitialPendingAssets : pendingAssetsOf s receiver = 0)
    (hInitialPendingTotal : totalPendingAssetsOf s = 0)
    (hOwnerShares : shareBalanceOf s owner >= 100)
    (hErc20 : erc20WellFormed s)
    (hFeeDivisor : feeDivisorFits s)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    candidate_g_source_reachable_spec receiver owner s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
