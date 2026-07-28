import Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow

open Verity
open Verity.EVM.Uint256

/-- Queue `(100,200)`, owner-update the fee, then fulfill under zero-recipient
    and receiver-equals-fee-recipient configurations. The flags are trusted ECM
    outcome/revert abstractions, so no external token balance delta is claimed. -/
theorem fee_aliasing
    (receiver owner : Address) (newFee : Uint256) (s : ContractState)
    (hVault : vaultAddress s != zeroAddress)
    (hReceiver : receiver != zeroAddress)
    (hOwner : owner != zeroAddress)
    (hOwnerNotVault : owner != vaultAddress s)
    (hOwnerIsSender : owner = s.sender)
    (hStoredOwner : ownerOf s = owner)
    (hNoAuthority : authorityOf s = zeroAddress)
    (hUnpaused : pausedOf s = 0)
    (hInitialPendingShares : pendingSharesOf s receiver = 0)
    (hInitialPendingAssets : pendingAssetsOf s receiver = 0)
    (hInitialPendingTotal : totalPendingAssetsOf s = 0)
    (hOwnerShares : shareBalanceOf s owner >= 100)
    (hErc20 : erc20WellFormed s)
    (hNewFeePositive : newFee > 0)
    (hNewFeeBound : newFee < maxFee)
    (hFeeChanged : feeOnWithdrawOf s != newFee)
    (hNewFeeDivisor : checkedAddFits newFee feeDenominator)
    (hPositiveNewFeeAmount : feeAmountWith 200 newFee > 0)
    (hUnderlyingNotVault : underlyingTokenOf s != vaultAddress s) :
    fee_aliasing_spec receiver owner newFee s := by
  exact ?_

end Benchmark.Cases.YOProtocol.AsyncRedemptionEscrow
