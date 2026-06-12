import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256

/-- `depositPegOut` records the required Rootstock amount and quote settlement fields. -/
theorem depositPegOut_registers_required_amount
    (quoteHash : Address)
    (value callFee gasFee penaltyFee msgValue dustThreshold : Uint256)
    (changeRefundSucceeds : Bool)
    (lpRskAddress rskRefundAddress : Address)
    (blockTimestamp : Uint256)
    (expireDate expireBlock : Uint256)
    (s : ContractState)
    (hValueAndCallNoOverflow : (add value callFee >= value) = true)
    (hRequiredNoOverflow : (add (add value callFee) gasFee >= add value callFee) = true)
    (hFresh : (s.storageMap 7 quoteHash == 0) = true)
    (hIncomplete : (s.storageMap 2 quoteHash == 0) = true)
    (hEnough : (add (add value callFee) gasFee <= msgValue) = true)
    (hChangeRefund :
      (if sub msgValue (add (add value callFee) gasFee) >= dustThreshold then
        changeRefundSucceeds
      else
        true) = true) :
    let s' := ((PegOutLifecycle.depositPegOut quoteHash value callFee gasFee
      penaltyFee msgValue dustThreshold changeRefundSucceeds lpRskAddress rskRefundAddress blockTimestamp
      expireDate expireBlock).run s).snd
    depositPegOut_registers_required_amount_spec
      quoteHash value callFee gasFee penaltyFee msgValue dustThreshold changeRefundSucceeds
      lpRskAddress rskRefundAddress blockTimestamp expireDate expireBlock s s' := by
  exact ?_

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
