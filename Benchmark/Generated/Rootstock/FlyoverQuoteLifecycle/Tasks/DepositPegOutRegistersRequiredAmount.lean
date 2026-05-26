import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256
set_option linter.unusedSimpArgs false

/-- `depositPegOut` records exactly the required Rootstock amount for a fresh quote. -/
theorem depositPegOut_registers_required_amount
    (quoteHash : Address)
    (value callFee gasFee penaltyFee msgValue dustThreshold : Uint256)
    (changeRefundSucceeds : Bool)
    (blockTimestamp : Uint256)
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
    let s' := ((PegOutLifecycle.depositPegOut quoteHash value callFee gasFee penaltyFee msgValue
      dustThreshold changeRefundSucceeds blockTimestamp).run s).snd
    depositPegOut_registers_required_amount_spec
      quoteHash value callFee gasFee penaltyFee msgValue dustThreshold changeRefundSucceeds
      blockTimestamp s s' := by
  by_cases hChange : sub msgValue (add (add value callFee) gasFee) >= dustThreshold
  · have hRefundSucceeds : changeRefundSucceeds = true := by
      simpa [hChange] using hChangeRefund
    simp [depositPegOut_registers_required_amount_spec, depositedAmount, depositTimestampOf,
      PegOutLifecycle.depositPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteDepositTimestamp,
      hValueAndCallNoOverflow, hRequiredNoOverflow, hFresh, hIncomplete, hEnough,
      hChange, hRefundSucceeds,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]
  · simp [depositPegOut_registers_required_amount_spec, depositedAmount, depositTimestampOf,
      PegOutLifecycle.depositPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteDepositTimestamp,
      hValueAndCallNoOverflow, hRequiredNoOverflow, hFresh, hIncomplete, hEnough,
      hChange, getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Pure.pure, Contract.run, ContractResult.snd]

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
