import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256
set_option linter.unusedSimpArgs false

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

theorem refundPegOut_conserves_quote_amount
    (quoteHash : Address)
    (lpRskAddress : Address)
    (transferSucceeds : Bool)
    (transferTime btcBlockTime firstConfirmationTimestamp
      expireDate currentTimestamp expireBlock currentBlock : Uint256)
    (s : ContractState)
    (hPenaltyDeadlineNoOverflow :
      add (s.storageMap 8 quoteHash) transferTime >= s.storageMap 8 quoteHash)
    (hPenaltyExpectedNoOverflow :
      add (add (s.storageMap 8 quoteHash) transferTime) btcBlockTime >=
        add (s.storageMap 8 quoteHash) transferTime)
    (hFallbackNoOverflow :
      add (s.storageMap 5 lpRskAddress) (s.storageMap 0 quoteHash) >=
        s.storageMap 5 lpRskAddress)
    (hRegistered : (s.storageMap 7 quoteHash == completedFlag) = true)
    (hIncomplete : (s.storageMap 2 quoteHash == 0) = true) :
    let s' := ((PegOutLifecycle.refundPegOut quoteHash lpRskAddress transferSucceeds transferTime
      btcBlockTime firstConfirmationTimestamp expireDate currentTimestamp expireBlock currentBlock).run s).snd
    refundPegOut_conserves_quote_amount_spec quoteHash lpRskAddress transferSucceeds transferTime
      btcBlockTime firstConfirmationTimestamp expireDate currentTimestamp expireBlock currentBlock s s' := by
  have hRegistered' : (s.storageMap 7 quoteHash == 1) = true := by
    simpa [completedFlag] using hRegistered
  have hPenaltyDeadlineNoOverflow' :
      (s.storageMap 8 quoteHash).val <= (add (s.storageMap 8 quoteHash) transferTime).val := by
    simpa [GE.ge] using hPenaltyDeadlineNoOverflow
  have hPenaltyExpectedNoOverflow' :
      (add (s.storageMap 8 quoteHash) transferTime).val <=
        (add (add (s.storageMap 8 quoteHash) transferTime) btcBlockTime).val := by
    simpa [GE.ge] using hPenaltyExpectedNoOverflow
  have hFallbackNoOverflow' :
      (s.storageMap 5 lpRskAddress).val <=
        (add (s.storageMap 5 lpRskAddress) (s.storageMap 0 quoteHash)).val := by
    simpa [GE.ge] using hFallbackNoOverflow
  cases transferSucceeds <;>
    by_cases hPenalize :
      (((add (add (s.storageMap 8 quoteHash) transferTime) btcBlockTime).val <
          firstConfirmationTimestamp.val ∨
        expireDate.val < currentTimestamp.val) ∨
        expireBlock.val < currentBlock.val) <;>
    simp [refundPegOut_conserves_quote_amount_spec, slashCallMatchesPenalty,
      depositedAmount, penaltyAmount, completed, registered,
      paidToLp, fallbackBalance, slashCallAmountOf, depositTimestampOf, completedFlag,
      PegOutLifecycle.refundPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.lpPaid,
      PegOutLifecycle.internalBalance, PegOutLifecycle.slashCallAmount,
      PegOutLifecycle.quoteRegistered, PegOutLifecycle.quoteDepositTimestamp,
      hRegistered', hIncomplete, hPenaltyDeadlineNoOverflow', hPenaltyExpectedNoOverflow',
      hFallbackNoOverflow', hPenalize, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Pure.pure,
      Contract.run, ContractResult.snd]

theorem refundUserPegOut_conserves_quote_amount
    (quoteHash : Address)
    (rskRefundAddress : Address)
    (transferSucceeds : Bool)
    (s : ContractState)
    (hFallbackNoOverflow :
      add (s.storageMap 5 rskRefundAddress) (s.storageMap 0 quoteHash) >=
        s.storageMap 5 rskRefundAddress)
    (hRegistered : (s.storageMap 7 quoteHash == completedFlag) = true)
    :
    let s' := ((PegOutLifecycle.refundUserPegOut quoteHash rskRefundAddress transferSucceeds).run s).snd
    refundUserPegOut_conserves_quote_amount_spec quoteHash rskRefundAddress transferSucceeds s s' := by
  have hRegistered' : (s.storageMap 7 quoteHash == 1) = true := by
    simpa [completedFlag] using hRegistered
  have hFallbackNoOverflow' :
      (s.storageMap 5 rskRefundAddress).val <=
        (add (s.storageMap 5 rskRefundAddress) (s.storageMap 0 quoteHash)).val := by
    simpa [GE.ge] using hFallbackNoOverflow
  cases transferSucceeds <;>
    simp [refundUserPegOut_conserves_quote_amount_spec,
      depositedAmount, penaltyAmount, completed, registered,
      paidToUser, fallbackBalance, slashCallAmountOf, completedFlag,
      PegOutLifecycle.refundUserPegOut, PegOutLifecycle.quoteAmount,
      PegOutLifecycle.quotePenalty, PegOutLifecycle.quoteCompleted,
      PegOutLifecycle.userPaid,
      PegOutLifecycle.internalBalance, PegOutLifecycle.slashCallAmount,
      PegOutLifecycle.quoteRegistered,
      hRegistered', hFallbackNoOverflow', getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
