import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256
set_option linter.unusedSimpArgs false

/-- LP refund completes the quote and assigns no more than the registered amount. -/
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

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
