import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256
set_option linter.unusedSimpArgs false

/-- User refund completes the quote and assigns no more than the registered amount. -/
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
