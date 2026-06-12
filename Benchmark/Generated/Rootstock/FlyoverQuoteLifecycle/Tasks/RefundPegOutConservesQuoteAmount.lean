import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256

/-- LP refund completes the quote and assigns the registered amount. -/
theorem refundPegOut_conserves_quote_amount
    (quoteHash : Address)
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
      add (s.storageMap 5 (lpRecipientOf s quoteHash)) (s.storageMap 0 quoteHash) >=
        s.storageMap 5 (lpRecipientOf s quoteHash))
    (hRegistered : (s.storageMap 7 quoteHash == completedFlag) = true)
    (hIncomplete : (s.storageMap 2 quoteHash == 0) = true) :
    let s' := ((PegOutLifecycle.refundPegOut quoteHash transferSucceeds transferTime
      btcBlockTime firstConfirmationTimestamp expireDate currentTimestamp expireBlock currentBlock).run s).snd
    refundPegOut_conserves_quote_amount_spec quoteHash transferSucceeds transferTime
      btcBlockTime firstConfirmationTimestamp expireDate currentTimestamp expireBlock currentBlock s s' := by
  exact ?_

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
