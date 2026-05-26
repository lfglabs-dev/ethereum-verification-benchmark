import Verity.Specs.Common
import Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Contract

namespace Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle

open Verity
open Verity.EVM.Uint256

/-- Amount deposited and still registered for a quote. -/
def depositedAmount (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 0 quoteHash

/-- Explicit quote penalty passed to the external collateral slash call. -/
def penaltyAmount (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 1 quoteHash

/-- Completion flag for `PegOutRecord.completed`. -/
def completed (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 2 quoteHash

/-- Amount paid directly to the LP on the Rootstock side. -/
def paidToLp (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 3 quoteHash

/-- Amount paid directly to the user refund address on the Rootstock side. -/
def paidToUser (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 4 quoteHash

/-- Recipient-keyed fallback balance credited when a Rootstock transfer fails. -/
def fallbackBalance (s : ContractState) (recipient : Address) : Uint256 :=
  s.storageMap 5 recipient

/-- Local witness for the external collateral slash call amount. -/
def slashCallAmountOf (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 6 quoteHash

/-- Quote existence flag corresponding to `quote.lbcAddress != address(0)`. -/
def registered (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 7 quoteHash

/-- Stored quote deposit timestamp used by the LP penalty predicate. -/
def depositTimestampOf (s : ContractState) (quoteHash : Address) : Uint256 :=
  s.storageMap 8 quoteHash

/-- The external slash call is reached with the explicit quote penalty when it occurs. -/
def slashCallMatchesPenalty (s s' : ContractState) (quoteHash : Address) (slashed : Bool) : Prop :=
  if slashed then
    slashCallAmountOf s' quoteHash = penaltyAmount s quoteHash
  else
    slashCallAmountOf s' quoteHash = slashCallAmountOf s quoteHash

/-- Deposit stores exactly `value + callFee + gasFee` for this quote. -/
def depositPegOut_registers_required_amount_spec
    (quoteHash : Address)
    (value callFee gasFee : Uint256)
    (_penaltyFee _msgValue _dustThreshold : Uint256)
    (_changeRefundSucceeds : Bool)
    (blockTimestamp : Uint256)
    (_s s' : ContractState) : Prop :=
  depositedAmount s' quoteHash = add (add value callFee) gasFee ∧
    depositTimestampOf s' quoteHash = blockTimestamp

/-- LP settlement assigns the quote amount once, either as a transfer or fallback balance. -/
def refundPegOut_conserves_quote_amount_spec
    (quoteHash : Address)
    (lpRskAddress : Address)
    (transferSucceeds : Bool)
    (transferTime btcBlockTime firstConfirmationTimestamp
      expireDate currentTimestamp expireBlock currentBlock : Uint256)
    (s s' : ContractState) : Prop :=
  let expectedConfirmation :=
    add (add (depositTimestampOf s quoteHash) transferTime) btcBlockTime
  let shouldPenalize :=
    (firstConfirmationTimestamp > expectedConfirmation) ||
      (currentTimestamp > expireDate) ||
      (currentBlock > expireBlock)
  completed s' quoteHash = completedFlag ∧
    registered s' quoteHash = 0 ∧
    (if transferSucceeds then
      paidToLp s' quoteHash = depositedAmount s quoteHash ∧
        fallbackBalance s' lpRskAddress = fallbackBalance s lpRskAddress
    else
      paidToLp s' quoteHash = paidToLp s quoteHash ∧
        fallbackBalance s' lpRskAddress =
          add (fallbackBalance s lpRskAddress) (depositedAmount s quoteHash)) ∧
    slashCallMatchesPenalty s s' quoteHash shouldPenalize

/-- User settlement assigns the quote amount once, either as a transfer or fallback balance. -/
def refundUserPegOut_conserves_quote_amount_spec
    (quoteHash : Address)
    (rskRefundAddress : Address)
    (transferSucceeds : Bool)
    (s s' : ContractState) : Prop :=
  completed s' quoteHash = completedFlag ∧
    registered s' quoteHash = 0 ∧
    (if transferSucceeds then
      paidToUser s' quoteHash = depositedAmount s quoteHash ∧
        fallbackBalance s' rskRefundAddress = fallbackBalance s rskRefundAddress
    else
      paidToUser s' quoteHash = paidToUser s quoteHash ∧
        fallbackBalance s' rskRefundAddress =
          add (fallbackBalance s rskRefundAddress) (depositedAmount s quoteHash)) ∧
    slashCallAmountOf s' quoteHash = penaltyAmount s quoteHash

end Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle
