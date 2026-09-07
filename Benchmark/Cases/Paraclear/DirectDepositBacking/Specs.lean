import Benchmark.Cases.Paraclear.DirectDepositBacking.Contract

/-!
# The single business specification

`DirectDepositPreservesBackingSlack` is the only public business specification in this
POC. Helper definitions make its accounting meaning explicit.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

section Spec

variable {Account Token : Type}
variable [Fintype Account] [DecidableEq Account] [DecidableEq Token]
variable [Zero Account] [Zero Token]

/-- Sum of positive posted balances for one token over unique account identities. -/
def postedPositiveBalances (state : State Account Token) (token : Token) : Int :=
  ∑ account : Account, max (state.internalBalance account token) 0

/-- The contract's raw ERC20 custody normalized to Paraclear's eight decimals. -/
def normalizedCustody (state : State Account Token) (token : Token) : Int :=
  (toInternal (state.custodyRaw token) (state.tokenDecimals token) : Int)

/-- Positive values mean custody exceeds posted positive internal balances. -/
def backingSlack (state : State Account Token) (token : Token) : Int :=
  normalizedCustody state token - postedPositiveBalances state token

/--
A successful public direct deposit cannot reduce the deposited token's backing slack.
-/
def DirectDepositPreservesBackingSlack
    (state state' : State Account Token)
    (input : DirectDepositInput Account Token) : Prop :=
  runDirectDeposit state input = some state' →
    backingSlack state' input.token ≥ backingSlack state input.token

end Spec

end Benchmark.Cases.Paraclear.DirectDepositBacking
