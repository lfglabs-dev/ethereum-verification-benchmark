import Benchmark.Cases.Paraclear.DirectDepositBacking.Contract

/-!
# The single business specification

`DirectDepositPreservesBackingSlack` is the only public business specification in this
POC. Helper definitions make its accounting meaning explicit.

These quantities are mathematical observations, not additional Cairo storage:
* postedPositiveBalances sums max(balance, 0), so debts do not cancel another
  customer's positive claim. The sum is over all Account identities, NOT the
  registeredAccounts set. Interpreting it on Cairo requires a complete, unique
  account domain covering every positive balance.
* normalizedCustody converts external token holdings into the internal precision.
* backingSlack subtracts the positive claims from that normalized custody.
The property compares one successful deposit's endpoints; it neither establishes
initial solvency nor covers all future protocol operations.

The remaining relations document the implementation boundary:
WellFormed / StorageRepresents relate already-decoded balance records to numbers;
ReachableRecord only covers empty records followed by checked local updates;
ObservationsMatch couples entry custody to the supplied ERC20 before-read.
None is a mechanized connection to physical Cairo storage or concrete token calls.
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

section Storage

variable {Account Token : Type} [DecidableEq Token] [Zero Token]

def BalanceRecord.WellFormed (key : Token) (record : BalanceRecord Token) : Prop :=
  (record.tokenAddress = 0 → record.amount = 0) ∧
  (record.tokenAddress ≠ 0 → record.tokenAddress = key) ∧
  inI128 record.amount = true

variable [DecidableEq Account]

def StorageRepresents (records : Account → Token → BalanceRecord Token)
    (state : State Account Token) : Prop :=
  ∀ account token, (records account token).WellFormed token ∧
    (records account token).amount = state.internalBalance account token

/-- Deposit-local record histories. Other Cairo writers must be added before this
can establish validity for arbitrary protocol histories. -/
inductive ReachableRecord (key : Token) : BalanceRecord Token → Prop where
  | empty : ReachableRecord key ⟨0, 0⟩
  | credit (record : BalanceRecord Token) (delta : Int)
      (prior : ReachableRecord key record)
      (bounded : inI128 (record.amount + delta) = true) :
      ReachableRecord key (upsertRecord key record delta)

end Storage

section SourceExecution

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

/-- Coupling to external custody at the *entry* boundary, not a Cairo assertion.
External calls must additionally frame represented storage and normalization metadata
to instantiate this snapshot model from a concrete execution. -/
def ObservationsMatch (state : State Account Token) (input : DirectDepositInput Account Token) : Prop :=
  input.transfer.balanceBefore = state.custodyRaw input.token

end SourceExecution

end Benchmark.Cases.Paraclear.DirectDepositBacking
