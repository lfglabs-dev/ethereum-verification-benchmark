import Benchmark.Cases.Paraclear.DirectDepositBacking.CairoInt

/-!
# Source-aligned Paraclear direct-deposit model

This is a hand-written Lean model of the net state transition performed by the public
`deposit` and `deposit_on_behalf_of` entrypoints. It is not generated from Cairo or
Sierra.

Documented abstraction boundaries:

* Starknet contract addresses and token addresses are abstract identity types with
  `Zero` and `DecidableEq`; only the aggregate-balance specification later requires
  `Fintype Account`.
* ERC20 calls are explicit observations supplied in `TransferObservation`. The model
  checks the same allowance, return value, and before/after balance relationship as the
  Cairo source, but does not prove ERC20 implementation behavior.
* Token metadata is stable across the modeled transition: `decimals()` is represented
  by one unchanged `tokenDecimals` state value.
* Every external dispatcher call (Assets Manager, registry, and ERC20 metadata,
  allowance, balance, and transfer calls) is an atomic observation. Callback traces
  into other Paraclear entrypoints are outside this POC.
* The linked-list pointers used by `upsert_asset_balance` are omitted. The modeled
  balance map has the same observable amount behavior, including a zero delta leaving
  a zero balance unchanged.
* The reentrancy guard is modeled with explicit enter/exit state updates around the
  successful deposit body. Reversion is represented by `none`. No external token
  state is returned on failure;
  this does not independently prove Starknet transaction atomicity.
* `decimals ≤ 32` is restated in the deposit checks as a supported-asset state
  invariant. The Cairo contract enforces it when a supported token is created or
  updated, rather than rechecking it inside `_deposit`.
* `assetsManagerConfigured` makes the Cairo no-op pause branch explicit: per-token
  pause is enforced only when an Assets Manager is configured.
* Events and the returned felt balance are omitted because they do not affect backing.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

inductive DepositKind where
  | self
  | onBehalf
  deriving Repr, DecidableEq

structure TransferObservation where
  allowance : Nat
  transferSucceeded : Bool
  balanceBefore : Nat
  balanceAfter : Nat
  deriving Repr, DecidableEq

structure DirectDepositInput (Account Token : Type) where
  kind : DepositKind
  caller : Account
  requestedRecipient : Account
  token : Token
  amount8 : Nat
  transfer : TransferObservation
  deriving Repr

structure State (Account Token : Type) where
  internalBalance : Account → Token → Int
  custodyRaw : Token → Nat
  registeredAccounts : Finset Account
  reentrancyEntered : Bool
  globalDepositsAllowed : Bool
  assetsManagerConfigured : Bool
  tokenDepositsPaused : Token → Bool
  assetSupported : Token → Bool
  registryAllows : Account → Account → Nat → Bool
  tokenDecimals : Token → Nat

section Model

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

def DirectDepositInput.recipient (input : DirectDepositInput Account Token) : Account :=
  match input.kind with
  | .self => input.caller
  | .onBehalf => input.requestedRecipient

def publicDepositChecks
    (state : State Account Token) (input : DirectDepositInput Account Token) : Bool :=
  !state.reentrancyEntered &&
    decide (input.token ≠ 0) &&
    (!state.assetsManagerConfigured || !state.tokenDepositsPaused input.token) &&
    match input.kind with
    | .self => true
    | .onBehalf => decide (input.requestedRecipient ≠ 0)

def internalDepositChecks
    (state : State Account Token) (input : DirectDepositInput Account Token) : Bool :=
  let recipient := input.recipient
  let decimals := state.tokenDecimals input.token
  let rawAmount := toRaw input.amount8 decimals
  let credit := depositCredit input.amount8 decimals
  let oldBalance := state.internalBalance recipient input.token
  state.globalDepositsAllowed &&
    state.assetSupported input.token &&
    decide (decimals ≤ 32) &&
    decide (input.amount8 ≤ i128MaxNat) &&
    decide (rawAmount ≤ i128MaxNat) &&
    inI128 oldBalance &&
    inI128 (oldBalance + (credit : Int)) &&
    decide (input.transfer.allowance ≤ u256Max) &&
    decide (input.transfer.allowance ≥ rawAmount) &&
    state.registryAllows input.caller recipient rawAmount &&
    input.transfer.transferSucceeded &&
    decide (input.transfer.balanceBefore = state.custodyRaw input.token) &&
    decide (input.transfer.balanceAfter = input.transfer.balanceBefore + rawAmount) &&
    decide (input.transfer.balanceAfter ≤ u256Max)

def updateInternalBalance
    (balances : Account → Token → Int)
    (account : Account)
    (token : Token)
    (value : Int) : Account → Token → Int :=
  Function.update balances account (Function.update (balances account) token value)

def upsertAssetBalance
    (state : State Account Token)
    (account : Account)
    (token : Token)
    (delta : Int) : State Account Token :=
  { state with
    internalBalance := updateInternalBalance state.internalBalance account token
      (state.internalBalance account token + delta) }

/-- Enter the public entrypoint's reentrancy guard before any external call. -/
def enterReentrancyGuard (state : State Account Token) : State Account Token :=
  { state with reentrancyEntered := true }

/-- Exit the public entrypoint's reentrancy guard after the deposit body succeeds. -/
def exitReentrancyGuard (state : State Account Token) : State Account Token :=
  { state with reentrancyEntered := false }

def applySuccessfulDirectDeposit
    (state : State Account Token) (input : DirectDepositInput Account Token) :
    State Account Token :=
  let guarded := enterReentrancyGuard state
  let recipient := input.recipient
  let decimals := guarded.tokenDecimals input.token
  let rawAmount := toRaw input.amount8 decimals
  let credit := depositCredit input.amount8 decimals
  let credited := upsertAssetBalance guarded recipient input.token (credit : Int)
  exitReentrancyGuard {
    credited with
    custodyRaw := Function.update guarded.custodyRaw input.token
      (guarded.custodyRaw input.token + rawAmount)
    registeredAccounts := insert recipient guarded.registeredAccounts }

/-- Unified model of both public direct-deposit entrypoints. -/
def runDirectDeposit
    (state : State Account Token) (input : DirectDepositInput Account Token) :
    Option (State Account Token) :=
  if publicDepositChecks state input && internalDepositChecks state input then
    some (applySuccessfulDirectDeposit state input)
  else
    none

/-- Source-shaped wrapper for `deposit`. -/
def deposit
    (state : State Account Token)
    (caller : Account)
    (token : Token)
    (amount8 : Nat)
    (transfer : TransferObservation) : Option (State Account Token) :=
  runDirectDeposit state {
    kind := .self
    caller := caller
    requestedRecipient := caller
    token := token
    amount8 := amount8
    transfer := transfer
  }

/-- Source-shaped wrapper for `deposit_on_behalf_of`. -/
def depositOnBehalfOf
    (state : State Account Token)
    (caller recipient : Account)
    (token : Token)
    (amount8 : Nat)
    (transfer : TransferObservation) : Option (State Account Token) :=
  runDirectDeposit state {
    kind := .onBehalf
    caller := caller
    requestedRecipient := recipient
    token := token
    amount8 := amount8
    transfer := transfer
  }

end Model

end Benchmark.Cases.Paraclear.DirectDepositBacking
