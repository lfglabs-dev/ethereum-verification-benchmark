import Mathlib

/-!
# One step-by-step direct-deposit model

runDirectDeposit is the sole deposit executor. It checks observation consistency,
then executeChecks applies each accepted phase's effect in source order.
There is no separate simplified deposit or executable endpoint model.

Reading map (reviewed Cairo operation -> Lean representation):
* Scaling helpers -> toRaw / toInternal / depositCredit. Nat division floors;
  explicit checks impose the source's i128/u256 limits and decimals <= 32 bound.
* deposit / deposit_on_behalf_of -> DepositKind and recipient; caller pays and
  the selected recipient receives credit. Both wrappers invoke the same executor.
* _deposit checks -> sourceChecks, including exact raw receipt after subtraction.
  Dispatches carries success/revert/malformed observations, not executed token calls.
* Account creation and guard writes -> registration, guard and guardExit phase effects.
* ERC20 balanceOf -> TransferObservation; final custody is the observed after-balance,
  NOT a fabricated increment by the expected amount.
* upsert_asset_balance -> upsertAssetBalance's numeric update. upsertRecord describes
  decoded create/update/remove branches; their agreement is proved for valid records.

Entry consistency is a model condition, NOT a Cairo runtime assertion:
balanceBefore must equal the projection's entry custody. An inconsistent input is
reported as observationMatch before executing source phases. This retains the
previous net model's acceptance condition and the detailed proof's former explicit
observation premise. It is not a new business assumption or a source revert claim.

Cairo reads decimals once and reuses that value. The executor captures precision
from the initial state for both conversion and endpoint accounting.
Checks use captured observations and initial balances; external-call interference
and callbacks are excluded. Physical felt decoding, storage hashing/list pointers,
event/return serialization, other protocol transitions and runtime atomicity are
outside this handwritten projection. Registration/event markers do not prove those
operations cannot fail. No Cairo/deployed-code correspondence is asserted.

Specs.lean states the backing rule; Proofs.lean derives the actual successful
executor's checks, receipt and state effects, then proves that rule directly.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

/-! ## Decimal arithmetic -/

def paraclearDecimals : Nat := 8

def i128Min : Int := -(2 ^ 127)
def i128Max : Int := 2 ^ 127 - 1
def i128MaxNat : Nat := 2 ^ 127 - 1
def u256Max : Nat := 2 ^ 256 - 1

def inI128 (value : Int) : Bool :=
  decide (i128Min ≤ value ∧ value ≤ i128Max)

def scaleFactor (tokenDecimals : Nat) : Nat :=
  if tokenDecimals < paraclearDecimals then
    10 ^ (paraclearDecimals - tokenDecimals)
  else
    10 ^ (tokenDecimals - paraclearDecimals)

/-- Cairo `_scale_from_paraclear_decimals` on a validated nonnegative amount. -/
def toRaw (amount8 tokenDecimals : Nat) : Nat :=
  if tokenDecimals = paraclearDecimals then
    amount8
  else if tokenDecimals < paraclearDecimals then
    amount8 / scaleFactor tokenDecimals
  else
    amount8 * scaleFactor tokenDecimals

/-- Cairo `_scale_to_paraclear_decimals` on a nonnegative raw token amount. -/
def toInternal (rawAmount tokenDecimals : Nat) : Nat :=
  if tokenDecimals = paraclearDecimals then
    rawAmount
  else if tokenDecimals < paraclearDecimals then
    rawAmount * scaleFactor tokenDecimals
  else
    rawAmount / scaleFactor tokenDecimals

/-- The actual internal credit: convert to raw token units, then back to 8 decimals. -/
def depositCredit (amount8 tokenDecimals : Nat) : Nat :=
  toInternal (toRaw amount8 tokenDecimals) tokenDecimals

/-! ## 2. Net deposit: accepted inputs and committed accounting changes -/

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

inductive DispatchStatus where
  | returned | reverted | malformed
  deriving Repr, DecidableEq

structure Dispatches where
  pause : DispatchStatus
  decimals : DispatchStatus
  allowance : DispatchStatus
  registry : DispatchStatus
  beforeBalance : DispatchStatus
  transfer : DispatchStatus
  afterBalance : DispatchStatus
  deriving Repr

def Dispatches.completed : Dispatches :=
  ⟨.returned, .returned, .returned, .returned, .returned, .returned, .returned⟩

inductive DepositPhase where
  | observationMatch | guard | recipient | token | pause | registration | globalPause | decimals
  | amountCast | scaling | allowance | support | registryConfigured | registry
  | beforeBalance | transfer | afterBalance | receipt | balanceCast | balanceUpdate
  | event | guardExit
  deriving Repr, DecidableEq

structure DepositCheck where
  phase : DepositPhase
  passes : Bool

structure DirectDepositInput (Account Token : Type) where
  kind : DepositKind
  caller : Account
  requestedRecipient : Account
  token : Token
  amount8 : Nat
  transfer : TransferObservation
  dispatches : Dispatches := .completed
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
  registryConfigured : Bool
  /-- A completed registry dispatch returned restriction code zero. -/
  registryAllows : Account → Account → Nat → Bool
  tokenDecimals : Token → Nat

section Model

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

def DirectDepositInput.recipient (input : DirectDepositInput Account Token) : Account :=
  match input.kind with
  | .self => input.caller
  | .onBehalf => input.requestedRecipient

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

/-! ## Decoded balance records -/

/-- Decoded amount-level storage. Pointers and felt decoding remain outside this type. -/
structure BalanceRecord (Token : Type) where
  tokenAddress : Token
  amount : Int
  deriving Repr, DecidableEq


/-- The source's absent/create, existing/update, and existing/remove amount branches.
The caller has already checked that the signed addition fits i128. -/
def upsertRecord (key : Token) (record : BalanceRecord Token) (delta : Int) :
    BalanceRecord Token :=
  if record.tokenAddress = 0 then
    if delta = 0 then record else ⟨key, delta⟩
  else if record.amount + delta = 0 then
    ⟨0, 0⟩
  else
    ⟨record.tokenAddress, record.amount + delta⟩


def updateRecord (records : Account → Token → BalanceRecord Token)
    (account : Account) (token : Token) (delta : Int) :=
  Function.update records account
    (Function.update (records account) token (upsertRecord token (records account token) delta))

/-! ## Source checks and phase execution -/

/-- Ordered predicates from the reviewed Cairo. Values are captured observations:
`tokenDecimals` is the single saved metadata read, and `transfer` carries returned
ERC20 values. Entry-observation consistency is checked separately by runDirectDeposit.
No callback execution or external world mutation is interpreted here. -/
def sourceChecks (state : State Account Token) (input : DirectDepositInput Account Token)
    : List DepositCheck :=
  let calls := input.dispatches
  let d := state.tokenDecimals input.token
  let raw := toRaw input.amount8 d
  let credit := depositCredit input.amount8 d
  [⟨.guard, !state.reentrancyEntered⟩,
   ⟨.recipient, match input.kind with
     | .self => true | .onBehalf => decide (input.requestedRecipient ≠ 0)⟩,
   ⟨.token, decide (input.token ≠ 0)⟩,
   ⟨.pause, !state.assetsManagerConfigured ||
     (decide (calls.pause = .returned) && !state.tokenDepositsPaused input.token)⟩,
   ⟨.registration, true⟩,
   ⟨.globalPause, state.globalDepositsAllowed⟩,
   ⟨.decimals, decide (calls.decimals = .returned)⟩,
   ⟨.amountCast, decide (input.amount8 ≤ i128MaxNat)⟩,
   ⟨.scaling, decide (d ≤ 32) && decide (raw ≤ i128MaxNat)⟩,
   ⟨.allowance, decide (calls.allowance = .returned) &&
     decide (input.transfer.allowance ≤ u256Max) && decide (input.transfer.allowance ≥ raw)⟩,
   ⟨.support, state.assetSupported input.token⟩,
   ⟨.registryConfigured, state.registryConfigured⟩,
   ⟨.registry, decide (calls.registry = .returned) &&
     state.registryAllows input.caller input.recipient raw⟩,
   ⟨.beforeBalance, decide (calls.beforeBalance = .returned) &&
     decide (input.transfer.balanceBefore ≤ u256Max)⟩,
   ⟨.transfer, decide (calls.transfer = .returned) && input.transfer.transferSucceeded⟩,
   ⟨.afterBalance, decide (calls.afterBalance = .returned) &&
     decide (input.transfer.balanceAfter ≤ u256Max) &&
     decide (input.transfer.balanceBefore ≤ input.transfer.balanceAfter)⟩,
   ⟨.receipt, decide (input.transfer.balanceAfter - input.transfer.balanceBefore = raw)⟩,
   ⟨.balanceCast, inI128 (state.internalBalance input.recipient input.token)⟩,
   ⟨.balanceUpdate, inI128 (state.internalBalance input.recipient input.token + (credit : Int))⟩,
   ⟨.event, true⟩, ⟨.guardExit, true⟩]

/-- Effects on the accounting projection at their source phases. The external token
world is not executed: final custody is installed at the successful after-read.
The captured precision must be supplied from entry, not read again during execution. -/
def phaseEffect (input : DirectDepositInput Account Token) (capturedDecimals : Nat)
    (phase : DepositPhase) (state : State Account Token) : State Account Token :=
  match phase with
  | .guard => { state with reentrancyEntered := true }
  | .registration => { state with registeredAccounts := insert input.recipient state.registeredAccounts }
  | .afterBalance => { state with custodyRaw := Function.update state.custodyRaw input.token input.transfer.balanceAfter }
  | .balanceUpdate => upsertAssetBalance state input.recipient input.token
      (depositCredit input.amount8 capturedDecimals : Int)
  | .guardExit => { state with reentrancyEntered := false }
  | _ => state

/-- Executes source phases in order, including tentative guard/registration writes.
Predicates use captured observations under the documented noninterference boundary.
Failed runs expose the first failing phase and no committed post-state. -/
def executeChecks (input : DirectDepositInput Account Token) (capturedDecimals : Nat) :
    List DepositCheck → State Account Token → Except DepositPhase (State Account Token)
  | [], state => .ok state
  | check :: rest, state =>
      if check.passes then
        executeChecks input capturedDecimals rest (phaseEffect input capturedDecimals check.phase state)
      else .error check.phase

/-- The only deposit model. Invalid entry observations are distinguished from
source-phase rejection; no committed post-state is returned in either case. -/
def runDirectDeposit (state : State Account Token) (input : DirectDepositInput Account Token) :
    Except DepositPhase (State Account Token) :=
  if input.transfer.balanceBefore = state.custodyRaw input.token then
    executeChecks input (state.tokenDecimals input.token) (sourceChecks state input) state
  else
    .error .observationMatch

/-- Source-shaped self-deposit wrapper; no independent transition implementation. -/
def deposit (state : State Account Token) (caller : Account) (token : Token)
    (amount8 : Nat) (transfer : TransferObservation) (dispatches : Dispatches := .completed) :
    Except DepositPhase (State Account Token) :=
  runDirectDeposit state {
    kind := .self, caller := caller, requestedRecipient := caller,
    token := token, amount8 := amount8, transfer := transfer, dispatches := dispatches }

/-- Source-shaped on-behalf wrapper; caller pays and recipient receives the credit. -/
def depositOnBehalfOf (state : State Account Token) (caller recipient : Account) (token : Token)
    (amount8 : Nat) (transfer : TransferObservation) (dispatches : Dispatches := .completed) :
    Except DepositPhase (State Account Token) :=
  runDirectDeposit state {
    kind := .onBehalf, caller := caller, requestedRecipient := recipient,
    token := token, amount8 := amount8, transfer := transfer, dispatches := dispatches }

/-- Accounting projection committed by the model. On rejection, use the input
projection; this wrapper does not prove Starknet world rollback. -/
def committedDepositState (state : State Account Token) (input : DirectDepositInput Account Token) :
    State Account Token :=
  match runDirectDeposit state input with
  | .ok state' => state'
  | .error _ => state

end Model

end Benchmark.Cases.Paraclear.DirectDepositBacking
