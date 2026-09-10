import Mathlib

/-!
# Reading this model alongside Cairo

This file is a handwritten accounting projection, not translated Cairo and not a
Cairo/Sierra/CASM interpreter. Names refer to the reviewed private implementation;
no source code is reproduced here. Specs.lean states the mathematical relations,
and Proofs.lean proves them. Both net and ordered models below are Lean models.

Reading map (Cairo operation -> Lean representation):
* Decimal scaling helpers -> toRaw, toInternal, depositCredit. Nat division floors.
  Nat/Int are mathematical integers; explicit checks impose i128/u256 bounds.
* Public deposit / deposit_on_behalf_of -> DepositKind, recipient, publicDepositChecks.
  Caller pays; the selected recipient receives the internal credit.
* Account registration -> registeredAccounts set insertion, not account storage layout.
* Internal _deposit -> internalDepositChecks (net acceptance) and sourceChecks
  (ordered acceptance with dispatcher status and first rejected phase).
* ERC20 allowance/transfer/balanceOf -> supplied TransferObservation and Dispatches,
  not calls executed against a token. custodyRaw is external custody in the projection,
  not an extra Cairo storage field.
* upsert_asset_balance -> upsertRecord's absent/create/update/remove branches.
  upsertAssetBalance is its simpler numeric effect, justified only for valid records.
* Guard, registration, receipt and credit writes -> phaseEffect / executeChecks.
  runSourceDeposit computes an endpoint; runOrderedDeposit executes phase effects.
  Their equivalence is proved, not assumed, in Proofs.lean.

Runtime checks versus assumptions:
The source checks addresses, pauses, range/scaling limits, allowance, support,
registry configuration/permission, transfer success and exact received amount.
The net model additionally checks entry custody = before observation: this is an
environment coupling condition (ObservationsMatch in Specs), NOT a Cairo assertion.
Record decoding/validity, completeness of the account domain, and noninterference
of external calls must be established separately for a concrete execution.
Cairo captures decimals once and reuses it; the model fixes endpoint normalization
to that precision. It does not assert lifetime immutability of token metadata.
The decimals <= 32 limit models the scaling helper's runtime exponent bound.

What is omitted:
Physical felt decoding, storage hashing and linked-list pointers; callback traces;
event payload and returned felt serialization; resource failure and runtime internals.
Event/registration markers that pass unconditionally are not proofs those operations
cannot fail. Failed execution returns no committed state; rollback of the real
Starknet world remains trusted. The guard is not a proof of whole-ABI noninterference.
Withdrawals, bridge deposits, settlement, fees, liquidation and other balance writers
are outside this local deposit proof. No deployed-code correspondence is claimed.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

/-! ## 1. Decimal arithmetic corresponding to the scaling helpers -/

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
    state.registryConfigured &&
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

/-! ## 3. Decoded records corresponding to upsert_asset_balance -/

section Storage

/-- Decoded amount-level storage. Pointers and felt decoding remain outside this type. -/
structure BalanceRecord (Token : Type) where
  tokenAddress : Token
  amount : Int
  deriving Repr, DecidableEq

variable {Account Token : Type} [DecidableEq Token] [Zero Token]

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

variable [DecidableEq Account]

def updateRecord (records : Account → Token → BalanceRecord Token)
    (account : Account) (token : Token) (delta : Int) :=
  Function.update records account
    (Function.update (records account) token (upsertRecord token (records account token) delta))

end Storage

/-! ## 4. Ordered Cairo-shaped checks and observed endpoint -/

section SourceExecution

/-- Dispatch failure and malformed return data both reject, but remain distinguishable. -/
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
  | guard | recipient | token | pause | registration | globalPause | decimals
  | amountCast | scaling | allowance | support | registryConfigured | registry
  | beforeBalance | transfer | afterBalance | receipt | balanceCast | balanceUpdate
  | event | guardExit
  deriving Repr, DecidableEq

structure DepositCheck where
  phase : DepositPhase
  passes : Bool

/-- Stops at the first rejected phase; this is not a VM call trace. -/
def firstFailure : List DepositCheck → Option DepositPhase
  | [] => none
  | check :: rest => if check.passes then firstFailure rest else some check.phase

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

/-- Ordered predicates from the reviewed Cairo. Values are captured observations:
`tokenDecimals` is the single saved metadata read, and `transfer` carries returned
ERC20 values. ObservationsMatch in Specs is separate from source runtime checks.
No callback execution or external world mutation is interpreted here. -/
def sourceChecks (state : State Account Token) (input : DirectDepositInput Account Token)
    (calls : Dispatches) : List DepositCheck :=
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

/-- Independent endpoint construction using the observed final ERC20 balance.
Account registration occurs earlier in Cairo; only its committed membership effect
is represented here. Failure location is exposed by runSourceDeposit; event payloads
and return serialization are not represented. -/
def sourcePostState (state : State Account Token) (input : DirectDepositInput Account Token) :
    State Account Token :=
  { state with
    internalBalance := updateInternalBalance state.internalBalance input.recipient input.token
      (state.internalBalance input.recipient input.token +
        (depositCredit input.amount8 (state.tokenDecimals input.token) : Int))
    custodyRaw := Function.update state.custodyRaw input.token input.transfer.balanceAfter
    registeredAccounts := insert input.recipient state.registeredAccounts
    reentrancyEntered := false }

def runSourceDeposit (state : State Account Token) (input : DirectDepositInput Account Token)
    (calls : Dispatches) : Except DepositPhase (State Account Token) :=
  match firstFailure (sourceChecks state input calls) with
  | some phase => .error phase
  | none => .ok (sourcePostState state input)

/-- Rollback wrapper for this accounting projection; runtime atomicity is still trusted. -/
def committedSourceState (state : State Account Token) (input : DirectDepositInput Account Token)
    (calls : Dispatches) : State Account Token :=
  match runSourceDeposit state input calls with
  | .ok state' => state'
  | .error _ => state

end SourceExecution

/-! ## 5. Step-by-step execution of the modeled phase effects -/

section Execution

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

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

def uncheckedEffects (input : DirectDepositInput Account Token) (capturedDecimals : Nat)
    (checks : List DepositCheck) (state : State Account Token) : State Account Token :=
  checks.foldl (fun s check => phaseEffect input capturedDecimals check.phase s) state

def runOrderedDeposit (state : State Account Token) (input : DirectDepositInput Account Token)
    (calls : Dispatches) : Except DepositPhase (State Account Token) :=
  executeChecks input (state.tokenDecimals input.token) (sourceChecks state input calls) state

end Execution

end Benchmark.Cases.Paraclear.DirectDepositBacking
