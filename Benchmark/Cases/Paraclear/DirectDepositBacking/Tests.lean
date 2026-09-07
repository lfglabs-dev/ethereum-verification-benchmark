import Benchmark.Cases.Paraclear.DirectDepositBacking.Proofs

namespace Benchmark.Cases.Paraclear.DirectDepositBacking.Tests

open Benchmark.Cases.Paraclear.DirectDepositBacking

abbrev Account := Fin 4
abbrev Token := Fin 4

def baseState : State Account Token := {
  internalBalance := fun _ _ => 0
  custodyRaw := fun _ => 1_000_000_000
  registeredAccounts := ∅
  reentrancyEntered := false
  globalDepositsAllowed := true
  assetsManagerConfigured := true
  tokenDepositsPaused := fun _ => false
  assetSupported := fun _ => true
  registryAllows := fun _ _ _ => true
  tokenDecimals := fun _ => 8
}

def exactTransfer (before raw : Nat) : TransferObservation := {
  allowance := raw
  transferSucceeded := true
  balanceBefore := before
  balanceAfter := before + raw
}

def selfInput (amount : Nat) : DirectDepositInput Account Token := {
  kind := .self
  caller := 1
  requestedRecipient := 1
  token := 1
  amount8 := amount
  transfer := exactTransfer 1_000_000_000 amount
}

example : toRaw 123_456_789 0 = 1 := by native_decide
example : depositCredit 123_456_789 0 = 100_000_000 := by native_decide
example : toRaw 123_456_789 7 = 12_345_678 := by native_decide
example : depositCredit 123_456_789 7 = 123_456_780 := by native_decide
example : depositCredit 123_456_789 8 = 123_456_789 := by native_decide
example : depositCredit 123_456_789 9 = 123_456_789 := by native_decide
example : depositCredit 123_456_789 18 = 123_456_789 := by native_decide
example : depositCredit 123_456_789 24 = 123_456_789 := by native_decide
example : depositCredit 123_456_789 32 = 123_456_789 := by native_decide

def stateAtDecimals (decimals : Nat) : State Account Token :=
  { baseState with
    tokenDecimals := fun token => if token = 1 then decimals else 8 }

def inputAtDecimals (decimals amount : Nat) : DirectDepositInput Account Token :=
  let raw := toRaw amount decimals
  { kind := .self
    caller := 1
    requestedRecipient := 1
    token := 1
    amount8 := amount
    transfer := exactTransfer 1_000_000_000 raw }

example :
    (runDirectDeposit (stateAtDecimals 0) (inputAtDecimals 0 123_456_789)).isSome = true := by
  native_decide
example :
    (runDirectDeposit (stateAtDecimals 7) (inputAtDecimals 7 123_456_789)).isSome = true := by
  native_decide
example :
    (runDirectDeposit (stateAtDecimals 8) (inputAtDecimals 8 123_456_789)).isSome = true := by
  native_decide
example :
    (runDirectDeposit (stateAtDecimals 9) (inputAtDecimals 9 123_456_789)).isSome = true := by
  native_decide
example :
    (runDirectDeposit (stateAtDecimals 18) (inputAtDecimals 18 123_456_789)).isSome = true := by
  native_decide
example :
    (runDirectDeposit (stateAtDecimals 24) (inputAtDecimals 24 123_456_789)).isSome = true := by
  native_decide
example :
    (runDirectDeposit (stateAtDecimals 32) (inputAtDecimals 32 123_456_789)).isSome = true := by
  native_decide

example : (runDirectDeposit baseState (selfInput 0)).isSome = true := by native_decide

example :
    ((runDirectDeposit (stateAtDecimals 0) (inputAtDecimals 0 99_999_999)).map
      (fun state => state.internalBalance 1 1)) = some 0 := by
  native_decide

example :
    (deposit baseState 1 1 200 (exactTransfer 1_000_000_000 200)).isSome = true := by
  native_decide

example :
    let input := selfInput 200
    let state' := applySuccessfulDirectDeposit baseState input
    backingSlack state' input.token ≥ backingSlack baseState input.token := by
  apply directDeposit_preservesBackingSlack
  have public_ok : publicDepositChecks baseState (selfInput 200) = true := by
    native_decide
  have internal_ok : internalDepositChecks baseState (selfInput 200) = true := by
    native_decide
  simp [runDirectDeposit, public_ok, internal_ok]

def negativeState : State Account Token :=
  { baseState with
    internalBalance := fun account token =>
      if account = 1 ∧ token = 1 then -500 else 0 }

example :
    ((runDirectDeposit negativeState (selfInput 200)).map
      (fun state => state.internalBalance 1 1)) = some (-300) := by
  native_decide

def positiveState : State Account Token :=
  { baseState with
    internalBalance := fun account token =>
      if account = 1 ∧ token = 1 then 500 else 0 }

example :
    ((runDirectDeposit positiveState (selfInput 200)).map
      (fun state => state.internalBalance 1 1)) = some 700 := by
  native_decide

def onBehalfInput : DirectDepositInput Account Token := {
  kind := .onBehalf
  caller := 1
  requestedRecipient := 2
  token := 1
  amount8 := 200
  transfer := exactTransfer 1_000_000_000 200
}

example :
    ((runDirectDeposit baseState onBehalfInput).map
      (fun state => state.internalBalance 2 1)) = some 200 := by
  native_decide

example :
    (depositOnBehalfOf baseState 1 2 1 200
      (exactTransfer 1_000_000_000 200)).isSome = true := by
  native_decide

example :
    let input := onBehalfInput
    let state' := applySuccessfulDirectDeposit baseState input
    backingSlack state' input.token ≥ backingSlack baseState input.token := by
  apply directDeposit_preservesBackingSlack
  have public_ok : publicDepositChecks baseState onBehalfInput = true := by
    native_decide
  have internal_ok : internalDepositChecks baseState onBehalfInput = true := by
    native_decide
  simp [runDirectDeposit, public_ok, internal_ok]

example :
    ((runDirectDeposit baseState onBehalfInput).map
      (fun state => decide (2 ∈ state.registeredAccounts))) = some true := by
  native_decide

example :
    (runDirectDeposit baseState (selfInput i128MaxNat)).isSome = true := by
  native_decide

example : runDirectDeposit baseState (selfInput (i128MaxNat + 1)) = none := by
  native_decide

example :
    runDirectDeposit (stateAtDecimals 32) (inputAtDecimals 32 i128MaxNat) = none := by
  native_decide

example : runDirectDeposit (stateAtDecimals 33) (inputAtDecimals 33 1) = none := by
  native_decide

def withTransfer (input : DirectDepositInput Account Token)
    (transfer : TransferObservation) : DirectDepositInput Account Token :=
  { input with transfer := transfer }

example : runDirectDeposit baseState
    (withTransfer (selfInput 200) {
      allowance := 199
      transferSucceeded := true
      balanceBefore := 1_000_000_000
      balanceAfter := 1_000_000_200
    }) = none := by native_decide

example : runDirectDeposit baseState
    (withTransfer (selfInput 200) {
      allowance := 200
      transferSucceeded := false
      balanceBefore := 1_000_000_000
      balanceAfter := 1_000_000_200
    }) = none := by native_decide

example : runDirectDeposit baseState
    (withTransfer (selfInput 200) {
      allowance := 200
      transferSucceeded := true
      balanceBefore := 1_000_000_000
      balanceAfter := 1_000_000_199
    }) = none := by native_decide

example : runDirectDeposit baseState
    (withTransfer (selfInput 200) {
      allowance := 200
      transferSucceeded := true
      balanceBefore := 1_000_000_000
      balanceAfter := 1_000_000_201
    }) = none := by native_decide

def pausedState : State Account Token :=
  { baseState with tokenDepositsPaused := fun token => token = 1 }

example : runDirectDeposit pausedState (selfInput 200) = none := by native_decide

def noAssetsManagerState : State Account Token :=
  { pausedState with assetsManagerConfigured := false }

example : (runDirectDeposit noAssetsManagerState (selfInput 200)).isSome = true := by
  native_decide

def unsupportedState : State Account Token :=
  { baseState with assetSupported := fun token => token ≠ 1 }

example : runDirectDeposit unsupportedState (selfInput 200) = none := by native_decide

def registryRejectedState : State Account Token :=
  { baseState with registryAllows := fun _ _ _ => false }

example : runDirectDeposit registryRejectedState (selfInput 200) = none := by native_decide

def enteredState : State Account Token :=
  { baseState with reentrancyEntered := true }

example : runDirectDeposit enteredState (selfInput 200) = none := by native_decide

example :
    ((runDirectDeposit baseState (selfInput 200)).map
      (fun state => state.reentrancyEntered)) = some false := by
  native_decide

example : runDirectDeposit baseState
    (withTransfer (selfInput 200) {
      allowance := u256Max + 1
      transferSucceeded := true
      balanceBefore := 1_000_000_000
      balanceAfter := 1_000_000_200
    }) = none := by native_decide

def nearU256CustodyState : State Account Token :=
  { baseState with
    custodyRaw := fun token => if token = 1 then u256Max else 1_000_000_000 }

example : runDirectDeposit nearU256CustodyState
    (withTransfer (selfInput 1) {
      allowance := 1
      transferSucceeded := true
      balanceBefore := u256Max
      balanceAfter := u256Max + 1
    }) = none := by native_decide

def globallyPausedState : State Account Token :=
  { baseState with globalDepositsAllowed := false }

example : runDirectDeposit globallyPausedState (selfInput 200) = none := by native_decide

def zeroTokenInput : DirectDepositInput Account Token :=
  { selfInput 200 with token := 0 }

example : runDirectDeposit baseState zeroTokenInput = none := by native_decide

def zeroRecipientInput : DirectDepositInput Account Token :=
  { onBehalfInput with requestedRecipient := 0 }

example : runDirectDeposit baseState zeroRecipientInput = none := by native_decide

example : runDirectDeposit baseState
    (withTransfer (selfInput 200) {
      allowance := 200
      transferSucceeded := true
      balanceBefore := 999_999_999
      balanceAfter := 1_000_000_199
    }) = none := by native_decide

def unrelatedState : State Account Token :=
  { baseState with
    internalBalance := fun account token =>
      if account = 3 ∧ token = 2 then 777 else 0 }

example :
    ((runDirectDeposit unrelatedState (selfInput 200)).map
      (fun state => state.internalBalance 3 2)) = some 777 := by
  native_decide

example (state : State Account Token) (input : DirectDepositInput Account Token)
    (account : Account) (token : Token)
    (unrelated : account ≠ input.recipient ∨ token ≠ input.token) :
    (applySuccessfulDirectDeposit state input).internalBalance account token =
      state.internalBalance account token :=
  unrelatedBalance_after_successful_apply state input account token unrelated

example (state state' : State Account Token)
    (success : runDirectDeposit state (selfInput 200) = some state') :
    backingSlack state' 1 ≥ backingSlack state 1 :=
  directDeposit_preservesBackingSlack state state' (selfInput 200) success

end Benchmark.Cases.Paraclear.DirectDepositBacking.Tests
