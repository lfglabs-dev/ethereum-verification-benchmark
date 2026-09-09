import Benchmark.Cases.Paraclear.DirectDepositBacking.SourceExecution

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

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

theorem executeChecks_eq (input : DirectDepositInput Account Token) (d : Nat)
    (checks : List DepositCheck) (state : State Account Token) :
    executeChecks input d checks state =
      match firstFailure checks with
      | some phase => .error phase
      | none => .ok (uncheckedEffects input d checks state) := by
  induction checks generalizing state with
  | nil => rfl
  | cons check rest ih =>
    cases h : check.passes <;>
      simp [executeChecks, firstFailure, h, ih, uncheckedEffects, List.foldl_cons]

theorem sourceEffects_eq_postState (state : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches) :
    uncheckedEffects input (state.tokenDecimals input.token) (sourceChecks state input calls) state =
      sourcePostState state input := by
  simp [uncheckedEffects, sourceChecks, phaseEffect, sourcePostState, upsertAssetBalance]

def runOrderedDeposit (state : State Account Token) (input : DirectDepositInput Account Token)
    (calls : Dispatches) : Except DepositPhase (State Account Token) :=
  executeChecks input (state.tokenDecimals input.token) (sourceChecks state input calls) state

/-- Exact equivalence of ordered projection execution and the source-shaped endpoint
model, including rejection phase. This is still a Lean-to-Lean equivalence. -/
theorem ordered_eq_source (state : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches) :
    runOrderedDeposit state input calls = runSourceDeposit state input calls := by
  unfold runOrderedDeposit runSourceDeposit
  rw [executeChecks_eq]
  cases firstFailure (sourceChecks state input calls) <;>
    simp [sourceEffects_eq_postState]

theorem ordered_success_refines (state state' : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches)
    (coupled : ObservationsMatch state input)
    (success : runOrderedDeposit state input calls = .ok state') :
    runDirectDeposit state input = some state' := by
  rw [ordered_eq_source] at success
  exact source_success_refines state state' input calls coupled success

/-- Composes ordered execution with the existence-aware record update theorem.
This relates decoded amount records, not physical Cairo storage or its pointers. -/
theorem ordered_success_storage_represents (state state' : State Account Token)
    (records : Account → Token → BalanceRecord Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches)
    (rep : StorageRepresents records state) (coupled : ObservationsMatch state input)
    (success : runOrderedDeposit state input calls = .ok state') :
    StorageRepresents
      (updateRecord records input.recipient input.token
        (depositCredit input.amount8 (state.tokenDecimals input.token) : Int)) state' := by
  have net := ordered_success_refines state state' input calls coupled success
  have checks : (publicDepositChecks state input && internalDepositChecks state input) = true := by
    unfold runDirectDeposit at net
    split at net
    · assumption
    · contradiction
  have token_ne : input.token ≠ 0 := by
    have h := checks
    simp only [Bool.and_eq_true, publicDepositChecks, decide_eq_true_eq] at h
    tauto
  have bounded : inI128 (state.internalBalance input.recipient input.token +
      (depositCredit input.amount8 (state.tokenDecimals input.token) : Int)) = true := by
    have h := checks
    simp only [Bool.and_eq_true, internalDepositChecks, decide_eq_true_eq] at h
    tauto
  rw [successful_run_eq_apply state state' input net]
  change StorageRepresents _ (upsertAssetBalance state input.recipient input.token
    (depositCredit input.amount8 (state.tokenDecimals input.token) : Int))
  exact updateRecord_represents records state input.recipient input.token _ rep token_ne bounded

variable [Fintype Account]

theorem ordered_success_preservesBackingSlack (state state' : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches)
    (coupled : ObservationsMatch state input)
    (success : runOrderedDeposit state input calls = .ok state') :
    backingSlack state' input.token ≥ backingSlack state input.token :=
  directDeposit_preservesBackingSlack state state' input
    (ordered_success_refines state state' input calls coupled success)

end Benchmark.Cases.Paraclear.DirectDepositBacking
