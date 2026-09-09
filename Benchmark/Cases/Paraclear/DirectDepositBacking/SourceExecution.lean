import Benchmark.Cases.Paraclear.DirectDepositBacking.Proofs
import Benchmark.Cases.Paraclear.DirectDepositBacking.Storage

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

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

theorem firstFailure_none_iff (checks : List DepositCheck) :
    firstFailure checks = none ↔ ∀ check ∈ checks, check.passes = true := by
  induction checks with
  | nil => simp [firstFailure]
  | cons check rest ih =>
    cases h : check.passes <;> simp [firstFailure, h, ih]

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

/-- Ordered predicates from the reviewed Cairo. Values are captured observations:
`tokenDecimals` is the single saved metadata read, and `transfer` carries returned
ERC20 values. The environment relation below is separate from source runtime checks.
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

/-- Coupling to external custody at the *entry* boundary, not a Cairo assertion.
External calls must additionally frame represented storage and normalization metadata
to instantiate this snapshot model from a concrete execution. -/
def ObservationsMatch (state : State Account Token) (input : DirectDepositInput Account Token) : Prop :=
  input.transfer.balanceBefore = state.custodyRaw input.token

/-- Independent endpoint construction using the observed final ERC20 balance.
Account registration occurs earlier in Cairo; only its committed membership effect
is represented here. Events, return value, and failure location are exposed separately. -/
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

theorem sourceChecks_imply_modelChecks (state : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches)
    (accepted : firstFailure (sourceChecks state input calls) = none)
    (coupled : ObservationsMatch state input) :
    (publicDepositChecks state input && internalDepositChecks state input) = true := by
  rw [firstFailure_none_iff] at accepted
  simp only [sourceChecks, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, Bool.and_eq_true, decide_eq_true_eq] at accepted
  simp only [publicDepositChecks, internalDepositChecks, Bool.and_eq_true,
    decide_eq_true_eq]
  have receipt : input.transfer.balanceAfter = input.transfer.balanceBefore +
      toRaw input.amount8 (state.tokenDecimals input.token) := by omega
  have pause : (!state.assetsManagerConfigured || !state.tokenDepositsPaused input.token) = true := by
    have hp := accepted.2.2.2.1
    cases h : state.assetsManagerConfigured <;> simp_all
  change input.transfer.balanceBefore = state.custodyRaw input.token at coupled
  tauto

theorem sourcePostState_eq_apply (state : State Account Token)
    (input : DirectDepositInput Account Token)
    (receipt : input.transfer.balanceAfter = state.custodyRaw input.token +
      toRaw input.amount8 (state.tokenDecimals input.token)) :
    sourcePostState state input = applySuccessfulDirectDeposit state input := by
  simp [sourcePostState, applySuccessfulDirectDeposit, enterReentrancyGuard,
    exitReentrancyGuard, upsertAssetBalance, receipt]

/-- Refinement between two handwritten Lean models, NOT a Cairo semantics theorem. -/
theorem source_success_refines (state state' : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches)
    (coupled : ObservationsMatch state input)
    (success : runSourceDeposit state input calls = .ok state') :
    runDirectDeposit state input = some state' := by
  unfold runSourceDeposit at success
  cases h : firstFailure (sourceChecks state input calls) with
  | some phase => simp [h] at success
  | none =>
    simp only [h, Except.ok.injEq] at success
    subst state'
    have checks := sourceChecks_imply_modelChecks state input calls h coupled
    have receipt : input.transfer.balanceAfter = state.custodyRaw input.token +
        toRaw input.amount8 (state.tokenDecimals input.token) := by
      have hc := checks
      simp only [Bool.and_eq_true, internalDepositChecks, decide_eq_true_eq] at hc
      change input.transfer.balanceBefore = state.custodyRaw input.token at coupled
      omega
    simp [runDirectDeposit, checks, sourcePostState_eq_apply state input receipt]

/-- Rollback wrapper for this accounting projection; runtime atomicity is still trusted. -/
def committedSourceState (state : State Account Token) (input : DirectDepositInput Account Token)
    (calls : Dispatches) : State Account Token :=
  match runSourceDeposit state input calls with
  | .ok state' => state'
  | .error _ => state

theorem rejected_source_preserves_projection (state : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches) (phase : DepositPhase)
    (failed : runSourceDeposit state input calls = .error phase) :
    committedSourceState state input calls = state := by
  simp [committedSourceState, failed]

variable [Fintype Account]

theorem source_success_preservesBackingSlack (state state' : State Account Token)
    (input : DirectDepositInput Account Token) (calls : Dispatches)
    (coupled : ObservationsMatch state input)
    (success : runSourceDeposit state input calls = .ok state') :
    backingSlack state' input.token ≥ backingSlack state input.token :=
  directDeposit_preservesBackingSlack state state' input
    (source_success_refines state state' input calls coupled success)

end Benchmark.Cases.Paraclear.DirectDepositBacking
