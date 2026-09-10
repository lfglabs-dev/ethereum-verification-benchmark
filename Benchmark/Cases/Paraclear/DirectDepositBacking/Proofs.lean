import Benchmark.Cases.Paraclear.DirectDepositBacking.Specs

/-!
# Proof guide: which connection is proved?

1. Arithmetic: a deposit-shaped custody increment normalizes to exactly the credit;
   adding that credit to a signed balance increases its positive part by at most
   the credit. Subtracting the two proves directDeposit_preservesBackingSlack.
2. Storage: the source-shaped create/update/remove record branches have the same
   numeric effect as addition, provided the decoded record is well formed. Local
   update histories preserve this validity; arbitrary Cairo histories are not proved.
3. SourceExecution: ordered predicates and observed final custody refine the net
   deposit under ObservationsMatch. This assumption is not a source runtime check.
4. Execution: applying the modeled phase effects gives the source-shaped endpoint,
   including the same first rejection. Composing these results transfers the backing
   property and decoded-record relation to the ordered Lean execution.

All four are Lean-to-Lean results. The missing implementation theorem would connect
an actual Cairo execution and its external calls to these observations and records.
Callbacks, physical storage/ABI decoding, and runtime atomicity are not proved here.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

section Accounting

/-- A deposit-sized raw increment normalizes additively at every token precision. -/
theorem toInternal_add_toRaw
    (custodyRaw amount8 tokenDecimals : Nat) :
    toInternal (custodyRaw + toRaw amount8 tokenDecimals) tokenDecimals =
      toInternal custodyRaw tokenDecimals + depositCredit amount8 tokenDecimals := by
  by_cases heq : tokenDecimals = paraclearDecimals
  · simp [toInternal, toRaw, depositCredit, heq]
  · by_cases hlt : tokenDecimals < paraclearDecimals
    · simp [toInternal, toRaw, depositCredit, heq, hlt, Nat.add_mul]
    · have hgt : paraclearDecimals < tokenDecimals := by omega
      have hpos : 0 < scaleFactor tokenDecimals := by
        simp [scaleFactor, Nat.not_lt.mpr (Nat.le_of_lt hgt)]
      simp [toInternal, toRaw, depositCredit, heq, hlt]
      rw [Nat.mul_div_cancel amount8 hpos]
      exact Nat.add_mul_div_right custodyRaw amount8 hpos

variable {Account Token : Type}
variable [Fintype Account] [DecidableEq Account] [DecidableEq Token]
variable [Zero Account] [Zero Token]

theorem positivePart_add_nonnegative_le (balance : Int) (credit : Nat) :
    max (balance + (credit : Int)) 0 ≤ max balance 0 + credit := by
  omega

omit [Zero Account] [Zero Token] in
theorem postedPositiveBalances_update_le
    (state : State Account Token)
    (account : Account)
    (token : Token)
    (credit : Nat) :
    postedPositiveBalances
        (upsertAssetBalance state account token (credit : Int)) token ≤
      postedPositiveBalances state token + credit := by
  unfold postedPositiveBalances
  calc
    ∑ current : Account,
        max ((upsertAssetBalance state account token (credit : Int)).internalBalance
          current token) 0 ≤
        ∑ current : Account,
          (max (state.internalBalance current token) 0 +
            if current = account then (credit : Int) else 0) := by
      apply Finset.sum_le_sum
      intro current _
      by_cases hcurrent : current = account
      · subst current
        simpa [upsertAssetBalance, updateInternalBalance, Function.update] using
          positivePart_add_nonnegative_le (state.internalBalance account token) credit
      · simp [upsertAssetBalance, updateInternalBalance, Function.update, hcurrent]
    _ = postedPositiveBalances state token + credit := by
      rw [Finset.sum_add_distrib]
      simp [postedPositiveBalances]

omit [Fintype Account] in
theorem successful_run_eq_apply
    (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = some state') :
    state' = applySuccessfulDirectDeposit state input := by
  unfold runDirectDeposit at success
  split at success
  · exact Option.some.inj success.symm
  · contradiction

omit [Fintype Account] [Zero Account] [Zero Token] in
theorem custodyRaw_after_successful_apply
    (state : State Account Token)
    (input : DirectDepositInput Account Token) :
    (applySuccessfulDirectDeposit state input).custodyRaw input.token =
      state.custodyRaw input.token +
        toRaw input.amount8 (state.tokenDecimals input.token) := by
  simp [applySuccessfulDirectDeposit, enterReentrancyGuard, exitReentrancyGuard]

omit [Fintype Account] [Zero Account] [Zero Token] in
theorem recipientBalance_after_successful_apply
    (state : State Account Token)
    (input : DirectDepositInput Account Token) :
    (applySuccessfulDirectDeposit state input).internalBalance
        input.recipient input.token =
      state.internalBalance input.recipient input.token +
        depositCredit input.amount8 (state.tokenDecimals input.token) := by
  simp [applySuccessfulDirectDeposit, enterReentrancyGuard, exitReentrancyGuard,
    upsertAssetBalance, updateInternalBalance, Function.update]

omit [Fintype Account] [Zero Account] [Zero Token] in
theorem unrelatedBalance_after_successful_apply
    (state : State Account Token)
    (input : DirectDepositInput Account Token)
    (account : Account)
    (token : Token)
    (unrelated : account ≠ input.recipient ∨ token ≠ input.token) :
    (applySuccessfulDirectDeposit state input).internalBalance account token =
      state.internalBalance account token := by
  rcases unrelated with account_ne | token_ne
  · simp [applySuccessfulDirectDeposit, enterReentrancyGuard, exitReentrancyGuard,
      upsertAssetBalance, updateInternalBalance, Function.update, account_ne]
  · by_cases account_eq : account = input.recipient
    · subst account
      simp [applySuccessfulDirectDeposit, enterReentrancyGuard, exitReentrancyGuard,
        upsertAssetBalance, updateInternalBalance, Function.update, token_ne]
    · simp [applySuccessfulDirectDeposit, enterReentrancyGuard, exitReentrancyGuard,
        upsertAssetBalance, updateInternalBalance, Function.update, account_eq]

omit [Fintype Account] [Zero Account] [Zero Token] in
theorem unrelatedCustody_after_successful_apply
    (state : State Account Token)
    (input : DirectDepositInput Account Token)
    (token : Token)
    (token_ne : token ≠ input.token) :
    (applySuccessfulDirectDeposit state input).custodyRaw token =
      state.custodyRaw token := by
  simp [applySuccessfulDirectDeposit, enterReentrancyGuard, exitReentrancyGuard,
    Function.update, token_ne]

omit [Fintype Account] [Zero Account] [Zero Token] in
theorem normalizedCustody_after_successful_apply
    (state : State Account Token)
    (input : DirectDepositInput Account Token) :
    normalizedCustody (applySuccessfulDirectDeposit state input) input.token =
      normalizedCustody state input.token +
        depositCredit input.amount8 (state.tokenDecimals input.token) := by
  simp [normalizedCustody, applySuccessfulDirectDeposit, enterReentrancyGuard,
    exitReentrancyGuard, upsertAssetBalance, toInternal_add_toRaw]

omit [Zero Account] [Zero Token] in
theorem postedPositiveBalances_after_successful_apply_le
    (state : State Account Token)
    (input : DirectDepositInput Account Token) :
    postedPositiveBalances (applySuccessfulDirectDeposit state input) input.token ≤
      postedPositiveBalances state input.token +
        depositCredit input.amount8 (state.tokenDecimals input.token) := by
  change
    postedPositiveBalances
        (upsertAssetBalance state input.recipient input.token
          (depositCredit input.amount8 (state.tokenDecimals input.token) : Int))
        input.token ≤
      postedPositiveBalances state input.token +
        depositCredit input.amount8 (state.tokenDecimals input.token)
  exact postedPositiveBalances_update_le state input.recipient input.token
    (depositCredit input.amount8 (state.tokenDecimals input.token))

/--
The one public preservation theorem for this POC.

It covers both values of `DepositKind`, hence both `deposit` and
`deposit_on_behalf_of`. The theorem is about the source-aligned Lean model only.
-/
theorem directDeposit_preservesBackingSlack
    (state state' : State Account Token)
    (input : DirectDepositInput Account Token) :
    DirectDepositPreservesBackingSlack state state' input := by
  intro success
  rw [successful_run_eq_apply state state' input success]
  unfold backingSlack
  have hCustody := normalizedCustody_after_successful_apply state input
  have hBalances := postedPositiveBalances_after_successful_apply_le state input
  omega

/-- Immediate corollary: nonnegative backing remains nonnegative. -/
theorem directDeposit_preservesNonnegativeBacking
    (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = some state')
    (backedBefore : 0 ≤ backingSlack state input.token) :
    0 ≤ backingSlack state' input.token := by
  have h := directDeposit_preservesBackingSlack state state' input success
  omega

end Accounting

section Storage

variable {Account Token : Type} [DecidableEq Token] [Zero Token]

theorem upsertRecord_amount (key : Token) (record : BalanceRecord Token) (delta : Int)
    (valid : record.WellFormed key) :
    (upsertRecord key record delta).amount = record.amount + delta := by
  rcases valid with ⟨absent, _, _⟩
  by_cases h : record.tokenAddress = 0
  · by_cases hd : delta = 0 <;> simp [upsertRecord, h, hd, absent h]
  · by_cases hz : record.amount + delta = 0 <;> simp [upsertRecord, h, hz]

theorem upsertRecord_wellFormed (key : Token) (record : BalanceRecord Token) (delta : Int)
    (key_ne : key ≠ 0) (valid : record.WellFormed key)
    (bounded : inI128 (record.amount + delta) = true) :
    (upsertRecord key record delta).WellFormed key := by
  rcases valid with ⟨absent, present, oldBound⟩
  by_cases h : record.tokenAddress = 0
  · have ha := absent h
    by_cases hd : delta = 0
    · simpa [upsertRecord, h, hd, BalanceRecord.WellFormed] using
        (show record.WellFormed key from ⟨absent, present, oldBound⟩)
    · simpa [upsertRecord, h, hd, BalanceRecord.WellFormed, key_ne, ha] using bounded
  · by_cases hz : record.amount + delta = 0
    · simp [upsertRecord, h, hz, BalanceRecord.WellFormed, inI128, i128Min, i128Max]
    · simp [upsertRecord, h, hz, BalanceRecord.WellFormed, present h, key_ne, bounded]

variable [DecidableEq Account]

theorem updateRecord_represents (records : Account → Token → BalanceRecord Token)
    (state : State Account Token) (account : Account) (token : Token) (delta : Int)
    (rep : StorageRepresents records state) (token_ne : token ≠ 0)
    (bounded : inI128 (state.internalBalance account token + delta) = true) :
    StorageRepresents (updateRecord records account token delta)
      (upsertAssetBalance state account token delta) := by
  intro a t
  by_cases ha : a = account
  · subst a
    by_cases ht : t = token
    · subst t
      have hb : inI128 ((records account token).amount + delta) = true := by
        simpa [(rep account token).2] using bounded
      have hv := upsertRecord_wellFormed token _ delta token_ne (rep account token).1 hb
      have ha := upsertRecord_amount token (records account token) delta (rep account token).1
      simpa [updateRecord, upsertAssetBalance, updateInternalBalance, Function.update,
        (rep account token).2] using And.intro hv ha
    · simpa [updateRecord, upsertAssetBalance, updateInternalBalance, Function.update, ht] using rep account t
  · simpa [updateRecord, upsertAssetBalance, updateInternalBalance, Function.update, ha] using rep a t

/-- Registration changes no balance records or amounts. -/
theorem registration_represents (records : Account → Token → BalanceRecord Token)
    (state : State Account Token) (account : Account) (rep : StorageRepresents records state) :
    StorageRepresents records { state with registeredAccounts := insert account state.registeredAccounts } :=
  rep

theorem reachableRecord_wellFormed (key : Token) (key_ne : key ≠ 0)
    (record : BalanceRecord Token) (reachable : ReachableRecord key record) :
    record.WellFormed key := by
  induction reachable with
  | empty => simp [BalanceRecord.WellFormed, inI128, i128Min, i128Max]
  | credit record delta _ bounded ih =>
    exact upsertRecord_wellFormed key record delta key_ne ih bounded

end Storage

section SourceExecution

theorem firstFailure_none_iff (checks : List DepositCheck) :
    firstFailure checks = none ↔ ∀ check ∈ checks, check.passes = true := by
  induction checks with
  | nil => simp [firstFailure]
  | cons check rest ih =>
    cases h : check.passes <;> simp [firstFailure, h, ih]

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

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

end SourceExecution

section Execution

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

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

end Execution

end Benchmark.Cases.Paraclear.DirectDepositBacking
