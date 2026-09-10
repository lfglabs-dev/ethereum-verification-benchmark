import Benchmark.Cases.Paraclear.DirectDepositBacking.Specs

/-!
# Direct proof about the single deposit executor

1. Induction on executeChecks derives passed checks and the actual phase effects.
   The final state below is a theorem about execution, not a second deposit function.
2. Successful receipt checks and entry consistency establish the custody increment.
3. Decimal arithmetic and the positive-part bound show that custody growth covers
   any increase in positive customer balances.
4. Decoded record lemmas justify the numeric balance update for valid records.

The main theorem needs only successful modeled execution. Record validity is a
premise of the supporting storage theorem, not an extra premise of the backing rule.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

/-! ## Arithmetic helpers -/
section

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

end

/-! ## Decoded record updates -/
section

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

end

/-! ## Direct execution proof -/
section

variable {Account Token : Type}
variable [DecidableEq Account] [DecidableEq Token] [Zero Account] [Zero Token]

/-- Induct on the actual interpreter, retaining both acceptance and state effects. -/
theorem executeChecks_success (input : DirectDepositInput Account Token) (d : Nat)
    (checks : List DepositCheck) (state state' : State Account Token)
    (success : executeChecks input d checks state = .ok state') :
    (∀ check ∈ checks, check.passes = true) ∧
      state' = checks.foldl (fun s check => phaseEffect input d check.phase s) state := by
  induction checks generalizing state with
  | nil =>
    simp only [executeChecks, Except.ok.injEq] at success
    subst state'
    simp
  | cons check rest ih =>
    simp only [executeChecks] at success
    split at success
    · rename_i passed
      obtain ⟨accepted, effects⟩ := ih _ success
      constructor
      · simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨passed, accepted⟩
      · simpa only [List.foldl_cons] using effects
    · contradiction

theorem successful_deposit_observation (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    input.transfer.balanceBefore = state.custodyRaw input.token := by
  unfold runDirectDeposit at success
  split at success
  · assumption
  · contradiction

theorem successful_deposit_checks (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    ∀ check ∈ sourceChecks state input, check.passes = true := by
  unfold runDirectDeposit at success
  split at success
  · exact (executeChecks_success input _ _ state state' success).1
  · contradiction

/-- Derive the observed final state by executing the phases. No endpoint model is
defined or assumed, and custody remains the observed after-balance. -/
theorem successful_deposit_state (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    state' = { state with
      internalBalance := updateInternalBalance state.internalBalance input.recipient input.token
        (state.internalBalance input.recipient input.token +
          (depositCredit input.amount8 (state.tokenDecimals input.token) : Int))
      custodyRaw := Function.update state.custodyRaw input.token input.transfer.balanceAfter
      registeredAccounts := insert input.recipient state.registeredAccounts
      reentrancyEntered := false } := by
  unfold runDirectDeposit at success
  split at success
  · have effects := (executeChecks_success input _ _ state state' success).2
    simpa [sourceChecks, List.foldl, phaseEffect, upsertAssetBalance] using effects
  · contradiction

/-- Exact receipt is extracted from the successful execution's checks, not assumed
as the conclusion of the business theorem. Removing that check breaks this argument. -/
theorem successful_deposit_receipt (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    input.transfer.balanceAfter = state.custodyRaw input.token +
      toRaw input.amount8 (state.tokenDecimals input.token) := by
  have accepted := successful_deposit_checks state state' input success
  simp only [sourceChecks, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have coupled := successful_deposit_observation state state' input success
  omega

theorem recipientBalance_after_success (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    state'.internalBalance input.recipient input.token =
      state.internalBalance input.recipient input.token +
        depositCredit input.amount8 (state.tokenDecimals input.token) := by
  rw [successful_deposit_state state state' input success]
  simp [updateInternalBalance]

theorem unrelatedBalance_after_success (state state' : State Account Token)
    (input : DirectDepositInput Account Token) (account : Account) (token : Token)
    (success : runDirectDeposit state input = .ok state')
    (unrelated : account ≠ input.recipient ∨ token ≠ input.token) :
    state'.internalBalance account token = state.internalBalance account token := by
  rw [successful_deposit_state state state' input success]
  rcases unrelated with ha | ht
  · simp [updateInternalBalance, Function.update, ha]
  · by_cases ha : account = input.recipient
    · subst account
      simp [updateInternalBalance, Function.update, ht]
    · simp [updateInternalBalance, Function.update, ha]

theorem unrelatedCustody_after_success (state state' : State Account Token)
    (input : DirectDepositInput Account Token) (token : Token)
    (success : runDirectDeposit state input = .ok state') (token_ne : token ≠ input.token) :
    state'.custodyRaw token = state.custodyRaw token := by
  rw [successful_deposit_state state state' input success]
  simp [Function.update, token_ne]

/-- Relates decoded records to the successful executor's numeric balances. -/
theorem directDeposit_storage_represents (state state' : State Account Token)
    (records : Account → Token → BalanceRecord Token)
    (input : DirectDepositInput Account Token)
    (rep : StorageRepresents records state)
    (success : runDirectDeposit state input = .ok state') :
    StorageRepresents
      (updateRecord records input.recipient input.token
        (depositCredit input.amount8 (state.tokenDecimals input.token) : Int)) state' := by
  have accepted := successful_deposit_checks state state' input success
  simp only [sourceChecks, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have token_ne : input.token ≠ 0 := by tauto
  have bounded : inI128 (state.internalBalance input.recipient input.token +
      (depositCredit input.amount8 (state.tokenDecimals input.token) : Int)) = true := by tauto
  rw [successful_deposit_state state state' input success]
  change StorageRepresents _ (upsertAssetBalance state input.recipient input.token
    (depositCredit input.amount8 (state.tokenDecimals input.token) : Int))
  exact updateRecord_represents records state input.recipient input.token _ rep token_ne bounded

theorem rejected_deposit_preserves_projection (state : State Account Token)
    (input : DirectDepositInput Account Token) (phase : DepositPhase)
    (failed : runDirectDeposit state input = .error phase) :
    committedDepositState state input = state := by
  simp [committedDepositState, failed]

variable [Fintype Account]

theorem normalizedCustody_after_success (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    normalizedCustody state' input.token = normalizedCustody state input.token +
      depositCredit input.amount8 (state.tokenDecimals input.token) := by
  have receipt := successful_deposit_receipt state state' input success
  rw [successful_deposit_state state state' input success]
  simp [normalizedCustody, receipt, toInternal_add_toRaw]

theorem postedPositiveBalances_after_success_le (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state') :
    postedPositiveBalances state' input.token ≤ postedPositiveBalances state input.token +
      depositCredit input.amount8 (state.tokenDecimals input.token) := by
  rw [successful_deposit_state state state' input success]
  change postedPositiveBalances
    (upsertAssetBalance state input.recipient input.token
      (depositCredit input.amount8 (state.tokenDecimals input.token) : Int)) input.token ≤ _
  exact postedPositiveBalances_update_le state input.recipient input.token _

/-- The business theorem is proved directly about the sole step-by-step executor. -/
theorem directDeposit_preservesBackingSlack (state state' : State Account Token)
    (input : DirectDepositInput Account Token) :
    DirectDepositPreservesBackingSlack state state' input := by
  intro success
  have custody := normalizedCustody_after_success state state' input success
  have claims := postedPositiveBalances_after_success_le state state' input success
  unfold backingSlack
  omega

theorem directDeposit_preservesNonnegativeBacking (state state' : State Account Token)
    (input : DirectDepositInput Account Token)
    (success : runDirectDeposit state input = .ok state')
    (backedBefore : 0 ≤ backingSlack state input.token) :
    0 ≤ backingSlack state' input.token := by
  have preserved := directDeposit_preservesBackingSlack state state' input success
  omega

end

end Benchmark.Cases.Paraclear.DirectDepositBacking
