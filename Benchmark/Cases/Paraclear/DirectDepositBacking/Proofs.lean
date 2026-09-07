import Benchmark.Cases.Paraclear.DirectDepositBacking.Specs

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

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

end Benchmark.Cases.Paraclear.DirectDepositBacking
