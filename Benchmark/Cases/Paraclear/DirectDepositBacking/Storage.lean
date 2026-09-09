import Benchmark.Cases.Paraclear.DirectDepositBacking.Contract

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

/-- Decoded amount-level storage. Pointers and felt decoding remain outside this type. -/
structure BalanceRecord (Token : Type) where
  tokenAddress : Token
  amount : Int
  deriving Repr, DecidableEq

variable {Account Token : Type} [DecidableEq Token] [Zero Token]

def BalanceRecord.WellFormed (key : Token) (record : BalanceRecord Token) : Prop :=
  (record.tokenAddress = 0 → record.amount = 0) ∧
  (record.tokenAddress ≠ 0 → record.tokenAddress = key) ∧
  inI128 record.amount = true

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

def StorageRepresents (records : Account → Token → BalanceRecord Token)
    (state : State Account Token) : Prop :=
  ∀ account token, (records account token).WellFormed token ∧
    (records account token).amount = state.internalBalance account token

def updateRecord (records : Account → Token → BalanceRecord Token)
    (account : Account) (token : Token) (delta : Int) :=
  Function.update records account
    (Function.update (records account) token (upsertRecord token (records account token) delta))

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

/-- Deposit-local record histories. Other Cairo writers must be added before this
can establish validity for arbitrary protocol histories. -/
inductive ReachableRecord (key : Token) : BalanceRecord Token → Prop where
  | empty : ReachableRecord key ⟨0, 0⟩
  | credit (record : BalanceRecord Token) (delta : Int)
      (prior : ReachableRecord key record)
      (bounded : inI128 (record.amount + delta) = true) :
      ReachableRecord key (upsertRecord key record delta)

theorem reachableRecord_wellFormed (key : Token) (key_ne : key ≠ 0)
    (record : BalanceRecord Token) (reachable : ReachableRecord key record) :
    record.WellFormed key := by
  induction reachable with
  | empty => simp [BalanceRecord.WellFormed, inI128, i128Min, i128Max]
  | credit record delta _ bounded ih =>
    exact upsertRecord_wellFormed key record delta key_ne ih bounded

end Benchmark.Cases.Paraclear.DirectDepositBacking
