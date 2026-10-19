import Benchmark.Cases.Taurus.CMTATPartialFreeze.Specs
import Lean.Elab.Tactic.Omega

namespace Benchmark.Cases.Taurus.CMTATPartialFreeze
open Verity.Core
set_option maxHeartbeats 2000000

private theorem bind_ok {α β : Type} (x : Except Error α) (f : α → Except Error β)
    (b : β) (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => change Except.error e = Except.ok b at h; cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem word_val (n : Nat) (h : n < modulus) : (word n).val = n :=
  Nat.mod_eq_of_lt h

private theorem balance_lt (s : State) (a : Account) : balanceOf s a < modulus :=
  (s.balances a).isLt

private theorem frozen_lt (s : State) (a : Account) : getFrozenTokens s a < modulus :=
  (s.frozenTokens a).isLt

/-- Unchanged non-ledger fields for ordinary execution. -/
def controlFrame (s t : State) : Prop :=
  t.frozenTokens = s.frozenTokens ∧ t.addressFrozen = s.addressFrozen ∧
  t.paused = s.paused ∧ t.deactivated = s.deactivated ∧
  t.erc20Enforcer = s.erc20Enforcer ∧ t.defaultAdmin = s.defaultAdmin

private theorem check_active (s : State) (spender src to : Account) (v : Word)
    (h : _checkTransferred s spender src to v = .ok ()) :
    getFrozenTokens s src ≤ balanceOf s src ∧
    (getFrozenTokens s src > 0 → v.val ≤ balanceOf s src - getFrozenTokens s src) := by
  obtain ⟨b, hb, rest⟩ := bind_ok _ _ _ h
  have bt : b = true := by
    cases b
    · change Except.error Error.activeBalance = Except.ok () at rest
      cases rest
    · rfl
  subst b
  dsimp [_checkActiveBalance] at hb
  split at hb
  · split at hb
    · cases hb
    · have hv : v.val ≤ balanceOf s src - getFrozenTokens s src := by simpa using hb
      constructor
      · omega
      · intro _; exact hv
  · constructor <;> omega

/-- `_update` here is only the nonzero-endpoint transfer ledger fragment. -/
private theorem update_facts (s t : State) (src to : Account) (v : Word)
    (h : _update s src to v = .ok t) :
    v.val ≤ balanceOf s src ∧ controlFrame s t ∧ t.allowances = s.allowances ∧
    balanceOf t src = (if src = to then balanceOf s src else balanceOf s src - v.val) ∧
    (∀ a, a ≠ src → a ≠ to → t.balances a = s.balances a) := by
  unfold _update at h
  split at h
  · cases h
  · rename_i hn
    have hv : v.val ≤ balanceOf s src := by omega
    have hd : balanceOf s src - v.val < modulus := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (balance_lt s src)
    cases h
    refine ⟨hv, ?_, rfl, ?_, ?_⟩
    · simp [controlFrame]
    · by_cases he : src = to
      · subst to
        simp only [balanceOf, ite_true]
        change (word ((word (balanceOf s src - v.val)).val + v.val)).val = balanceOf s src
        rw [word_val _ hd]
        rw [Nat.sub_add_cancel hv]
        exact word_val _ (balance_lt s src)
      · simp only [balanceOf, he, ↓reduceIte]
        exact word_val _ hd
    · intro a hsrc hto
      simp [hsrc, hto]

private theorem transfer_facts (s t : State) (src to : Account) (v : Word)
    (h : _transfer s src to v = .ok t) :
    v.val ≤ balanceOf s src ∧ controlFrame s t ∧ t.allowances = s.allowances ∧
    balanceOf t src = (if src = to then balanceOf s src else balanceOf s src - v.val) ∧
    (∀ a, a ≠ src → a ≠ to → t.balances a = s.balances a) := by
  unfold _transfer at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact update_facts s t src to v h

private theorem spend_facts (s t : State) (owner spender : Account) (v : Word)
    (h : _spendAllowance s owner spender v = .ok t) :
    t.balances = s.balances ∧ controlFrame s t ∧
    (if (s.allowances owner spender).val = modulus - 1 then t.allowances = s.allowances
     else v.val ≤ (s.allowances owner spender).val ∧
       t.allowances owner spender = word ((s.allowances owner spender).val - v.val) ∧
       ∀ a b, (a ≠ owner ∨ b ≠ spender) → t.allowances a b = s.allowances a b) := by
  dsimp [_spendAllowance] at h
  split at h
  · cases h
    simp [*, controlFrame]
  · rename_i hm
    split at h
    · cases h
    · rename_i hv
      unfold _approve at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
          refine ⟨rfl, ?_, ?_⟩
          · simp [controlFrame]
          · simp only [hm, ↓reduceIte]
            refine ⟨by omega, by simp, ?_⟩
            intro a b hab
            rcases hab with ha | hb
            · simp [ha]
            · simp [hb]

private theorem protected_of_facts (s t : State) (op : Operation)
    (hc : getFrozenTokens s op.sender ≤ balanceOf s op.sender)
    (ha : getFrozenTokens s op.sender > 0 → op.amount.val ≤ balanceOf s op.sender - getFrozenTokens s op.sender)
    (hv : op.amount.val ≤ balanceOf s op.sender)
    (hf : t.frozenTokens = s.frozenTokens)
    (hb : balanceOf t op.sender = if op.sender = op.recipient then balanceOf s op.sender else balanceOf s op.sender - op.amount.val) :
    senderProtected s t op := by
  have bound : op.amount.val ≤ balanceOf s op.sender - getFrozenTokens s op.sender := by
    by_cases hz : getFrozenTokens s op.sender > 0
    · exact ha hz
    · have : getFrozenTokens s op.sender = 0 := by omega
      simpa [this] using hv
  refine ⟨bound, hf, ?_, hb⟩
  unfold getFrozenTokens
  rw [hf, hb]
  split <;> dsimp [getFrozenTokens] at * <;> omega

theorem transfer_senderProtected (s t : State) (caller to : Account) (v : Word)
    (h : transfer s caller to v = .ok t) : senderProtected s t (.transfer caller to v) := by
  obtain ⟨u, hc, ht⟩ := bind_ok _ _ _ h
  cases u
  obtain ⟨hback, hactive⟩ := check_active s 0 caller to v hc
  obtain ⟨hv, hf, _, hb, _⟩ := transfer_facts s t caller to v ht
  exact protected_of_facts s t _ hback hactive hv hf.1 hb

theorem transferFrom_senderProtected (s t : State) (caller src to : Account) (v : Word)
    (h : transferFrom s caller src to v = .ok t) : senderProtected s t (.transferFrom caller src to v) := by
  obtain ⟨u, hc, rest⟩ := bind_ok _ _ _ h
  cases u
  obtain ⟨a, hs, ht⟩ := bind_ok _ _ _ rest
  obtain ⟨hback, hactive⟩ := check_active s caller src to v hc
  obtain ⟨hab, haf, _⟩ := spend_facts s a src caller v hs
  obtain ⟨hv, htf, _, hb, _⟩ := transfer_facts a t src to v ht
  have hbal : ∀ x, balanceOf a x = balanceOf s x := by intro x; simp [balanceOf, hab]
  have hfr : t.frozenTokens = s.frozenTokens := htf.1.trans haf.1
  apply protected_of_facts s t (.transferFrom caller src to v) hback hactive
  · simpa only [Operation.amount, Operation.sender, hbal] using hv
  · exact hfr
  · simpa only [Operation.sender, Operation.recipient, Operation.amount, hbal] using hb

theorem run_senderProtected (s t : State) (op : Operation) (h : run s op = .ok t) :
    senderProtected s t op := by
  cases op with
  | transfer c to v => exact transfer_senderProtected s t c to v h
  | transferFrom c src to v => exact transferFrom_senderProtected s t c src to v h

theorem all_traces_protected (s : State) (ops : List Operation) : traceProtected s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
    simp only [traceProtected]
    split
    · exact ih s
    · rename_i t h
      exact ⟨run_senderProtected s t op h, ih t⟩

theorem error_atomic_rollback (s : State) (op : Operation) (e : Error)
    (h : run s op = .error e) : transact s op = (false, s) := by
  simp [transact, h]

theorem freeze_establishes_backing (s t : State) (caller account : Account) (v : Word)
    (h : freezePartialTokens s caller account v = .ok t) : freezeBacking t account := by
  dsimp [freezePartialTokens] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hrange
      split at h
      · cases h
      · rename_i hcover
        cases h
        simp only [freezeBacking, getFrozenTokens, balanceOf, ite_true]
        change (word (getFrozenTokens s account + v.val)).val ≤ balanceOf s account
        rw [word_val _ (by omega)]
        exact Nat.le_of_not_gt hcover

theorem unfreeze_preserves_backing (s t : State) (caller account : Account) (v : Word)
    (initial : freezeBacking s account)
    (h : unfreezePartialTokens s caller account v = .ok t) : freezeBacking t account := by
  unfold unfreezePartialTokens at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      have hr : getFrozenTokens s account - v.val < modulus :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (frozen_lt s account)
      simp only [freezeBacking, getFrozenTokens, balanceOf, ite_true]
      change (word (getFrozenTokens s account - v.val)).val ≤ balanceOf s account
      rw [word_val _ hr]
      exact Nat.le_trans (Nat.sub_le _ _) initial

private theorem controlFrame_trans {s a t : State} (ha : controlFrame s a)
    (ht : controlFrame a t) : controlFrame s t := by
  rcases ha with ⟨h1,h2,h3,h4,h5,h6⟩
  rcases ht with ⟨k1,k2,k3,k4,k5,k6⟩
  exact ⟨k1.trans h1,k2.trans h2,k3.trans h3,k4.trans h4,k5.trans h5,k6.trans h6⟩

/-- Direct transfer preserves every allowance, all control fields, and unrelated balances. -/
theorem transfer_frame (s t : State) (caller to : Account) (v : Word)
    (h : transfer s caller to v = .ok t) :
    controlFrame s t ∧ t.allowances = s.allowances ∧
    ∀ a, a ≠ caller → a ≠ to → t.balances a = s.balances a := by
  obtain ⟨u, _, ht⟩ := bind_ok _ _ _ h
  cases u
  obtain ⟨_, hf, hal, _, hbal⟩ := transfer_facts s t caller to v ht
  exact ⟨hf, hal, hbal⟩

/-- Exact maximum/finite allowance split, including the complete unrelated-slot frame. -/
theorem transferFrom_allowance_frame (s t : State) (caller src to : Account) (v : Word)
    (h : transferFrom s caller src to v = .ok t) :
    controlFrame s t ∧
    (∀ a, a ≠ src → a ≠ to → t.balances a = s.balances a) ∧
    (if (s.allowances src caller).val = modulus - 1 then t.allowances = s.allowances
     else v.val ≤ (s.allowances src caller).val ∧
       t.allowances src caller = word ((s.allowances src caller).val - v.val) ∧
       ∀ a b, (a ≠ src ∨ b ≠ caller) → t.allowances a b = s.allowances a b) := by
  obtain ⟨u, _, rest⟩ := bind_ok _ _ _ h
  cases u
  obtain ⟨a, hs, ht⟩ := bind_ok _ _ _ rest
  obtain ⟨hab, haf, hal⟩ := spend_facts s a src caller v hs
  obtain ⟨_, htf, htal, _, hbal⟩ := transfer_facts a t src to v ht
  refine ⟨controlFrame_trans haf htf, ?_, ?_⟩
  · intro x hx hy
    rw [hbal x hx hy, hab]
  · rw [htal]
    exact hal

theorem transferFrom_max_allowance (s t : State) (caller src to : Account) (v : Word)
    (hmax : (s.allowances src caller).val = modulus - 1)
    (h : transferFrom s caller src to v = .ok t) : t.allowances = s.allowances := by
  have hf := (transferFrom_allowance_frame s t caller src to v h).2.2
  simpa only [hmax, ↓reduceIte] using hf

theorem transferFrom_finite_allowance (s t : State) (caller src to : Account) (v : Word)
    (hfinite : (s.allowances src caller).val ≠ modulus - 1)
    (h : transferFrom s caller src to v = .ok t) :
    v.val ≤ (s.allowances src caller).val ∧
    (t.allowances src caller).val = (s.allowances src caller).val - v.val ∧
    (∀ a b, (a ≠ src ∨ b ≠ caller) → t.allowances a b = s.allowances a b) := by
  have hf := (transferFrom_allowance_frame s t caller src to v h).2.2
  simp only [hfinite, ↓reduceIte] at hf
  refine ⟨hf.1, ?_, hf.2.2⟩
  rw [hf.2.1]
  exact word_val _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s.allowances src caller).isLt)

/-- Every successful operation has the non-ledger and unrelated-balance frame. -/
theorem run_frame (s t : State) (op : Operation) (h : run s op = .ok t) :
    controlFrame s t ∧
    ∀ a, a ≠ op.sender → a ≠ op.recipient → t.balances a = s.balances a := by
  cases op with
  | transfer c to v =>
    have hf := transfer_frame s t c to v h
    exact ⟨hf.1, hf.2.2⟩
  | transferFrom c src to v =>
    have hf := transferFrom_allowance_frame s t c src to v h
    exact ⟨hf.1, hf.2.1⟩

/-- Single exported conjunction used for the kernel dependency audit. -/
theorem phase3_theorem_bundle :
    (∀ s t op, run s op = .ok t → senderProtected s t op) ∧
    (∀ s ops, traceProtected s ops) ∧
    (∀ s t c to v, transfer s c to v = .ok t →
      controlFrame s t ∧ t.allowances = s.allowances ∧
      ∀ a, a ≠ c → a ≠ to → t.balances a = s.balances a) ∧
    (∀ s t c src to v, transferFrom s c src to v = .ok t →
      controlFrame s t ∧
      (∀ a, a ≠ src → a ≠ to → t.balances a = s.balances a) ∧
      (if (s.allowances src c).val = modulus - 1 then t.allowances = s.allowances
       else v.val ≤ (s.allowances src c).val ∧
         t.allowances src c = word ((s.allowances src c).val - v.val) ∧
         ∀ a b, (a ≠ src ∨ b ≠ c) → t.allowances a b = s.allowances a b)) ∧
    (∀ s op e, run s op = .error e → transact s op = (false, s)) ∧
    (∀ s t c a v, freezePartialTokens s c a v = .ok t → freezeBacking t a) ∧
    (∀ s t c a v, freezeBacking s a → unfreezePartialTokens s c a v = .ok t → freezeBacking t a) :=
  ⟨run_senderProtected, all_traces_protected, transfer_frame,
   transferFrom_allowance_frame, error_atomic_rollback,
   freeze_establishes_backing, unfreeze_preserves_backing⟩

#print axioms phase3_theorem_bundle
#print axioms transferFrom_finite_allowance
#print axioms transferFrom_max_allowance
#print axioms run_frame

end Benchmark.Cases.Taurus.CMTATPartialFreeze
