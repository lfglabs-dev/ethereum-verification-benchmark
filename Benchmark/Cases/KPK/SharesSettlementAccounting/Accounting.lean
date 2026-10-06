import Benchmark.Cases.KPK.SharesSettlementAccounting.Execution
import Mathlib.Tactic.Ring

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

-- Pure validation cannot change the state before fee-prefix assumptions apply.
theorem validatePriceDeviation_success (asset : Address) (price : Nat) (s t : State)
    (hp : price < wordLimit) (hl : s.lastSettledPrice asset < wordLimit)
    (h : _validatePriceDeviation asset price s = .ok ((),t)) : t = s := by
  by_cases hz : s.lastSettledPrice asset = 0
  · simp [_validatePriceDeviation, hz, get, getThe, MonadStateOf.get,
      StateT.get, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure] at h
    exact h.symm
  · simp only [_validatePriceDeviation, get, getThe, MonadStateOf.get,
      StateT.get, Bind.bind, StateT.bind, Except.bind, Pure.pure,
      StateT.pure, Except.pure, show (s.lastSettledPrice asset == 0) = false by simpa using hz,
      Bool.false_eq_true, ↓reduceIte] at h
    let d := if price > s.lastSettledPrice asset then price - s.lastSettledPrice asset
      else s.lastSettledPrice asset - price
    have hd : d < wordLimit := by dsimp [d]; split <;> omega
    change (mulDiv d bps (s.lastSettledPrice asset) >>= fun q =>
      guard (q <= 3000) "PriceDeviationTooLarge") s = .ok ((),t) at h
    obtain ⟨q,m,hm,hg⟩ := tx_bind_ok _ _ _ _ _ h
    have hs := (mulDiv_success _ _ _ _ _ _ hd (by norm_num [bps,wordLimit]) hl hm).2.2.2
    rw [hs] at hg
    exact (guard_success _ _ _ _ _ hg).2

theorem bslot_injective : Function.Injective bslot := by
  intro a b h
  apply Verity.Core.Address.ext
  dsimp [bslot] at h
  omega

-- Cantor cells have disjoint diagonals; no address collision hypothesis is used.
theorem cantor_injective (a b c d : Nat)
    (h : (a+b)*(a+b+1)/2+b = (c+d)*(c+d+1)/2+d) : a = c ∧ b = d := by
  have triangle_step (x : Nat) : x*(x+1)/2 + x+1 = (x+1)*(x+2)/2 := by
    have he : (x+1)*(x+2) = x*(x+1) + 2*(x+1) := by ring
    rw [he, Nat.add_mul_div_left]
    · omega
    · decide
  have triangle_mono (x y : Nat) (hxy : x < y) :
      x*(x+1)/2+x < y*(y+1)/2 := by
    have hx := triangle_step x
    have hm : (x+1)*(x+2) ≤ y*(y+1) := Nat.mul_le_mul (by omega) (by omega)
    have hh := Nat.div_le_div_right (c := 2) hm
    omega
  have hs : a+b = c+d := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · have hh' := triangle_mono _ _ hh
      omega
    · have hh' := triangle_mono _ _ hh
      omega
  rw [hs] at h
  constructor <;> omega

theorem aslot_injective (a b c d : Address) (h : aslot a b = aslot c d) : a = c ∧ b = d := by
  have hp : (a.val+b.val)*(a.val+b.val+1)/2+b.val =
      (c.val+d.val)*(c.val+d.val+1)/2+d.val := by dsimp [aslot] at h; omega
  obtain ⟨ha,hb⟩ := cantor_injective _ _ _ _ hp
  exact ⟨Verity.Core.Address.ext ha,Verity.Core.Address.ext hb⟩

theorem transfer_allowance_frame (s : State) (token fromAddr toAddr owner spender : Address)
    (amount : Nat) :
    assetAllowance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount}
      token owner spender = assetAllowance s token owner spender := by
  simp [assetAllowance, tokenWordTransfer, writeExternal, allowance_slot_ne_balance]

-- Success extracts actual finite/infinite allowance branches and affordability.
theorem safeTransferFrom_success (env : Environment) (token spender fromAddr toAddr : Address)
    (amount : Nat) (s t : State)
    (ha : amount < wordLimit) (ho : assetBalance s token fromAddr < wordLimit)
    (hal : assetAllowance s token fromAddr spender < wordLimit)
    (h : safeTransferFrom env token spender fromAddr toAddr amount s = .ok ((),t)) :
    (env.hasCode token && env.isToken token && env.tokenAccepts token) = true ∧
    (token != s.config.self) = true ∧ (fromAddr != 0 && toAddr != 0) = true ∧
    amount ≤ assetBalance s token fromAddr ∧
    (if assetAllowance s token fromAddr spender = wordLimit-1 then
      t = {s with
        external := tokenWordTransfer s.external token fromAddr toAddr amount,
        trace := s.trace ++ [.assetTransfer token fromAddr toAddr amount]}
    else amount ≤ assetAllowance s token fromAddr spender ∧
      t = {s with
        external := tokenWordTransfer
          (writeExternal s.external token.val (aslot fromAddr spender)
            (assetAllowance s token fromAddr spender - amount)) token fromAddr toAddr amount,
        trace := s.trace ++ [.allowanceSpent token fromAddr spender amount,
          .assetTransfer token fromAddr toAddr amount]}) := by
  by_cases hi : assetAllowance s token fromAddr spender = wordLimit-1
  · simp only [safeTransferFrom, get, getThe, MonadStateOf.get, StateT.get,
      Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
      hi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hc,ht,he,hb,hn⟩ := safeTransfer_success _ _ _ _ _ _ _ ha ho h
    exact ⟨hc,ht,he,hb,by simpa only [if_pos hi] using hn⟩
  · have hiB : (assetAllowance s token fromAddr spender != wordLimit-1) = true := by simpa using hi
    by_cases hsp : amount ≤ assetAllowance s token fromAddr spender
    · let m : State := {s with
        external := writeExternal s.external token.val (aslot fromAddr spender)
          (assetAllowance s token fromAddr spender - amount)
        trace := s.trace ++ [.allowanceSpent token fromAddr spender amount]}
      have hrun : safeTransferFrom env token spender fromAddr toAddr amount s =
          safeTransfer env token fromAddr toAddr amount m := by
        simp only [safeTransferFrom, get, getThe, MonadStateOf.get, StateT.get,
          Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
          hiB, ↓reduceIte, checkedSub_run _ _ hal ha s, hsp,
          putExternal_run, record_run]
        rfl
      rw [hrun] at h
      have hbal : assetBalance m token fromAddr = assetBalance s token fromAddr :=
        balance_after_allowance_write _ _ _ _ _ _
      obtain ⟨hc,ht,he,hb,hn⟩ := safeTransfer_success _ _ _ _ _ _ _ ha
        (by rw [hbal]; exact ho) h
      refine ⟨hc,ht,he,by simpa only [hbal] using hb,?_⟩
      rw [if_neg hi]
      refine ⟨hsp,?_⟩
      simpa only [m, List.append_assoc, List.cons_append, List.nil_append] using hn
    · simp [safeTransferFrom, get, getThe, MonadStateOf.get, StateT.get,
        Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure,
        hiB, checkedSub_run _ _ hal ha s, hsp,
        MonadExcept.throw, throwThe, MonadExceptOf.throw, StateT.lift] at h

theorem support_member_bound (accounts : List Address) (f : Address → Nat)
    (x : Address) (hx : x ∈ accounts) : f x ≤ (accounts.map f).sum := by
  induction accounts with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hh := ih hx
      simp only [List.map_cons,List.sum_cons]; omega

-- A support sum bounds two distinct endpoint balances jointly, not just separately.
theorem support_pair_bound (accounts : List Address) (f : Address → Nat)
    (hn : accounts.Nodup) (hs : ∀ a, a ∉ accounts → f a = 0)
    (x y : Address) (hne : x ≠ y) : f x + f y ≤ (accounts.map f).sum := by
  induction accounts generalizing f with
  | nil => simp only [List.not_mem_nil, forall_const] at hs; simp [hs]
  | cons a as ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hx : x = a
    · subst x
      have hy : y ≠ a := Ne.symm hne
      have hfy : f y ≤ (as.map f).sum := by
        by_cases hm : y ∈ as
        · exact support_member_bound as f y hm
        · have hh : y ∉ a::as := by simp [hm,hy]
          rw [hs y hh]; omega
      simp only [List.map_cons,List.sum_cons]; omega
    · by_cases hy : y = a
      · subst y
        have hfx : f x ≤ (as.map f).sum := by
          by_cases hm : x ∈ as
          · exact support_member_bound as f x hm
          · have hh : x ∉ a::as := by simp [hm,hx]
            rw [hs x hh]; omega
        simp only [List.map_cons,List.sum_cons]; omega
      · let g := fun z => if z = a then 0 else f z
        have hsg : ∀ z, z ∉ as → g z = 0 := by
          intro z hz
          by_cases ha : z = a
          · simp [g,ha]
          · have hh : z ∉ a::as := by simp [hz,ha]
            simp [g,ha,hs z hh]
        have hg : as.map g = as.map f := by
          apply List.map_congr_left
          intro z hz
          have ha : z ≠ a := by intro he; subst z; exact hn'.1 hz
          simp [g,ha]
        have hh := ih g hn'.2 hsg
        simp only [g,if_neg hx,if_neg hy,hg] at hh
        simp only [List.map_cons,List.sum_cons]; omega

-- Exact word-level recipient reload works for all aliases; a distinct endpoint
-- no-wrap bound is necessary, and later follows from finite-support coherence.
theorem token_transfer_balance (s : State) (token fromAddr toAddr x : Address)
    (amount : Nat) (ha : amount ≤ assetBalance s token fromAddr)
    (ho : assetBalance s token fromAddr < wordLimit)
    (hr : fromAddr ≠ toAddr → assetBalance s token toAddr + amount < wordLimit) :
    assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount}
      token x =
      if x = toAddr then (if fromAddr = toAddr then assetBalance s token x
        else assetBalance s token x + amount)
      else if x = fromAddr then assetBalance s token x - amount else assetBalance s token x := by
  have hslot (a b : Address) : bslot a = bslot b ↔ a = b :=
    ⟨fun h => bslot_injective h,congrArg bslot⟩
  by_cases he : fromAddr = toAddr
  · subst toAddr
    by_cases hx : x = fromAddr
    · subst x
      have hv : (word (assetBalance s token fromAddr - amount + amount)).val =
          assetBalance s token fromAddr := by rw [Nat.sub_add_cancel ha]; exact word_val _ ho
      simpa [assetBalance,tokenWordTransfer,writeExternal] using hv
    · simp [assetBalance,tokenWordTransfer,writeExternal,hslot,hx]
  · by_cases hx : x = toAddr
    · subst x
      have hv := word_val _ (hr he)
      simpa [assetBalance,tokenWordTransfer,writeExternal,hslot,he,Ne.symm he] using hv
    · by_cases hf : x = fromAddr
      · subst x
        simp [assetBalance,tokenWordTransfer,writeExternal,hslot,he,Ne.symm he]
      · simp [assetBalance,tokenWordTransfer,writeExternal,hslot,hx,hf,he]

theorem token_transfer_integer_effect (s : State) (token fromAddr toAddr x : Address)
    (amount : Nat) (ha : amount ≤ assetBalance s token fromAddr)
    (ho : assetBalance s token fromAddr < wordLimit)
    (hr : fromAddr ≠ toAddr → assetBalance s token toAddr + amount < wordLimit) :
    (assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount}
      token x : Int) - assetBalance s token x = indicator x toAddr amount - indicator x fromAddr amount := by
  rw [token_transfer_balance _ _ _ _ _ _ ha ho hr]
  by_cases ht : x = toAddr
  · subst x
    by_cases he : fromAddr = toAddr
    · subst fromAddr; simp [indicator]
    · simp [he,Ne.symm he,indicator]
  · by_cases hf : x = fromAddr
    · subst x
      simp only [if_neg ht,if_pos rfl,indicator,if_neg ht,if_true]
      omega
    · simp [ht,hf,indicator]

theorem token_coherent_credit_bound (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (token fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0)
    (amount : Nat) (ha : amount ≤ assetBalance s token fromAddr) (hne : fromAddr ≠ toAddr) :
    assetBalance s token toAddr + amount < wordLimit := by
  obtain ⟨_,_,accounts,hn,hs,hb,_⟩ := hap token hreg ht
  have hh := support_pair_bound accounts (assetBalance s token) hn hs fromAddr toAddr hne
  omega

-- Finite-support closure uses a real zero-extension of the witness list.
theorem support_insert (accounts : List Address) (f : Address → Nat)
    (hn : accounts.Nodup) (hs : ∀ a, a ∉ accounts → f a = 0) (x : Address) :
    (accounts.insert x).Nodup ∧
    (∀ a, a ∉ accounts.insert x → f a = 0) ∧
    ((accounts.insert x).map f).sum = (accounts.map f).sum := by
  by_cases hx : x ∈ accounts
  · rw [List.insert_of_mem hx]; exact ⟨hn,hs,rfl⟩
  · rw [List.insert_of_not_mem hx]
    refine ⟨List.nodup_cons.mpr ⟨hx,hn⟩,?_,?_⟩
    · intro a ha
      exact hs a (fun hm => ha (List.mem_cons_of_mem x hm))
    · simp [hs x hx]

theorem sum_indicator (accounts : List Address) (x : Address) (amount : Nat)
    (hn : accounts.Nodup) :
    (accounts.map fun a => if a = x then amount else 0).sum =
      if x ∈ accounts then amount else 0 := by
  induction accounts with
  | nil => simp
  | cons a as ih =>
    have hh := List.nodup_cons.mp hn
    by_cases ha : a = x
    · subst a
      simp [hh.1, ih hh.2]
    · simp [ha,Ne.symm ha,ih hh.2]

theorem sum_pointwise_balance (accounts : List Address) (f g : Address → Nat)
    (fromAddr toAddr : Address) (amount : Nat)
    (h : ∀ x, g x + (if x = fromAddr then amount else 0) =
      f x + (if x = toAddr then amount else 0)) :
    (accounts.map g).sum + (accounts.map fun x => if x = fromAddr then amount else 0).sum =
      (accounts.map f).sum + (accounts.map fun x => if x = toAddr then amount else 0).sum := by
  induction accounts with
  | nil => simp
  | cons a as ih =>
    have hh := h a
    simp only [List.map_cons,List.sum_cons]
    omega

theorem support_transfer_preserved (accounts : List Address) (f g : Address → Nat)
    (hn : accounts.Nodup) (hs : ∀ a, a ∉ accounts → f a = 0)
    (fromAddr toAddr : Address) (amount : Nat)
    (h : ∀ x, g x + (if x = fromAddr then amount else 0) =
      f x + (if x = toAddr then amount else 0)) :
    ∃ next : List Address, next.Nodup ∧ (∀ a, a ∉ next → g a = 0) ∧
      (next.map g).sum = (accounts.map f).sum := by
  obtain ⟨hn1,hs1,he1⟩ := support_insert accounts f hn hs fromAddr
  obtain ⟨hn2,hs2,he2⟩ := support_insert (accounts.insert fromAddr) f hn1 hs1 toAddr
  let next := (accounts.insert fromAddr).insert toAddr
  have hfrom : fromAddr ∈ next := by simp [next]
  have hto : toAddr ∈ next := by simp [next]
  refine ⟨next,hn2,?_,?_⟩
  · intro a ha
    have hf : a ≠ fromAddr := by intro he; subst a; exact ha hfrom
    have ht : a ≠ toAddr := by intro he; subst a; exact ha hto
    have hh := h a
    simp only [if_neg hf,if_neg ht,Nat.add_zero] at hh
    rw [hh]; exact hs2 a ha
  · have hh := sum_pointwise_balance next f g fromAddr toAddr amount h
    rw [sum_indicator next fromAddr amount hn2, sum_indicator next toAddr amount hn2,
      if_pos hfrom,if_pos hto] at hh
    have he : (next.map f).sum = (accounts.map f).sum := he2.trans he1
    omega

theorem token_transfer_coherent (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (token fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0)
    (amount : Nat) (ha : amount ≤ assetBalance s token fromAddr)
    (hf : fromAddr ≠ 0) (hto : toAddr ≠ 0) :
    ∃ accounts : List Address, accounts.Nodup ∧
      (∀ owner, owner ∉ accounts →
        assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount} token owner = 0) ∧
      (accounts.map (assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount} token)).sum < wordLimit ∧
      assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount} token 0 = 0 := by
  obtain ⟨_,_,accounts,hn,hs,hb,hzero⟩ := hap token hreg ht
  have ho : assetBalance s token fromAddr < wordLimit := by
    by_cases hm : fromAddr ∈ accounts
    · have hh := support_member_bound accounts (assetBalance s token) fromAddr hm; omega
    · rw [hs fromAddr hm]; exact (word_val_lt 0)
  have hr : fromAddr ≠ toAddr → assetBalance s token toAddr + amount < wordLimit :=
    token_coherent_credit_bound s env hap token fromAddr toAddr hreg ht amount ha
  let g := assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount} token
  have hg : ∀ x, g x + (if x = fromAddr then amount else 0) =
      assetBalance s token x + (if x = toAddr then amount else 0) := by
    intro x
    have hh := token_transfer_integer_effect s token fromAddr toAddr x amount ha ho hr
    dsimp only [indicator] at hh
    dsimp only [g]
    have hifrom : (if x = fromAddr then (amount : Int) else 0) =
        ((if x = fromAddr then amount else 0 : Nat) : Int) := by split <;> rfl
    have hito : (if x = toAddr then (amount : Int) else 0) =
        ((if x = toAddr then amount else 0 : Nat) : Int) := by split <;> rfl
    rw [hifrom,hito] at hh
    omega
  obtain ⟨next,hn',hs',he⟩ := support_transfer_preserved accounts (assetBalance s token) g hn hs fromAddr toAddr amount hg
  refine ⟨next,hn',hs',?_,?_⟩
  · rw [he]; exact hb
  · have hh := hg 0
    simp only [if_neg (Ne.symm hf),if_neg (Ne.symm hto),Nat.add_zero,hzero] at hh
    exact hh

theorem token_transfer_other_target (s : State) (token other fromAddr toAddr : Address)
    (amount : Nat) (hne : other ≠ token) :
    (tokenWordTransfer s.external token fromAddr toAddr amount).accountState other.val =
      s.external.accountState other.val := by
  have hv : other.val ≠ token.val := fun he => hne (Verity.Core.Address.ext he)
  funext k
  simp [tokenWordTransfer,writeExternal,hv]

theorem allowance_write_exact (s : State) (token owner spender x y : Address) (value : Nat) :
    assetAllowance {s with external := writeExternal s.external token.val (aslot owner spender) value}
      token x y = if x = owner ∧ y = spender then value else assetAllowance s token x y := by
  have hi : aslot x y = aslot owner spender ↔ x = owner ∧ y = spender := by
    constructor
    · exact aslot_injective x y owner spender
    · rintro ⟨rfl,rfl⟩; rfl
  simp [assetAllowance,writeExternal,hi]

theorem allowance_write_other_target (s : State) (token other owner spender : Address)
    (value : Nat) (hne : other ≠ token) :
    (writeExternal s.external token.val (aslot owner spender) value).accountState other.val =
      s.external.accountState other.val := by
  have hv : other.val ≠ token.val := fun he => hne (Verity.Core.Address.ext he)
  funext k
  simp [writeExternal,hv]

theorem transfer_preserves_applicability (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (token fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0)
    (amount : Nat) (ha : amount ≤ assetBalance s token fromAddr)
    (hf : fromAddr ≠ 0) (hto : toAddr ≠ 0) :
    ExternalApplicability env {s with external := tokenWordTransfer s.external token fromAddr toAddr amount} := by
  intro a hregA hnonzero
  obtain ⟨hc,hi,hledger⟩ := hap a hregA hnonzero
  refine ⟨hc,hi,?_⟩
  by_cases he : a = token
  · subst a
    exact token_transfer_coherent s env hap token fromAddr toAddr hreg ht amount ha hf hto
  · have hw := token_transfer_other_target s token a fromAddr toAddr amount he
    have heq : assetBalance {s with external := tokenWordTransfer s.external token fromAddr toAddr amount} a =
        assetBalance s a := by funext x; simp only [assetBalance,hw]
    simpa only [heq] using hledger

theorem allowance_write_preserves_applicability (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (token owner spender : Address) (value : Nat) :
    ExternalApplicability env {s with external := writeExternal s.external token.val (aslot owner spender) value} := by
  intro a hregA hnonzero
  obtain ⟨hc,hi,accounts,hn,hs,hb,hz⟩ := hap a hregA hnonzero
  have he (x : Address) :
        assetBalance {s with external := writeExternal s.external token.val (aslot owner spender) value} a x =
          assetBalance s a x := by
      by_cases ht : a = token
      · subst a; exact balance_after_allowance_write _ _ _ _ _ _
      · have hw := allowance_write_other_target s token a owner spender value ht
        simp only [assetBalance,hw]
  have heq := funext he
  exact ⟨hc,hi,accounts,hn,by simpa only [heq] using hs,
    by simpa only [heq] using hb,by simpa only [heq] using hz⟩

theorem safeTransfer_applicability (s t : State) (env : Environment)
    (hap : ExternalApplicability env s) (token fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0) (amount : Nat)
    (ha : amount < wordLimit)
    (h : safeTransfer env token fromAddr toAddr amount s = .ok ((),t)) :
    ExternalApplicability env t ∧
    (∀ x, (assetBalance t token x : Int) - assetBalance s token x =
      indicator x toAddr amount - indicator x fromAddr amount) ∧
    (∀ other owner spender, assetAllowance t other owner spender = assetAllowance s other owner spender) := by
  obtain ⟨_,_,accounts,hn,hs,hb,hz⟩ := hap token hreg ht
  have ho : assetBalance s token fromAddr < wordLimit := by
    by_cases hm : fromAddr ∈ accounts
    · have hh := support_member_bound accounts (assetBalance s token) fromAddr hm; omega
    · rw [hs fromAddr hm]; exact word_val_lt 0
  obtain ⟨hc,hnotself,he,hpay,hnxt⟩ := safeTransfer_success _ _ _ _ _ _ _ ha ho h
  have hef : fromAddr ≠ 0 ∧ toAddr ≠ 0 := by simpa using he
  rw [hnxt]
  refine ⟨transfer_preserves_applicability s env hap token fromAddr toAddr hreg ht amount hpay hef.1 hef.2,?_,?_⟩
  · intro x
    exact token_transfer_integer_effect s token fromAddr toAddr x amount hpay ho
      (token_coherent_credit_bound s env hap token fromAddr toAddr hreg ht amount hpay)
  · intro other owner spender
    by_cases htgt : other = token
    · subst other; exact transfer_allowance_frame _ _ _ _ _ _ _
    · have hw := token_transfer_other_target s token other fromAddr toAddr amount htgt
      simp only [assetAllowance,hw]

theorem safeTransferFrom_accounting (s t : State) (env : Environment)
    (hap : ExternalApplicability env s) (token spender fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0) (amount : Nat)
    (ha : amount < wordLimit) (hal : assetAllowance s token fromAddr spender < wordLimit)
    (h : safeTransferFrom env token spender fromAddr toAddr amount s = .ok ((),t)) :
    ExternalApplicability env t ∧
    (∀ x, (assetBalance t token x : Int) - assetBalance s token x =
      indicator x toAddr amount - indicator x fromAddr amount) ∧
    (∀ other owner sp,
      assetAllowance t other owner sp =
        if other = token ∧ owner = fromAddr ∧ sp = spender ∧
            assetAllowance s token fromAddr spender ≠ wordLimit-1 then
          assetAllowance s other owner sp - amount else assetAllowance s other owner sp) := by
  obtain ⟨_,_,accounts,hn,hs,hb,hz⟩ := hap token hreg ht
  have ho : assetBalance s token fromAddr < wordLimit := by
    by_cases hm : fromAddr ∈ accounts
    · have hh := support_member_bound accounts (assetBalance s token) fromAddr hm; omega
    · rw [hs fromAddr hm]; exact word_val_lt 0
  obtain ⟨hc,hnotself,he,hpay,hnext⟩ := safeTransferFrom_success _ _ _ _ _ _ _ _ ha ho hal h
  have hef : fromAddr ≠ 0 ∧ toAddr ≠ 0 := by simpa using he
  by_cases hi : assetAllowance s token fromAddr spender = wordLimit-1
  · rw [if_pos hi] at hnext
    rw [hnext]
    refine ⟨transfer_preserves_applicability s env hap token fromAddr toAddr hreg ht amount hpay hef.1 hef.2,?_,?_⟩
    · intro x
      exact token_transfer_integer_effect s token fromAddr toAddr x amount hpay ho
        (token_coherent_credit_bound s env hap token fromAddr toAddr hreg ht amount hpay)
    · intro other owner sp
      simp only [hi,ne_self_iff_false,and_false,if_false]
      by_cases htgt : other = token
      · subst other; exact transfer_allowance_frame _ _ _ _ _ _ _
      · have hw := token_transfer_other_target s token other fromAddr toAddr amount htgt
        simp only [assetAllowance,hw]
  · rw [if_neg hi] at hnext
    obtain ⟨hsp,hnext⟩ := hnext
    let m : State := {s with
      external := writeExternal s.external token.val (aslot fromAddr spender)
        (assetAllowance s token fromAddr spender - amount)}
    have hapm : ExternalApplicability env m := allowance_write_preserves_applicability s env hap token fromAddr spender _
    have hbm (x : Address) : assetBalance m token x = assetBalance s token x :=
      balance_after_allowance_write s token fromAddr spender x _
    rw [hnext]
    refine ⟨transfer_preserves_applicability m env hapm token fromAddr toAddr hreg ht amount
      (by rw [hbm]; exact hpay) hef.1 hef.2,?_,?_⟩
    · intro x
      have hh := token_transfer_integer_effect m token fromAddr toAddr x amount
        (by rw [hbm]; exact hpay) (by rw [hbm]; exact ho)
        (token_coherent_credit_bound m env hapm token fromAddr toAddr hreg ht amount (by rw [hbm]; exact hpay))
      rw [hbm] at hh
      exact hh
    · intro other owner sp
      have hw : assetAllowance {s with external := tokenWordTransfer m.external token fromAddr toAddr amount}
          other owner sp = assetAllowance m other owner sp := by
        by_cases htgt : other = token
        · subst other; exact transfer_allowance_frame _ _ _ _ _ _ _
        · have hworld := token_transfer_other_target m token other fromAddr toAddr amount htgt
          simp only [assetAllowance,hworld]
      change assetAllowance {s with external := tokenWordTransfer m.external token fromAddr toAddr amount}
        other owner sp = _
      rw [hw]
      by_cases htgt : other = token
      · subst other
        have hh := allowance_write_exact s token fromAddr spender owner sp
          (assetAllowance s token fromAddr spender - amount)
        change assetAllowance m token owner sp = _
        rw [hh]
        by_cases howner : owner = fromAddr <;> by_cases hsp : sp = spender <;>
          simp [howner,hsp,hi]
      · have hworld := allowance_write_other_target s token other fromAddr spender
          (assetAllowance s token fromAddr spender - amount) htgt
        rw [if_neg (by tauto : ¬(other = token ∧ owner = fromAddr ∧ sp = spender ∧
          assetAllowance s token fromAddr spender ≠ wordLimit-1))]
        exact congrFun hworld (aslot owner sp)

theorem registered_asset_balance_bounded (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (token owner : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0) :
    assetBalance s token owner < wordLimit := by
  obtain ⟨_,_,accounts,hn,hs,hb,hz⟩ := hap token hreg ht
  by_cases hm : owner ∈ accounts
  · have hh := support_member_bound accounts (assetBalance s token) owner hm; omega
  · rw [hs owner hm]; exact word_val_lt 0

theorem safeTransferFrom_allowance_integer (s t : State) (env : Environment)
    (hap : ExternalApplicability env s) (token spender fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0) (amount : Nat)
    (ha : amount < wordLimit) (hal : assetAllowance s token fromAddr spender < wordLimit)
    (h : safeTransferFrom env token spender fromAddr toAddr amount s = .ok ((),t)) :
    ∀ other owner sp,
      if assetAllowance s other owner sp = wordLimit-1 then assetAllowance t other owner sp = wordLimit-1
      else (assetAllowance t other owner sp : Int) - assetAllowance s other owner sp =
        -(if other = token ∧ owner = fromAddr ∧ sp = spender then (amount : Int) else 0) := by
  have hc := (safeTransferFrom_accounting s t env hap token spender fromAddr toAddr hreg ht amount ha hal h).2.2
  have hs := safeTransferFrom_success env token spender fromAddr toAddr amount s t ha
    (registered_asset_balance_bounded s env hap token fromAddr hreg ht) hal h
  intro other owner sp
  by_cases he : other = token ∧ owner = fromAddr ∧ sp = spender
  · rcases he with ⟨hother,howner,hspender⟩
    subst other; subst owner; subst sp
    by_cases hi : assetAllowance s token fromAddr spender = wordLimit-1
    · simp only [if_pos hi]
      rw [hc]; simp [hi]
    · have hs' := hs.2.2.2.2
      rw [if_neg hi] at hs'
      have hsp := hs'.1
      rw [if_neg hi,hc]
      simp only [and_self,ne_eq,hi,not_false_eq_true,and_true,if_true]
      omega
  · have hh := hc other owner sp
    rw [if_neg (by tauto : ¬(other = token ∧ owner = fromAddr ∧ sp = spender ∧
      assetAllowance s token fromAddr spender ≠ wordLimit-1))] at hh
    rw [hh,if_neg he]
    split <;> simp_all

theorem safeTransferFrom_allowance_bounds (s t : State) (env : Environment)
    (hap : ExternalApplicability env s) (token spender fromAddr toAddr : Address)
    (hreg : (s.config.assets token).asset = token) (ht : token ≠ 0) (amount : Nat)
    (ha : amount < wordLimit) (hal : ∀ other owner sp, assetAllowance s other owner sp < wordLimit)
    (h : safeTransferFrom env token spender fromAddr toAddr amount s = .ok ((),t)) :
    ∀ other owner sp, assetAllowance t other owner sp < wordLimit := by
  have hc := (safeTransferFrom_accounting s t env hap token spender fromAddr toAddr hreg ht amount ha (hal _ _ _) h).2.2
  intro other owner sp
  rw [hc]
  have hh := hal other owner sp
  split <;> omega

-- A fee callee's own mutable storage cannot collide with a registered ERC20.
theorem module_world_preserves_applicability (s : State) (env : Environment)
    (hap : ExternalApplicability env s) (moduleAddr : Address) (hm : env.isToken moduleAddr = false)
    (moduleState : Nat → Nat) :
    ExternalApplicability env {s with
      external := {accountState := fun target k =>
        if target == moduleAddr.val then moduleState k else s.external.accountState target k}} := by
  intro a hreg hnonzero
  obtain ⟨hc,ht,hl⟩ := hap a hreg hnonzero
  have hne : a.val ≠ moduleAddr.val := by
    intro hval
    have he : a = moduleAddr := Verity.Core.Address.ext hval
    rw [he,hm] at ht; cases ht
  have hb : assetBalance {s with
      external := {accountState := fun target k =>
        if target == moduleAddr.val then moduleState k else s.external.accountState target k}} a = assetBalance s a := by
    funext x; simp [assetBalance,hne]
  exact ⟨hc,ht,by simpa only [hb] using hl⟩

#print axioms registered_asset_balance_bounded
#print axioms safeTransferFrom_allowance_integer
#print axioms safeTransferFrom_allowance_bounds
#print axioms module_world_preserves_applicability
#print axioms safeTransferFrom_accounting
#print axioms token_transfer_other_target
#print axioms allowance_write_exact
#print axioms allowance_write_other_target
#print axioms transfer_preserves_applicability
#print axioms allowance_write_preserves_applicability
#print axioms safeTransfer_applicability
#print axioms support_insert
#print axioms sum_indicator
#print axioms sum_pointwise_balance
#print axioms support_transfer_preserved
#print axioms token_transfer_coherent
#print axioms support_pair_bound
#print axioms token_transfer_balance
#print axioms token_transfer_integer_effect
#print axioms token_coherent_credit_bound
#print axioms validatePriceDeviation_success
#print axioms bslot_injective
#print axioms cantor_injective
#print axioms aslot_injective
#print axioms transfer_allowance_frame
#print axioms safeTransferFrom_success
end Benchmark.Cases.KPK.SharesSettlementAccounting
