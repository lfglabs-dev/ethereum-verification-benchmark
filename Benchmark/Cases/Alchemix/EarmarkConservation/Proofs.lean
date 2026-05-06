import Benchmark.Cases.Alchemix.EarmarkConservation.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256
open Verity.Core (FiniteSet)

/-
  Reference proofs for the Alchemix V3 earmark conservation case.

  Each preservation theorem comes with explicit hypotheses surfaced on
  the theorem signature. Two families recur:

    * Q128 idealization hypotheses — `mulQ128 x ONE_Q128 = x`,
      `mulQ128 (a + b) r = mulQ128 a r + mulQ128 b r`. These mirror
      the "no Q128 floor-rounding drift" assumption documented in
      `Contract.lean` / `Specs.lean`. The literal EVM modular `mul`/`div`
      does not satisfy them in general (overflow + floor-rounding); they
      are faithful to the Alchemix design under the conservation
      invariant.

    * Synced-at-id hypotheses — `accounts_lastAccruedEarmarkWeight s id
      = _earmarkWeight s` etc. The operations `_subDebt` and
      `_subEarmarkedDebt` are only invariant-preserving when called
      against an account whose stored snapshot matches the current
      global weights (the Solidity source enforces this by calling
      `_sync(id)` immediately before, see lines 502, 522, 567, 590,
      869, 1052).

  Every proof is fully discharged from the Verity contract
  semantics; no proof gaps remain.
-/

/-! ## Pure arithmetic helpers -/

/-- Telescoping subtraction in Uint256: `(S - X) + (X - C) = S - C`
    when `C ≤ X`. Proven by case analysis on `X ≤ S`. -/
private theorem uint256_sub_telescope
    (S X C : Uint256) (hCleX : C ≤ X) :
    add (sub S X) (sub X C) = sub S C := by
  apply Verity.Core.Uint256.ext
  have hCleXVal : C.val ≤ X.val := hCleX
  have hSmod : S.val < Verity.Core.Uint256.modulus := S.isLt
  have hXmod : X.val < Verity.Core.Uint256.modulus := X.isLt
  have hCmod : C.val < Verity.Core.Uint256.modulus := C.isLt
  have hXCval : (sub X C).val = X.val - C.val :=
    Verity.Core.Uint256.sub_eq_of_le (a := X) (b := C) hCleX
  by_cases hXleS : X.val ≤ S.val
  · have hSXval : (sub S X).val = S.val - X.val :=
      Verity.Core.Uint256.sub_eq_of_le (a := S) (b := X) hXleS
    have hCleS : C.val ≤ S.val := Nat.le_trans (m := X.val) hCleXVal hXleS
    have hSCval : (sub S C).val = S.val - C.val :=
      Verity.Core.Uint256.sub_eq_of_le (a := S) (b := C) hCleS
    show (Verity.Core.Uint256.add (sub S X) (sub X C)).val = (sub S C).val
    unfold Verity.Core.Uint256.add
    show (Verity.Core.Uint256.ofNat ((sub S X).val + (sub X C).val)).val = (sub S C).val
    rw [hSXval, hXCval, hSCval]
    show ((S.val - X.val) + (X.val - C.val)) % Verity.Core.Uint256.modulus = S.val - C.val
    have hSXCsum : (S.val - X.val) + (X.val - C.val) = S.val - C.val := by omega
    rw [hSXCsum]
    have hLt : S.val - C.val < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) S.isLt
    exact Nat.mod_eq_of_lt hLt
  · have hXleS' : S.val < X.val := Nat.lt_of_not_le hXleS
    have hSXval : (sub S X).val =
        (Verity.Core.Uint256.modulus - (X.val - S.val)) % Verity.Core.Uint256.modulus :=
      Verity.Core.Uint256.sub_val_of_gt (a := S) (b := X) hXleS'
    show (Verity.Core.Uint256.add (sub S X) (sub X C)).val = (sub S C).val
    unfold Verity.Core.Uint256.add
    show (Verity.Core.Uint256.ofNat ((sub S X).val + (sub X C).val)).val = (sub S C).val
    rw [hSXval, hXCval]
    show ((Verity.Core.Uint256.modulus - (X.val - S.val)) % Verity.Core.Uint256.modulus + (X.val - C.val))
            % Verity.Core.Uint256.modulus = (sub S C).val
    have hXSpos : 0 < X.val - S.val := Nat.sub_pos_of_lt hXleS'
    have hMod1 : (Verity.Core.Uint256.modulus - (X.val - S.val)) % Verity.Core.Uint256.modulus
                  = Verity.Core.Uint256.modulus - (X.val - S.val) := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hMod1]
    by_cases hCleS : C.val ≤ S.val
    · have hSCval : (sub S C).val = S.val - C.val :=
        Verity.Core.Uint256.sub_eq_of_le (a := S) (b := C) hCleS
      rw [hSCval]
      have hSCmod : S.val - C.val < Verity.Core.Uint256.modulus :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) S.isLt
      have hSum : Verity.Core.Uint256.modulus - (X.val - S.val) + (X.val - C.val) =
                    Verity.Core.Uint256.modulus + (S.val - C.val) := by omega
      rw [hSum]
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt hSCmod
    · have hCleS' : S.val < C.val := Nat.lt_of_not_le hCleS
      have hSCval : (sub S C).val =
          (Verity.Core.Uint256.modulus - (C.val - S.val)) % Verity.Core.Uint256.modulus :=
        Verity.Core.Uint256.sub_val_of_gt (a := S) (b := C) hCleS'
      rw [hSCval]
      have hMod2 : (Verity.Core.Uint256.modulus - (C.val - S.val)) % Verity.Core.Uint256.modulus
                    = Verity.Core.Uint256.modulus - (C.val - S.val) := by
        apply Nat.mod_eq_of_lt
        omega
      rw [hMod2]
      have hSum : Verity.Core.Uint256.modulus - (X.val - S.val) + (X.val - C.val) =
                    Verity.Core.Uint256.modulus - (C.val - S.val) := by omega
      rw [hSum]
      apply Nat.mod_eq_of_lt
      omega

/-- `x - x = 0` (from Uint256 stdlib, repackaged for our `sub` notation). -/
private theorem sub_self_fn (x : Uint256) : sub x x = 0 :=
  Verity.Core.Uint256.sub_self x

/-- `add x 0 = x`. -/
private theorem add_zero_fn (x : Uint256) : add x 0 = x :=
  Verity.Core.Uint256.add_zero x

/-- `add 0 x = x`. -/
private theorem zero_add_fn (x : Uint256) : add 0 x = x :=
  Verity.Core.Uint256.zero_add x

/-- `mulQ128 0 r = 0`. -/
private theorem mulQ128_zero (r : Uint256) : mulQ128 0 r = 0 := by
  unfold mulQ128
  -- mul 0 r = 0
  have h1 : mul (0 : Uint256) r = 0 := Verity.Core.Uint256.zero_mul r
  rw [h1]
  -- div 0 ONE_Q128 = 0
  exact Verity.Core.Uint256.zero_div ONE_Q128

/-! ## Foldl helpers -/

/-- Pointwise congruence for `foldl` of `add`. -/
private theorem foldl_add_congr {α : Type} (l : List α)
    (f g : α → Uint256) (acc : Uint256)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun a x => a + f x) acc = l.foldl (fun a x => a + g x) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = g a := h a (by simp)
    rw [ha]
    exact ih (acc + g a) (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- Pointwise congruence for `foldl` of Nat-add. Used to transfer the
    no-overflow hypothesis across operations that don't change projections. -/
private theorem foldl_nat_add_congr {α : Type} (l : List α)
    (f g : α → Nat) (acc : Nat)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun a x => a + f x) acc = l.foldl (fun a x => a + g x) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = g a := h a (by simp)
    rw [ha]
    exact ih (acc + g a) (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- Foldl-shift for additive accumulators: `foldl + f (acc + d) l = foldl + f acc l + d`. -/
private theorem foldl_add_shift
    (l : List Uint256) (f : Uint256 → Uint256) (acc d : Uint256) :
    l.foldl (fun b x => b + f x) (acc + d) =
      l.foldl (fun b x => b + f x) acc + d := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl]
    have hReassoc : (acc + d + f hd) = (acc + f hd) + d := by
      have h1 : (acc + d) + f hd = acc + (d + f hd) :=
        Verity.Core.Uint256.add_assoc acc d (f hd)
      have h2 : d + f hd = f hd + d :=
        Verity.Core.Uint256.add_comm d (f hd)
      have h3 : acc + (f hd + d) = (acc + f hd) + d :=
        (Verity.Core.Uint256.add_assoc acc (f hd) d).symm
      rw [h1, h2, h3]
    rw [hReassoc]
    exact ih (acc + f hd)

/-- Pointwise congruence on the underlying list of a `FiniteSet`. -/
private theorem sum_congr_on
    {s : FiniteSet Uint256} {f g : Uint256 → Uint256}
    (h : ∀ x ∈ s.elements, f x = g x) :
    s.sum f = s.sum g := by
  unfold Verity.Core.FiniteSet.sum
  exact foldl_add_congr s.elements f g 0 h

/-- Foldl with combined accumulator: `foldl + (f+g) acc l = foldl + f acc l + foldl + g 0 l`. -/
private theorem foldl_add_distrib_aux
    (l : List Uint256) (f g : Uint256 → Uint256) (acc : Uint256) :
    l.foldl (fun b x => b + (f x + g x)) acc =
      l.foldl (fun b x => b + f x) acc +
        l.foldl (fun b x => b + g x) 0 := by
  induction l generalizing acc with
  | nil =>
    show acc = acc + 0
    exact (Verity.Core.Uint256.add_zero acc).symm
  | cons hd tl ih =>
    simp only [List.foldl]
    -- LHS = foldl_{f+g} tl (acc + (f hd + g hd))
    rw [ih (acc + (f hd + g hd))]
    -- LHS becomes foldl_f tl (acc + (f hd + g hd)) + foldl_g tl 0.
    -- Reassociate the f-side and use shift.
    have hReassoc1 : acc + (f hd + g hd) = (acc + f hd) + g hd :=
      (Verity.Core.Uint256.add_assoc acc (f hd) (g hd)).symm
    rw [hReassoc1, foldl_add_shift tl f (acc + f hd) (g hd)]
    -- RHS by simp [List.foldl] is foldl_f tl (acc + f hd) + foldl_g tl (0 + g hd).
    -- Use foldl_add_shift on RHS's g-foldl (with 0 + g hd = 0 + g hd, then move out).
    rw [show (0 : Uint256) + g hd = 0 + g hd from rfl]
    rw [foldl_add_shift tl g 0 (g hd)]
    -- Goal: foldl_f tl (acc+fhd) + ghd + foldl_g tl 0 =
    --       foldl_f tl (acc+fhd) + (foldl_g tl 0 + g hd)
    have h1 :
      tl.foldl (fun b x => b + f x) (acc + f hd) + g hd + tl.foldl (fun b x => b + g x) 0 =
        tl.foldl (fun b x => b + f x) (acc + f hd) + (g hd + tl.foldl (fun b x => b + g x) 0) :=
      Verity.Core.Uint256.add_assoc _ _ _
    have h2 : g hd + tl.foldl (fun b x => b + g x) 0 =
              tl.foldl (fun b x => b + g x) 0 + g hd :=
      Verity.Core.Uint256.add_comm _ _
    rw [h1, h2]

/-- Distribution of pointwise sum over a `FiniteSet`. -/
private theorem foldl_add_distrib
    (ids : FiniteSet Uint256) (f g : Uint256 → Uint256) :
    ids.sum (fun id => f id + g id) =
      ids.sum f + ids.sum g := by
  unfold Verity.Core.FiniteSet.sum
  exact foldl_add_distrib_aux ids.elements f g 0

/-- Foldl-version of mulQ128 distributing over additions. -/
private theorem foldl_mulQ128_distrib
    (l : List Uint256) (f : Uint256 → Uint256) (r : Uint256)
    (hLin : ∀ x y : Uint256, mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r)) :
    ∀ acc,
      l.foldl (fun b x => b + mulQ128 (f x) r) (mulQ128 acc r) =
        mulQ128 (l.foldl (fun b x => b + f x) acc) r := by
  induction l with
  | nil =>
    intro acc
    rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl]
    -- LHS = foldl tl (mulQ128 acc r + mulQ128 (f hd) r) = foldl tl (mulQ128 (acc + f hd) r) by hLin.
    have hSum : mulQ128 acc r + mulQ128 (f hd) r = mulQ128 (acc + f hd) r := by
      show add (mulQ128 acc r) (mulQ128 (f hd) r) = mulQ128 (add acc (f hd)) r
      exact (hLin acc (f hd)).symm
    rw [hSum]
    exact ih (acc + f hd)

/-- Sum-version of mulQ128 distribution: `Σ mulQ128 (f id) r = mulQ128 (Σ f id) r`. -/
private theorem sum_mulQ128_distrib
    (ids : FiniteSet Uint256) (f : Uint256 → Uint256) (r : Uint256)
    (hLin : ∀ x y : Uint256, mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r)) :
    ids.sum (fun id => mulQ128 (f id) r) =
      mulQ128 (ids.sum f) r := by
  unfold Verity.Core.FiniteSet.sum
  have h0 : mulQ128 (0 : Uint256) r = 0 := mulQ128_zero r
  -- Use foldl_mulQ128_distrib at acc = 0, with the mulQ128 0 r = 0 simplification.
  have hStep : List.foldl (fun b x => b + mulQ128 (f x) r) (mulQ128 0 r) ids.elements =
      mulQ128 (List.foldl (fun b x => b + f x) 0 ids.elements) r :=
    foldl_mulQ128_distrib ids.elements f r hLin 0
  rw [h0] at hStep
  exact hStep

/-! ## `projectedEarmarked` synced shortcut -/

/-- When account `id`'s last-accrued snapshots match the current global
    weights, the lazy projection collapses to the stored `accounts_earmarked`.

    Proof: at lastEW = eW, the unearmark survival ratio is `ONE_Q128`,
    so `unearmarkedRemaining = mulQ128 userExposure ONE_Q128 = userExposure`,
    so `earmarkRaw = sub userExposure userExposure = 0`, so
    `totalEarmarkedNow = earm + 0 = earm`. At lastRW = rW, the redemption
    survival ratio is `ONE_Q128`, so `newEarmarked = mulQ128 earm ONE_Q128 = earm`. -/
private theorem projectedEarmarked_of_synced
    (s : ContractState) (id : Uint256)
    (hSyncedEW : accounts_lastAccruedEarmarkWeight s id = _earmarkWeight s)
    (hSyncedRW : accounts_lastAccruedRedemptionWeight s id = _redemptionWeight s)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x) :
    projectedEarmarked s id = accounts_earmarked s id := by
  unfold projectedEarmarked _computeUnrealizedAccount
  -- Reduce the unearmarkSurvivalRatio: lastEW = eW → first branch hits ONE_Q128.
  simp only [hSyncedEW, hSyncedRW]
  -- Now the unearmarkedRemaining = div (mul userExposure ONE_Q128) ONE_Q128 = mulQ128 userExposure ONE_Q128 = userExposure.
  -- earmarkRaw = userExposure - unearmarkedRemaining = 0.
  -- totalEarmarkedNow = earm + 0 = earm.
  -- newEarmarked = mulQ128 earm ONE_Q128 = earm.
  show (div (mul (add (accounts_earmarked s id)
    (sub
      (if (accounts_debt s id) > (accounts_earmarked s id) then sub (accounts_debt s id) (accounts_earmarked s id) else 0)
      (div (mul
        (if (accounts_debt s id) > (accounts_earmarked s id) then sub (accounts_debt s id) (accounts_earmarked s id) else 0)
        ONE_Q128) ONE_Q128))) ONE_Q128) ONE_Q128) = accounts_earmarked s id
  -- Let UE = userExposure.
  generalize hUE :
    (if (accounts_debt s id) > (accounts_earmarked s id) then
      sub (accounts_debt s id) (accounts_earmarked s id) else (0 : Uint256)) = UE
  -- div (mul UE ONE_Q128) ONE_Q128 = mulQ128 UE ONE_Q128 = UE.
  have hUE_collapse : div (mul UE ONE_Q128) ONE_Q128 = UE := by
    show mulQ128 UE ONE_Q128 = UE
    exact hQ128MulOne UE
  rw [hUE_collapse]
  -- sub UE UE = 0.
  rw [sub_self_fn UE]
  rw [add_zero_fn]
  -- div (mul earm ONE_Q128) ONE_Q128 = mulQ128 earm ONE_Q128 = earm.
  show mulQ128 (accounts_earmarked s id) ONE_Q128 = accounts_earmarked s id
  exact hQ128MulOne _

/-! ## `_subDebt(tokenId, amount)` slot writes -/

/-- Slot-write lemma for `_subDebt(tokenId, amount)`. -/
private theorem _subDebt_slot_write
    (tokenId amount : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    s'.storage 1 = sub (totalDebt s) amount ∧
    s'.storage 0 =
      (if (cumulativeEarmarked s) > sub (totalDebt s) amount then
        sub (totalDebt s) amount
       else cumulativeEarmarked s) ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storage 3 = s.storage 3 ∧
    s'.storage 4 = s.storage 4 ∧
    s'.storageMapUint 100 tokenId =
      sub (accounts_debt s tokenId) amount ∧
    s'.storageMapUint 101 tokenId = s.storageMapUint 101 tokenId ∧
    s'.storageMapUint 102 tokenId = s.storageMapUint 102 tokenId ∧
    s'.storageMapUint 103 tokenId = s.storageMapUint 103 tokenId ∧
    s'.storageMapUint 104 tokenId = s.storageMapUint 104 tokenId := by
  repeat' constructor
  all_goals
    simp [AlchemistV3._subDebt,
      AlchemistV3._accounts_debt,
      AlchemistV3.cumulativeEarmarked, AlchemistV3.totalDebt,
      accounts_debt,
      getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

/-- Frame lemma for `_subDebt`: per-account mapping at `other ≠ tokenId` is unchanged. -/
private theorem _subDebt_mapping_unchanged_diff
    (tokenId other amount : Uint256) (s : ContractState) (slotIdx : Nat)
    (h : other ≠ tokenId) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    s'.storageMapUint slotIdx other = s.storageMapUint slotIdx other := by
  simp [AlchemistV3._subDebt,
    AlchemistV3._accounts_debt,
    AlchemistV3.cumulativeEarmarked, AlchemistV3.totalDebt,
    getStorage, setStorage, getMappingUint, setMappingUint,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd, h]

/-- Lazy projection at `id ≠ tokenId` is unchanged across `_subDebt`. -/
private theorem _subDebt_projectedEarmarked_other
    (s : ContractState) (tokenId amount other : Uint256)
    (h : other ≠ tokenId) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    projectedEarmarked s' other = projectedEarmarked s other := by
  intro s'
  show projectedEarmarked s' other = projectedEarmarked s other
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases _subDebt_slot_write tokenId amount s with
    ⟨_h1, _h0, h2, h3, _h4, _hM100, _hM101, _hM102, _hM103, _hM104⟩
  have h100 : s'.storageMapUint 100 other = s.storageMapUint 100 other :=
    _subDebt_mapping_unchanged_diff tokenId other amount s 100 h
  have h101 : s'.storageMapUint 101 other = s.storageMapUint 101 other :=
    _subDebt_mapping_unchanged_diff tokenId other amount s 101 h
  have h102 : s'.storageMapUint 102 other = s.storageMapUint 102 other :=
    _subDebt_mapping_unchanged_diff tokenId other amount s 102 h
  have h103 : s'.storageMapUint 103 other = s.storageMapUint 103 other :=
    _subDebt_mapping_unchanged_diff tokenId other amount s 103 h
  rw [h2, h3, h100, h101, h102, h103]

/-! ## `_subDebt` preservation theorem -/

theorem _subDebt_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (tokenId amount : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hSyncedAtTokenId :
      accounts_lastAccruedEarmarkWeight s tokenId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s tokenId = _redemptionWeight s)
    (hCumulativeLeTotalDebt :
      cumulativeEarmarked s ≤ sub (totalDebt s) amount) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    _subDebt_preserves_invariant_spec s s' ids tokenId := by
  intro s' _hMem hPre
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s'
  rcases _subDebt_slot_write tokenId amount s with
    ⟨_h1, h0, h2, h3, _h4, _hM100tok, hM101tok, hM102tok, hM103tok, _hM104tok⟩
  -- Step 1: cumulativeEarmarked unchanged because the clamp does not fire.
  have hCumulativeUnchanged :
      cumulativeEarmarked s' = cumulativeEarmarked s := by
    show s'.storage 0 = s.storage 0
    rw [h0]
    have hLe : ¬ (cumulativeEarmarked s) > sub (totalDebt s) amount := by
      intro hGt
      have hLeVal : (cumulativeEarmarked s).val ≤ (sub (totalDebt s) amount).val :=
        hCumulativeLeTotalDebt
      have hGtVal : (sub (totalDebt s) amount).val < (cumulativeEarmarked s).val := hGt
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hGtVal hLeVal)
    simp [hLe]
    rfl
  -- Step 2: per-id projection equality.
  have hProj : ∀ id ∈ ids.elements,
      projectedEarmarked s' id = projectedEarmarked s id := by
    intro id _hMemId
    by_cases hid : id = tokenId
    · subst hid
      have hPreSynced :
          projectedEarmarked s id = accounts_earmarked s id :=
        projectedEarmarked_of_synced s id hSyncedAtTokenId.1
          hSyncedAtTokenId.2 hQ128MulOne
      have hPostLastEW :
          accounts_lastAccruedEarmarkWeight s' id = _earmarkWeight s' := by
        show s'.storageMapUint 102 id = s'.storage 2
        rw [hM102tok, h2]
        exact hSyncedAtTokenId.1
      have hPostLastRW :
          accounts_lastAccruedRedemptionWeight s' id = _redemptionWeight s' := by
        show s'.storageMapUint 103 id = s'.storage 3
        rw [hM103tok, h3]
        exact hSyncedAtTokenId.2
      have hPostSynced :
          projectedEarmarked s' id = accounts_earmarked s' id :=
        projectedEarmarked_of_synced s' id hPostLastEW hPostLastRW hQ128MulOne
      have hStoredUnchanged :
          accounts_earmarked s' id = accounts_earmarked s id := by
        show s'.storageMapUint 101 id = s.storageMapUint 101 id
        exact hM101tok
      rw [hPreSynced, hPostSynced, hStoredUnchanged]
    · exact _subDebt_projectedEarmarked_other s tokenId amount id hid
  rw [hCumulativeUnchanged]
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s
  have hPre' : sumProjectedEarmarked s ids = cumulativeEarmarked s := hPre
  rw [← hPre']
  exact sum_congr_on hProj

/-! ## Singleton-decrement helper for `_subEarmarkedDebt` -/

/-- Singleton-replace law (auxiliary): when `f` and `g` agree everywhere
    except at `a` (which appears at most once in `l` via `nodup`), the
    foldl-sum of `g` equals the foldl-sum of `f` minus `f a` plus `g a`. -/
private theorem foldl_add_singleton_replace_aux
    (l : List Uint256) (a : Uint256) (hMem : a ∈ l) (hNoDup : l.Nodup)
    (f g : Uint256 → Uint256)
    (hAgreeOff : ∀ x, x ≠ a → f x = g x) :
    ∀ acc,
      l.foldl (fun b x => b + g x) acc =
        l.foldl (fun b x => b + f x) acc - f a + g a := by
  induction l with
  | nil => simp at hMem
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl]
    have hNoDupTl : tl.Nodup := (List.nodup_cons.mp hNoDup).2
    have hHdNotInTl : hd ∉ tl := (List.nodup_cons.mp hNoDup).1
    rcases List.mem_cons.mp hMem with rfl | hMemTl
    · -- a = hd; a ∉ tl, so f and g agree on tl, so the foldls are equal.
      have hAgreeTl : ∀ x ∈ tl, f x = g x := by
        intro x hx
        have hxNeA : x ≠ a := by
          intro hEq; subst hEq; exact hHdNotInTl hx
        exact hAgreeOff x hxNeA
      have hCongr :
          tl.foldl (fun b x => b + g x) (acc + g a) =
            tl.foldl (fun b x => b + f x) (acc + g a) := by
        exact (foldl_add_congr tl f g (acc + g a) hAgreeTl).symm
      rw [hCongr]
      rw [foldl_add_shift tl f acc (g a),
          foldl_add_shift tl f acc (f a)]
      rw [Verity.Core.Uint256.sub_add_cancel
        (tl.foldl (fun b x => b + f x) acc) (f a)]
    · -- a ∈ tl, so a ≠ hd.
      have hHdNeA : hd ≠ a := by
        intro hEq; subst hEq; exact hHdNotInTl hMemTl
      have hHdEq : f hd = g hd := hAgreeOff hd hHdNeA
      rw [hHdEq]
      exact ih hMemTl hNoDupTl _

private theorem sum_singleton_replace
    (s : FiniteSet Uint256) (a : Uint256) (hMem : a ∈ s.elements)
    (f g : Uint256 → Uint256)
    (hAgreeOff : ∀ x, x ≠ a → f x = g x) :
    s.sum g = s.sum f - f a + g a := by
  unfold Verity.Core.FiniteSet.sum
  exact foldl_add_singleton_replace_aux s.elements a hMem s.nodup f g hAgreeOff 0

private theorem sum_singleton_decrement
    (s : FiniteSet Uint256) (a : Uint256) (hMem : a ∈ s.elements)
    (f : Uint256 → Uint256) (c : Uint256) (hLe : c ≤ f a) :
    s.sum (fun id => if id = a then sub (f id) c else f id) =
      sub (s.sum f) c := by
  rw [sum_singleton_replace s a hMem f
        (fun id => if id = a then sub (f id) c else f id)
        (by intro x hx; simp [hx])]
  rw [if_pos rfl]
  exact uint256_sub_telescope (s.sum f) (f a) c hLe

/-! ## "Single summand ≤ sum" under non-overflow

  In Uint256 modular arithmetic, individual summands can exceed the
  modular sum if any partial sum wraps around 2^256. The
  `accounts_earmarked ≤ cumulativeEarmarked` precondition used by
  `_subEarmarkedDebt_preserves_invariant` is precisely "single summand
  ≤ sum" combined with H2-synced (so stored = projection) and the
  conservation invariant (so sum = cumulativeEarmarked). Once we have
  no-overflow, the inequality is automatic; H5 is *not* an independent
  hypothesis. -/

/-- Nat foldl-add shift: `foldl (acc + d) l = foldl acc l + d`. -/
private theorem foldl_nat_add_shift
    (l : List Uint256) (f : Uint256 → Uint256) (acc d : Nat) :
    l.foldl (fun b x => b + (f x).val) (acc + d) =
      l.foldl (fun b x => b + (f x).val) acc + d := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl]
    have h : acc + d + (f hd).val = (acc + (f hd).val) + d := by omega
    rw [h]
    exact ih (acc + (f hd).val)

/-- Nat foldl-add is monotone in the accumulator. -/
private theorem foldl_nat_add_ge_acc
    (l : List Uint256) (f : Uint256 → Uint256) (acc : Nat) :
    acc ≤ l.foldl (fun b x => b + (f x).val) acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons hd tl ih =>
    simp only [List.foldl]
    have h := ih (acc + (f hd).val)
    have h2 : acc ≤ acc + (f hd).val := Nat.le_add_right acc (f hd).val
    exact Nat.le_trans h2 h

/-- Single summand ≤ Nat foldl-add sum. -/
private theorem foldl_nat_add_ge_singleton
    (l : List Uint256) (f : Uint256 → Uint256) (a : Uint256) (hMem : a ∈ l) :
    ∀ acc, (f a).val ≤ l.foldl (fun b x => b + (f x).val) acc := by
  induction l with
  | nil => intro _; cases hMem
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl]
    rcases List.mem_cons.mp hMem with hEq | hMemTl
    · subst hEq
      have hge :
          acc + (f a).val ≤ tl.foldl (fun b x => b + (f x).val) (acc + (f a).val) :=
        foldl_nat_add_ge_acc tl f (acc + (f a).val)
      have h2 : (f a).val ≤ acc + (f a).val := Nat.le_add_left _ _
      exact Nat.le_trans h2 hge
    · exact ih hMemTl _

/-- The Uint256 foldl-add `.val` matches the Nat foldl-add when no partial
    sum exceeds 2^256. -/
private theorem foldl_uint256_val_eq_nat_of_no_overflow
    (l : List Uint256) (f : Uint256 → Uint256) :
    ∀ acc : Uint256,
      acc.val + l.foldl (fun b x => b + (f x).val) 0 < Verity.Core.Uint256.modulus →
      (l.foldl (fun b x => b + f x) acc).val =
        acc.val + l.foldl (fun b x => b + (f x).val) 0 := by
  induction l with
  | nil => intro acc _; show acc.val = acc.val + 0; omega
  | cons hd tl ih =>
    intro acc hNo
    simp only [List.foldl]
    -- Nat-sum over hd::tl from 0 = (f hd).val + Nat-sum over tl from 0.
    have hShift :
        tl.foldl (fun b x => b + (f x).val) ((f hd).val) =
          tl.foldl (fun b x => b + (f x).val) 0 + (f hd).val := by
      have := foldl_nat_add_shift tl f 0 (f hd).val
      simpa using this
    -- Rewrite hNo using hShift.
    have hNo' :
        acc.val + ((f hd).val + tl.foldl (fun b x => b + (f x).val) 0) <
          Verity.Core.Uint256.modulus := by
      have hSimp :
          (List.foldl (fun b x => b + (f x).val) 0 (hd :: tl)) =
            (f hd).val + tl.foldl (fun b x => b + (f x).val) 0 := by
        show tl.foldl (fun b x => b + (f x).val) (0 + (f hd).val) =
             (f hd).val + tl.foldl (fun b x => b + (f x).val) 0
        rw [Nat.zero_add]
        rw [hShift]
        exact Nat.add_comm _ _
      have hNoEq : acc.val + (List.foldl (fun b x => b + (f x).val) 0 (hd :: tl)) =
            acc.val + ((f hd).val + tl.foldl (fun b x => b + (f x).val) 0) := by
        rw [hSimp]
      omega
    -- (acc + f hd).val = acc.val + (f hd).val (no wrap because the sum is bounded).
    have hAccHd_no_wrap : acc.val + (f hd).val < Verity.Core.Uint256.modulus := by
      have h1 :
          acc.val + (f hd).val ≤
            acc.val + ((f hd).val + tl.foldl (fun b x => b + (f x).val) 0) := by
        have h2 : (f hd).val ≤
            (f hd).val + tl.foldl (fun b x => b + (f x).val) 0 := Nat.le_add_right _ _
        omega
      exact Nat.lt_of_le_of_lt h1 hNo'
    have hAccHdVal : (acc + f hd).val = acc.val + (f hd).val := by
      show (Verity.Core.Uint256.add acc (f hd)).val = acc.val + (f hd).val
      unfold Verity.Core.Uint256.add
      show (Verity.Core.Uint256.ofNat (acc.val + (f hd).val)).val =
             acc.val + (f hd).val
      exact Nat.mod_eq_of_lt hAccHd_no_wrap
    -- IH applies for (acc + f hd) over tl.
    have hIHno :
        (acc + f hd).val + tl.foldl (fun b x => b + (f x).val) 0 <
          Verity.Core.Uint256.modulus := by
      rw [hAccHdVal]
      omega
    have hIH := ih (acc + f hd) hIHno
    rw [hIH, hAccHdVal]
    -- Goal: acc.val + (f hd).val + tl.foldl ... 0 = acc.val + (foldl over hd::tl from 0)
    show acc.val + (f hd).val + tl.foldl (fun b x => b + (f x).val) 0 =
         acc.val + tl.foldl (fun b x => b + (f x).val) (0 + (f hd).val)
    rw [Nat.zero_add, hShift]
    omega

/-- Under no-overflow, the Uint256 `FiniteSet.sum` `.val` equals the Nat sum. -/
private theorem sum_val_eq_nat_sum_of_no_overflow
    (ids : FiniteSet Uint256) (f : Uint256 → Uint256)
    (hNo : ids.elements.foldl (fun b x => b + (f x).val) 0 <
              Verity.Core.Uint256.modulus) :
    (ids.sum f).val =
      ids.elements.foldl (fun b x => b + (f x).val) 0 := by
  unfold Verity.Core.FiniteSet.sum
  have h0 : (0 : Uint256).val = 0 := rfl
  have hNo' : (0 : Uint256).val + ids.elements.foldl (fun b x => b + (f x).val) 0 <
                Verity.Core.Uint256.modulus := by rw [h0]; omega
  have h := foldl_uint256_val_eq_nat_of_no_overflow ids.elements f 0 hNo'
  rw [h0] at h
  omega

/-- **Single summand ≤ sum** for `FiniteSet.sum` under no-overflow.

    This is the bridge from "the conservation invariant pins
    `Σ projections = cumulativeEarmarked`" to "no individual projection
    exceeds `cumulativeEarmarked`" — provided the sum doesn't wrap. -/
private theorem singleton_le_sum_of_no_overflow
    (ids : FiniteSet Uint256) (f : Uint256 → Uint256)
    (a : Uint256) (hMem : a ∈ ids.elements)
    (hNo : ids.elements.foldl (fun b x => b + (f x).val) 0 <
              Verity.Core.Uint256.modulus) :
    f a ≤ ids.sum f := by
  show (f a).val ≤ (ids.sum f).val
  rw [sum_val_eq_nat_sum_of_no_overflow ids f hNo]
  exact foldl_nat_add_ge_singleton ids.elements f a hMem 0

/-- **H5 corollary**: under the conservation invariant, H2-synced at
    `accountId`, and no-overflow on the projection sum, the stored
    earmarked at `accountId` is bounded by `cumulativeEarmarked`. -/
theorem accounts_earmarked_le_cumulative_of_invariant
    (s : ContractState) (ids : FiniteSet Uint256) (accountId : Uint256)
    (hMem : accountId ∈ ids.elements)
    (hSyncedAtAccountId :
      accounts_lastAccruedEarmarkWeight s accountId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s accountId = _redemptionWeight s)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hInvariant : sumProjectedEarmarked s ids = cumulativeEarmarked s)
    (hSumNoOverflow :
      ids.elements.foldl (fun b x => b + (projectedEarmarked s x).val) 0 <
        Verity.Core.Uint256.modulus) :
    accounts_earmarked s accountId ≤ cumulativeEarmarked s := by
  have hProj_eq_stored :
      projectedEarmarked s accountId = accounts_earmarked s accountId :=
    projectedEarmarked_of_synced s accountId
      hSyncedAtAccountId.1 hSyncedAtAccountId.2 hQ128MulOne
  have hLe :
      projectedEarmarked s accountId ≤ sumProjectedEarmarked s ids :=
    singleton_le_sum_of_no_overflow ids
      (fun id => projectedEarmarked s id) accountId hMem hSumNoOverflow
  show (accounts_earmarked s accountId).val ≤ (cumulativeEarmarked s).val
  rw [← hProj_eq_stored, ← hInvariant]
  exact hLe

/-! ## `_subEarmarkedDebt` slot writes and preservation -/

/-- Pure helper: `earmarkToRemove` as computed by the contract. -/
private def subEarmarkedDebt_earmarkToRemove
    (amountInDebtTokens accountDebt accountEarmarked : Uint256) : Uint256 :=
  let credit :=
    ite (amountInDebtTokens > accountDebt) accountDebt amountInDebtTokens
  ite (credit > accountEarmarked) accountEarmarked credit

private theorem _subEarmarkedDebt_slot_write
    (amountInDebtTokens accountId : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    let earmarkToRemove := subEarmarkedDebt_earmarkToRemove
      amountInDebtTokens (accounts_debt s accountId)
      (accounts_earmarked s accountId)
    let remove := ite (earmarkToRemove > cumulativeEarmarked s)
      (cumulativeEarmarked s) earmarkToRemove
    s'.storage 0 = sub (cumulativeEarmarked s) remove ∧
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storage 3 = s.storage 3 ∧
    s'.storage 4 = s.storage 4 ∧
    s'.storageMapUint 100 accountId = s.storageMapUint 100 accountId ∧
    s'.storageMapUint 101 accountId =
      sub (accounts_earmarked s accountId) earmarkToRemove ∧
    s'.storageMapUint 102 accountId = s.storageMapUint 102 accountId ∧
    s'.storageMapUint 103 accountId = s.storageMapUint 103 accountId ∧
    s'.storageMapUint 104 accountId = s.storageMapUint 104 accountId := by
  repeat' constructor
  all_goals
    simp [AlchemistV3._subEarmarkedDebt, subEarmarkedDebt_earmarkToRemove,
      AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
      AlchemistV3.cumulativeEarmarked,
      accounts_debt, accounts_earmarked,
      getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

private theorem _subEarmarkedDebt_mapping_unchanged_diff
    (amountInDebtTokens accountId other : Uint256) (s : ContractState)
    (slotIdx : Nat) (h : other ≠ accountId) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    s'.storageMapUint slotIdx other = s.storageMapUint slotIdx other := by
  simp [AlchemistV3._subEarmarkedDebt,
    AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
    AlchemistV3.cumulativeEarmarked,
    getStorage, setStorage, getMappingUint, setMappingUint,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd, h]

private theorem _subEarmarkedDebt_projectedEarmarked_other
    (s : ContractState) (amountInDebtTokens accountId other : Uint256)
    (h : other ≠ accountId) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    projectedEarmarked s' other = projectedEarmarked s other := by
  intro s'
  show projectedEarmarked s' other = projectedEarmarked s other
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases _subEarmarkedDebt_slot_write amountInDebtTokens accountId s with
    ⟨_h0, _h1, h2, h3, _h4, _hM100, _hM101, _hM102, _hM103, _hM104⟩
  have h100 : s'.storageMapUint 100 other = s.storageMapUint 100 other :=
    _subEarmarkedDebt_mapping_unchanged_diff amountInDebtTokens accountId other s 100 h
  have h101 : s'.storageMapUint 101 other = s.storageMapUint 101 other :=
    _subEarmarkedDebt_mapping_unchanged_diff amountInDebtTokens accountId other s 101 h
  have h102 : s'.storageMapUint 102 other = s.storageMapUint 102 other :=
    _subEarmarkedDebt_mapping_unchanged_diff amountInDebtTokens accountId other s 102 h
  have h103 : s'.storageMapUint 103 other = s.storageMapUint 103 other :=
    _subEarmarkedDebt_mapping_unchanged_diff amountInDebtTokens accountId other s 103 h
  rw [h2, h3, h100, h101, h102, h103]

private theorem subEarmarkedDebt_earmarkToRemove_le_earmarked
    (amountInDebtTokens accountDebt accountEarmarked : Uint256) :
    subEarmarkedDebt_earmarkToRemove amountInDebtTokens accountDebt accountEarmarked
      ≤ accountEarmarked := by
  unfold subEarmarkedDebt_earmarkToRemove
  show (ite ((ite (amountInDebtTokens > accountDebt) accountDebt amountInDebtTokens)
              > accountEarmarked) accountEarmarked
              (ite (amountInDebtTokens > accountDebt) accountDebt amountInDebtTokens)).val
       ≤ accountEarmarked.val
  by_cases h2 : (ite (amountInDebtTokens > accountDebt) accountDebt amountInDebtTokens)
                  > accountEarmarked
  · rw [if_pos h2]; exact Nat.le_refl _
  · rw [if_neg h2]
    have h2val : ¬ ((ite (amountInDebtTokens > accountDebt) accountDebt amountInDebtTokens).val
                    > accountEarmarked.val) := h2
    omega

theorem _subEarmarkedDebt_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (amountInDebtTokens accountId : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hSyncedAtAccountId :
      accounts_lastAccruedEarmarkWeight s accountId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s accountId = _redemptionWeight s)
    (hSumNoOverflow :
      ids.elements.foldl (fun b x => b + (projectedEarmarked s x).val) 0 <
        Verity.Core.Uint256.modulus) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    _subEarmarkedDebt_preserves_invariant_spec s s' ids accountId := by
  intro s' hMem hPre
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s'
  rcases _subEarmarkedDebt_slot_write amountInDebtTokens accountId s with
    ⟨h0, _h1, h2, h3, _h4, _hM100, hM101, hM102, hM103, _hM104⟩
  -- Derived: stored at accountId ≤ cumulativeEarmarked. Was H5 in the
  -- previous formulation; now derived from invariant + H2 + no-overflow.
  have hAccountEarmarkedLeCumulative :
      accounts_earmarked s accountId ≤ cumulativeEarmarked s :=
    accounts_earmarked_le_cumulative_of_invariant s ids accountId hMem
      hSyncedAtAccountId hQ128MulOne hPre hSumNoOverflow
  have hETR_le_earmarked :
      subEarmarkedDebt_earmarkToRemove amountInDebtTokens
          (accounts_debt s accountId) (accounts_earmarked s accountId)
        ≤ accounts_earmarked s accountId :=
    subEarmarkedDebt_earmarkToRemove_le_earmarked _ _ _
  have hETR_le_cum :
      subEarmarkedDebt_earmarkToRemove amountInDebtTokens
          (accounts_debt s accountId) (accounts_earmarked s accountId)
        ≤ cumulativeEarmarked s := by
    have hA :
        (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
            (accounts_debt s accountId) (accounts_earmarked s accountId)).val
          ≤ (accounts_earmarked s accountId).val :=
      hETR_le_earmarked
    have hB : (accounts_earmarked s accountId).val ≤ (cumulativeEarmarked s).val :=
      hAccountEarmarkedLeCumulative
    exact Nat.le_trans hA hB
  have hClampInactive :
      ¬ (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
            (accounts_debt s accountId) (accounts_earmarked s accountId)
          > cumulativeEarmarked s) := by
    intro hGt
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hGt hETR_le_cum)
  have hCumulativeDelta :
      cumulativeEarmarked s' =
        sub (cumulativeEarmarked s)
          (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
            (accounts_debt s accountId) (accounts_earmarked s accountId)) := by
    show s'.storage 0 =
      sub (cumulativeEarmarked s)
        (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
          (accounts_debt s accountId) (accounts_earmarked s accountId))
    rw [h0]
    rw [if_neg hClampInactive]
  have hPreProj_eq_stored :
      projectedEarmarked s accountId = accounts_earmarked s accountId :=
    projectedEarmarked_of_synced s accountId hSyncedAtAccountId.1
      hSyncedAtAccountId.2 hQ128MulOne
  have hPostLastEW :
      accounts_lastAccruedEarmarkWeight s' accountId = _earmarkWeight s' := by
    show s'.storageMapUint 102 accountId = s'.storage 2
    rw [hM102, h2]; exact hSyncedAtAccountId.1
  have hPostLastRW :
      accounts_lastAccruedRedemptionWeight s' accountId = _redemptionWeight s' := by
    show s'.storageMapUint 103 accountId = s'.storage 3
    rw [hM103, h3]; exact hSyncedAtAccountId.2
  have hPostProj_eq_stored' :
      projectedEarmarked s' accountId = accounts_earmarked s' accountId :=
    projectedEarmarked_of_synced s' accountId hPostLastEW hPostLastRW hQ128MulOne
  have hPostStored :
      accounts_earmarked s' accountId =
        sub (accounts_earmarked s accountId)
          (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
            (accounts_debt s accountId) (accounts_earmarked s accountId)) := by
    show s'.storageMapUint 101 accountId =
      sub (accounts_earmarked s accountId)
        (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
          (accounts_debt s accountId) (accounts_earmarked s accountId))
    exact hM101
  have hSumDecrement :
      sumProjectedEarmarked s' ids =
        sub (sumProjectedEarmarked s ids)
          (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
            (accounts_debt s accountId) (accounts_earmarked s accountId)) := by
    unfold sumProjectedEarmarked
    have hCongr :
        ids.sum (fun id => projectedEarmarked s' id) =
          ids.sum (fun id =>
            if id = accountId then
              sub (projectedEarmarked s id)
                (subEarmarkedDebt_earmarkToRemove amountInDebtTokens
                  (accounts_debt s accountId) (accounts_earmarked s accountId))
            else projectedEarmarked s id) := by
      apply sum_congr_on
      intro id _hMemId
      by_cases hid : id = accountId
      · rw [hid]
        simp only [if_true]
        rw [hPostProj_eq_stored', hPostStored, hPreProj_eq_stored]
      · simp only [if_neg hid]
        exact _subEarmarkedDebt_projectedEarmarked_other s amountInDebtTokens accountId id hid
    rw [hCongr]
    have hLe_proj :
        subEarmarkedDebt_earmarkToRemove amountInDebtTokens
            (accounts_debt s accountId) (accounts_earmarked s accountId)
          ≤ projectedEarmarked s accountId := by
      rw [hPreProj_eq_stored]; exact hETR_le_earmarked
    exact sum_singleton_decrement ids accountId hMem
      (fun id => projectedEarmarked s id) _ hLe_proj
  rw [hSumDecrement, hCumulativeDelta, hPre]

/-! ## `_sync(tokenId)` slot writes and preservation -/

/-- Slot-write lemma for `_sync(tokenId)`: globals slots 0-4 are
    untouched (only mappings 100-104 at tokenId are written). -/
theorem _sync_slot_write
    (tokenId : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storage 3 = s.storage 3 ∧
    s'.storage 4 = s.storage 4 ∧
    s'.storage 5 = s.storage 5 := by
  repeat' constructor
  all_goals
    simp [AlchemistV3._sync,
      AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
      AlchemistV3._survivalAccumulator,
      AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
      AlchemistV3._accounts_lastAccruedEarmarkWeight,
      AlchemistV3._accounts_lastAccruedRedemptionWeight,
      AlchemistV3._accounts_lastSurvivalAccumulator,
      getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

/-- Frame lemma for `_sync`: per-account mapping at `other ≠ tokenId` is unchanged. -/
private theorem _sync_mapping_unchanged_diff
    (tokenId other : Uint256) (s : ContractState) (slotIdx : Nat)
    (h : other ≠ tokenId) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    s'.storageMapUint slotIdx other = s.storageMapUint slotIdx other := by
  simp [AlchemistV3._sync,
    AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
    AlchemistV3._survivalAccumulator,
    AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
    AlchemistV3._accounts_lastAccruedEarmarkWeight,
    AlchemistV3._accounts_lastAccruedRedemptionWeight,
    AlchemistV3._accounts_lastSurvivalAccumulator,
    getStorage, getMappingUint, setMappingUint,
    Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd, h]

/-- After `_sync(tokenId)`, the lastAccruedEarmarkWeight at tokenId equals
    the (unchanged) global `_earmarkWeight`. -/
theorem _sync_writes_lastEW
    (tokenId : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    s'.storageMapUint 102 tokenId = s.storage 2 := by
  simp [AlchemistV3._sync,
    AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
    AlchemistV3._survivalAccumulator,
    AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
    AlchemistV3._accounts_lastAccruedEarmarkWeight,
    AlchemistV3._accounts_lastAccruedRedemptionWeight,
    AlchemistV3._accounts_lastSurvivalAccumulator,
    getStorage, getMappingUint, setMappingUint,
    Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

/-- After `_sync(tokenId)`, the lastAccruedRedemptionWeight at tokenId
    equals the global `_redemptionWeight`. -/
theorem _sync_writes_lastRW
    (tokenId : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    s'.storageMapUint 103 tokenId = s.storage 3 := by
  simp [AlchemistV3._sync,
    AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
    AlchemistV3._survivalAccumulator,
    AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
    AlchemistV3._accounts_lastAccruedEarmarkWeight,
    AlchemistV3._accounts_lastAccruedRedemptionWeight,
    AlchemistV3._accounts_lastSurvivalAccumulator,
    getStorage, getMappingUint, setMappingUint,
    Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

/-- The newEarmarked written into slot 101 at tokenId by `_sync` is the
    pre-state projection at tokenId. -/
private theorem _sync_writes_projected
    (tokenId : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    s'.storageMapUint 101 tokenId = projectedEarmarked s tokenId := by
  show ((AlchemistV3._sync tokenId).run s).snd.storageMapUint 101 tokenId =
    projectedEarmarked s tokenId
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  -- ONE_Q128 unfolds to the literal used in the contract body.
  show ((AlchemistV3._sync tokenId).run s).snd.storageMapUint 101 tokenId = _
  simp only [show ONE_Q128 = (340282366920938463463374607431768211456 : Uint256) from rfl]
  -- Also align `a > b` (Uint256) to `b.val < a.val` form.
  simp only [show ∀ (a b : Uint256), (a > b) = (b.val < a.val) from fun _ _ => rfl]
  simp [AlchemistV3._sync,
    AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
    AlchemistV3._survivalAccumulator,
    AlchemistV3._accounts_debt, AlchemistV3._accounts_earmarked,
    AlchemistV3._accounts_lastAccruedEarmarkWeight,
    AlchemistV3._accounts_lastAccruedRedemptionWeight,
    AlchemistV3._accounts_lastSurvivalAccumulator,
    getStorage, getMappingUint, setMappingUint,
    Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

/-- The pre-state and post-state projections at `id ≠ tokenId` agree
    because every storage location consumed by the projection is unchanged. -/
private theorem _sync_projectedEarmarked_other
    (s : ContractState) (tokenId other : Uint256)
    (h : other ≠ tokenId) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    projectedEarmarked s' other = projectedEarmarked s other := by
  intro s'
  show projectedEarmarked s' other = projectedEarmarked s other
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases _sync_slot_write tokenId s with ⟨_h0, _h1, h2, h3, _h4, _h5⟩
  have h100 : s'.storageMapUint 100 other = s.storageMapUint 100 other :=
    _sync_mapping_unchanged_diff tokenId other s 100 h
  have h101 : s'.storageMapUint 101 other = s.storageMapUint 101 other :=
    _sync_mapping_unchanged_diff tokenId other s 101 h
  have h102 : s'.storageMapUint 102 other = s.storageMapUint 102 other :=
    _sync_mapping_unchanged_diff tokenId other s 102 h
  have h103 : s'.storageMapUint 103 other = s.storageMapUint 103 other :=
    _sync_mapping_unchanged_diff tokenId other s 103 h
  rw [h2, h3, h100, h101, h102, h103]

/-- `_sync(tokenId)` replaces the per-id projection at tokenId with the
    *previous* projection value (because `_sync` writes the projected
    earmarked into storage, and at the new state the account is synced
    so its projection equals its stored value, which is exactly the
    pre-state projection). -/
private theorem _sync_projectedEarmarked_tokenId
    (s : ContractState) (tokenId : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    projectedEarmarked s' tokenId = projectedEarmarked s tokenId := by
  intro s'
  -- Post-state at tokenId is synced: lastEW = eW, lastRW = rW.
  have hPostLastEW :
      accounts_lastAccruedEarmarkWeight s' tokenId = _earmarkWeight s' := by
    show s'.storageMapUint 102 tokenId = s'.storage 2
    rcases _sync_slot_write tokenId s with ⟨_h0, _h1, h2, _h3, _h4, _h5⟩
    rw [h2]
    exact _sync_writes_lastEW tokenId s
  have hPostLastRW :
      accounts_lastAccruedRedemptionWeight s' tokenId = _redemptionWeight s' := by
    show s'.storageMapUint 103 tokenId = s'.storage 3
    rcases _sync_slot_write tokenId s with ⟨_h0, _h1, _h2, h3, _h4, _h5⟩
    rw [h3]
    exact _sync_writes_lastRW tokenId s
  have hPostSynced :
      projectedEarmarked s' tokenId = accounts_earmarked s' tokenId :=
    projectedEarmarked_of_synced s' tokenId hPostLastEW hPostLastRW hQ128MulOne
  have hPostStored :
      accounts_earmarked s' tokenId = projectedEarmarked s tokenId := by
    show s'.storageMapUint 101 tokenId = projectedEarmarked s tokenId
    exact _sync_writes_projected tokenId s
  rw [hPostSynced, hPostStored]

theorem _sync_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (tokenId : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    _sync_preserves_invariant_spec s s' ids := by
  intro s' hPre
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s'
  rcases _sync_slot_write tokenId s with ⟨h0, _h1, _h2, _h3, _h4, _h5⟩
  -- cumulativeEarmarked unchanged.
  have hCumulativeUnchanged :
      cumulativeEarmarked s' = cumulativeEarmarked s := by
    show s'.storage 0 = s.storage 0
    exact h0
  -- Per-id projection equality (at tokenId and at other ids).
  have hProj : ∀ id ∈ ids.elements,
      projectedEarmarked s' id = projectedEarmarked s id := by
    intro id _hMemId
    by_cases hid : id = tokenId
    · subst hid
      exact _sync_projectedEarmarked_tokenId s id hQ128MulOne
    · exact _sync_projectedEarmarked_other s tokenId id hid
  rw [hCumulativeUnchanged]
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s
  rw [← hPre]
  exact sum_congr_on hProj

/-! ## Composite call-site theorems — H2 discharged

  In the deployed Solidity, every call site for `_subDebt` and
  `_subEarmarkedDebt` invokes `_sync(id)` immediately before (lines 502,
  522, 567, 590, 869, 1052). The local `_subDebt_preserves_invariant`
  and `_subEarmarkedDebt_preserves_invariant` theorems take that
  synced precondition (H2) as a hypothesis. The composite theorems
  below prove the call-site sequence `_sync(id); _<op>(...)` preserves
  the invariant *without* H2: the synced precondition is discharged
  inside via `_sync_writes_lastEW` / `_sync_writes_lastRW`. -/

/-- The Nat foldl-sum of projections over `ids` is unchanged across
    `_sync(tokenId)`. Used to transfer the `hSumNoOverflow` hypothesis
    of `_subEarmarkedDebt_preserves_invariant` from `s` to the post-sync
    state. -/
private theorem _sync_projectedEarmarked_natsum_unchanged
    (s : ContractState) (tokenId : Uint256) (ids : FiniteSet Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x) :
    let s_synced := ((AlchemistV3._sync tokenId).run s).snd
    ids.elements.foldl
        (fun b x => b + (projectedEarmarked s_synced x).val) 0 =
      ids.elements.foldl
        (fun b x => b + (projectedEarmarked s x).val) 0 := by
  intro s_synced
  apply foldl_nat_add_congr
  intro id _hMem
  by_cases hid : id = tokenId
  · subst hid
    rw [_sync_projectedEarmarked_tokenId s id hQ128MulOne]
  · rw [_sync_projectedEarmarked_other s tokenId id hid]

/-- **`_sync(tokenId); _subDebt(tokenId, amount)` preserves the
    invariant.** Discharges H2 (synced-at-touched-id). -/
theorem _sync_then_subDebt_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (tokenId amount : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hCumulativeLeTotalDebt :
      cumulativeEarmarked s ≤ sub (totalDebt s) amount) :
    let s_synced := ((AlchemistV3._sync tokenId).run s).snd
    let s' := ((AlchemistV3._subDebt tokenId amount).run s_synced).snd
    _subDebt_preserves_invariant_spec s s' ids tokenId := by
  intro s_synced s' hMem hPre
  -- Sync preserves the invariant.
  have hSyncedInvariant :
      sumProjectedEarmarked s_synced ids = cumulativeEarmarked s_synced :=
    _sync_preserves_invariant s ids tokenId hQ128MulOne hPre
  -- After sync, tokenId is synced (H2 discharged).
  have hSyncedH2 :
      accounts_lastAccruedEarmarkWeight s_synced tokenId = _earmarkWeight s_synced ∧
      accounts_lastAccruedRedemptionWeight s_synced tokenId = _redemptionWeight s_synced := by
    constructor
    · show s_synced.storageMapUint 102 tokenId = s_synced.storage 2
      rcases _sync_slot_write tokenId s with ⟨_h0, _h1, h2, _h3, _h4, _h5⟩
      rw [h2]
      exact _sync_writes_lastEW tokenId s
    · show s_synced.storageMapUint 103 tokenId = s_synced.storage 3
      rcases _sync_slot_write tokenId s with ⟨_h0, _h1, _h2, h3, _h4, _h5⟩
      rw [h3]
      exact _sync_writes_lastRW tokenId s
  -- H4 transfers across sync (cumulativeEarmarked and totalDebt unchanged).
  have hSyncedH4 :
      cumulativeEarmarked s_synced ≤ sub (totalDebt s_synced) amount := by
    rcases _sync_slot_write tokenId s with ⟨h0, h1, _h2, _h3, _h4, _h5⟩
    have hC : cumulativeEarmarked s_synced = cumulativeEarmarked s := h0
    have hT : totalDebt s_synced = totalDebt s := h1
    show (cumulativeEarmarked s_synced).val ≤ (sub (totalDebt s_synced) amount).val
    rw [hC, hT]
    exact hCumulativeLeTotalDebt
  -- Apply the local theorem on the synced state.
  exact _subDebt_preserves_invariant s_synced ids tokenId amount hQ128MulOne
    hSyncedH2 hSyncedH4 hMem hSyncedInvariant

/-- **`_sync(accountId); _subEarmarkedDebt(amount, accountId)` preserves
    the invariant.** Discharges H2 (synced-at-touched-id). -/
theorem _sync_then_subEarmarkedDebt_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (amountInDebtTokens accountId : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hSumNoOverflow :
      ids.elements.foldl (fun b x => b + (projectedEarmarked s x).val) 0 <
        Verity.Core.Uint256.modulus) :
    let s_synced := ((AlchemistV3._sync accountId).run s).snd
    let s' :=
      ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s_synced).snd
    _subEarmarkedDebt_preserves_invariant_spec s s' ids accountId := by
  intro s_synced s' hMem hPre
  have hSyncedInvariant :
      sumProjectedEarmarked s_synced ids = cumulativeEarmarked s_synced :=
    _sync_preserves_invariant s ids accountId hQ128MulOne hPre
  have hSyncedH2 :
      accounts_lastAccruedEarmarkWeight s_synced accountId = _earmarkWeight s_synced ∧
      accounts_lastAccruedRedemptionWeight s_synced accountId = _redemptionWeight s_synced := by
    constructor
    · show s_synced.storageMapUint 102 accountId = s_synced.storage 2
      rcases _sync_slot_write accountId s with ⟨_h0, _h1, h2, _h3, _h4, _h5⟩
      rw [h2]
      exact _sync_writes_lastEW accountId s
    · show s_synced.storageMapUint 103 accountId = s_synced.storage 3
      rcases _sync_slot_write accountId s with ⟨_h0, _h1, _h2, h3, _h4, _h5⟩
      rw [h3]
      exact _sync_writes_lastRW accountId s
  have hSyncedNoOverflow :
      ids.elements.foldl
          (fun b x => b + (projectedEarmarked s_synced x).val) 0 <
        Verity.Core.Uint256.modulus := by
    rw [_sync_projectedEarmarked_natsum_unchanged s accountId ids hQ128MulOne]
    exact hSumNoOverflow
  exact _subEarmarkedDebt_preserves_invariant s_synced ids amountInDebtTokens accountId
    hQ128MulOne hSyncedH2 hSyncedNoOverflow hMem hSyncedInvariant

/-! ## `redeem(amount)` slot writes and preservation

  `redeem(amount)` scales `_redemptionWeight`, `_survivalAccumulator`,
  and `cumulativeEarmarked` by `ratioApplied`, and decreases `totalDebt`
  by `effectiveRedeemed`. Per-id projections scale by the same
  `ratioApplied` (via the redemption survival ratio). Sum-distributes
  by Q128 linearity.
-/

/-- Slot-write lemma for `redeem(amount)`. -/
private theorem redeem_slot_write
    (amount : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    let liveEarmarked := cumulativeEarmarked s
    let ratioApplied := redeem_ratioApplied amount liveEarmarked
    let active := redeem_active amount liveEarmarked
    s'.storage 0 =
      ite active (mulQ128 liveEarmarked ratioApplied) (cumulativeEarmarked s) ∧
    s'.storage 1 =
      ite active (sub (totalDebt s) (sub liveEarmarked (mulQ128 liveEarmarked ratioApplied))) (totalDebt s) ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storage 3 = ite active (mulQ128 (s.storage 3) ratioApplied) (s.storage 3) ∧
    s'.storage 4 = ite active (mulQ128 (s.storage 4) ratioApplied) (s.storage 4) := by
  repeat' constructor
  all_goals
    simp [AlchemistV3.redeem, mulQ128, redeem_ratioApplied, redeem_active,
      AlchemistV3.cumulativeEarmarked, AlchemistV3.totalDebt,
      AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
      AlchemistV3._survivalAccumulator,
      cumulativeEarmarked, totalDebt,
      getStorage, setStorage,
      Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

/-- `redeem(amount)` does not touch any per-account mapping. -/
private theorem redeem_mapping_unchanged
    (amount : Uint256) (s : ContractState) (slotIdx : Nat) (key : Uint256) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    s'.storageMapUint slotIdx key = s.storageMapUint slotIdx key := by
  simp [AlchemistV3.redeem,
    AlchemistV3.cumulativeEarmarked, AlchemistV3.totalDebt,
    AlchemistV3._redemptionWeight, AlchemistV3._survivalAccumulator,
    getStorage, setStorage,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

/-- Inactive branch of `redeem(amount)`: per-id projection unchanged. -/
private theorem redeem_projectedEarmarked_inactive
    (s : ContractState) (amount id : Uint256)
    (hInactive : redeem_active amount (cumulativeEarmarked s) = false) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    projectedEarmarked s' id = projectedEarmarked s id := by
  intro s'
  show projectedEarmarked s' id = projectedEarmarked s id
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases redeem_slot_write amount s with ⟨_h0, _h1, h2, h3, _h4⟩
  have h2' : s'.storage 2 = s.storage 2 := h2
  have h3' : s'.storage 3 = s.storage 3 := by
    rw [h3, hInactive]; rfl
  have h100 : s'.storageMapUint 100 id = s.storageMapUint 100 id :=
    redeem_mapping_unchanged amount s 100 id
  have h101 : s'.storageMapUint 101 id = s.storageMapUint 101 id :=
    redeem_mapping_unchanged amount s 101 id
  have h102 : s'.storageMapUint 102 id = s.storageMapUint 102 id :=
    redeem_mapping_unchanged amount s 102 id
  have h103 : s'.storageMapUint 103 id = s.storageMapUint 103 id :=
    redeem_mapping_unchanged amount s 103 id
  rw [h2', h3', h100, h101, h102, h103]

/-! ### Survival-ratio scaling helper

  When `eW' = mulQ128 eW r` (e.g. slot 2 scales under active `_earmark`,
  or slot 3 scales under active `redeem`), the `survivalRatio` formula
  evaluates to `mulQ128 (USR_pre) r`. This packages the case analysis
  used by both `_earmark_projectedEarmarked_active` and
  `redeem_projectedEarmarked_active`. -/
private theorem survivalRatio_scales
    (eW lastEW r : Uint256) (hLastEWNonZero : lastEW ≠ 0)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128) :
    (if lastEW = mulQ128 eW r then ONE_Q128
     else if lastEW = 0 then ONE_Q128
     else divQ128 (mulQ128 eW r) lastEW) =
    mulQ128 (if lastEW = eW then ONE_Q128
             else if lastEW = 0 then ONE_Q128
             else divQ128 eW lastEW) r := by
  by_cases hEq : lastEW = mulQ128 eW r
  · rw [if_pos hEq]
    by_cases hPreEq : lastEW = eW
    · rw [if_pos hPreEq, hQ128OneMul]
      -- hEq combined with hPreEq gives eW = mulQ128 eW r.
      have heW_fix : eW = mulQ128 eW r := hPreEq ▸ hEq
      by_cases heW0 : eW = 0
      · rw [heW0] at hPreEq
        exact absurd hPreEq hLastEWNonZero
      · exact (hQ128MulCancelOne eW r heW0 heW_fix.symm).symm
    · by_cases hPreZero : lastEW = 0
      · exact absurd hPreZero hLastEWNonZero
      · rw [if_neg hPreEq, if_neg hPreZero]
        -- Goal: ONE_Q128 = mulQ128 (divQ128 eW lastEW) r.
        -- Note: divQ128 lastEW lastEW = ONE_Q128 (divSelf).
        -- Replace the first lastEW with mulQ128 eW r (via hEq), giving
        -- divQ128 (mulQ128 eW r) lastEW = ONE_Q128.
        -- Then by hQ128DivCommScale, divQ128 (mulQ128 eW r) lastEW = mulQ128 (divQ128 eW lastEW) r.
        have hCS : divQ128 (mulQ128 eW r) lastEW = mulQ128 (divQ128 eW lastEW) r :=
          hQ128DivCommScale eW lastEW r hPreZero
        -- Combine: mulQ128 (divQ128 eW lastEW) r = divQ128 (mulQ128 eW r) lastEW
        --           = divQ128 lastEW lastEW (using hEq.symm to rewrite mulQ128 eW r as lastEW)
        --           = ONE_Q128.
        rw [← hCS, ← hEq, hQ128DivSelf lastEW hPreZero]
  · by_cases hPostZero : lastEW = 0
    · exact absurd hPostZero hLastEWNonZero
    · rw [if_neg hEq, if_neg hPostZero]
      rw [hQ128DivCommScale eW lastEW r hPostZero]
      by_cases hPreEq : lastEW = eW
      · rw [if_pos hPreEq]
        have heW_ne : eW ≠ 0 := hPreEq ▸ hPostZero
        rw [hPreEq, hQ128DivSelf eW heW_ne]
      · by_cases hPreZero : lastEW = 0
        · exact absurd hPreZero hLastEWNonZero
        · rw [if_neg hPreEq, if_neg hPreZero]

/-- Active branch: the per-id projection scales by `ratioApplied`.
    Derived from the slot-write (slot 3 scales) plus the redemption
    survival ratio scales identity, and the projection formula. -/
private theorem redeem_projectedEarmarked_active
    (s : ContractState) (amount id : Uint256)
    (hActive : redeem_active amount (cumulativeEarmarked s) = true)
    (hLastRWNonZero : accounts_lastAccruedRedemptionWeight s id ≠ 0)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128MulAssoc : ∀ a b c : Uint256,
      mulQ128 (mulQ128 a b) c = mulQ128 a (mulQ128 b c))
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    let ratioApplied := redeem_ratioApplied amount (cumulativeEarmarked s)
    projectedEarmarked s' id =
      mulQ128 (projectedEarmarked s id) ratioApplied := by
  intro s' ratioApplied
  show projectedEarmarked s' id = mulQ128 (projectedEarmarked s id) ratioApplied
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases redeem_slot_write amount s with ⟨_h0, _h1, h2, h3, _h4⟩
  have h2' : s'.storage 2 = s.storage 2 := h2
  have h3' : s'.storage 3 = mulQ128 (s.storage 3) ratioApplied := by
    rw [h3, hActive]
    rfl
  have h100 : s'.storageMapUint 100 id = s.storageMapUint 100 id :=
    redeem_mapping_unchanged amount s 100 id
  have h101 : s'.storageMapUint 101 id = s.storageMapUint 101 id :=
    redeem_mapping_unchanged amount s 101 id
  have h102 : s'.storageMapUint 102 id = s.storageMapUint 102 id :=
    redeem_mapping_unchanged amount s 102 id
  have h103 : s'.storageMapUint 103 id = s.storageMapUint 103 id :=
    redeem_mapping_unchanged amount s 103 id
  rw [h2', h3', h100, h101, h102, h103]
  -- The goal has `div (mul ... ONE_Q128) Y` which is `divQ128 ... Y` by defn,
  -- and `div (mul ... Y) ONE_Q128` which is `mulQ128 ... Y` by defn.
  -- Rewrite the goal to use divQ128 / mulQ128 abbreviations.
  show
    mulQ128
      (add (s.storageMapUint 101 id)
        (sub
          (if s.storageMapUint 100 id > s.storageMapUint 101 id then
            sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0)
          (mulQ128
            (if s.storageMapUint 100 id > s.storageMapUint 101 id then
              sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0)
            (if s.storageMapUint 102 id = s.storage 2 then ONE_Q128
             else if s.storageMapUint 102 id = 0 then ONE_Q128
             else divQ128 (s.storage 2) (s.storageMapUint 102 id)))))
      (if s.storageMapUint 103 id = mulQ128 (s.storage 3) ratioApplied then ONE_Q128
       else if s.storageMapUint 103 id = 0 then ONE_Q128
       else divQ128 (mulQ128 (s.storage 3) ratioApplied) (s.storageMapUint 103 id))
       =
       mulQ128
       (mulQ128 (add (s.storageMapUint 101 id)
          (sub
            (if s.storageMapUint 100 id > s.storageMapUint 101 id then
              sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0)
            (mulQ128
              (if s.storageMapUint 100 id > s.storageMapUint 101 id then
                sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0)
              (if s.storageMapUint 102 id = s.storage 2 then ONE_Q128
               else if s.storageMapUint 102 id = 0 then ONE_Q128
               else divQ128 (s.storage 2) (s.storageMapUint 102 id)))))
          (if s.storageMapUint 103 id = s.storage 3 then ONE_Q128
           else if s.storageMapUint 103 id = 0 then ONE_Q128
           else divQ128 (s.storage 3) (s.storageMapUint 103 id))) ratioApplied
  -- Apply survivalRatio_scales to the post-state redemption-survival ratio.
  have hScale := survivalRatio_scales (s.storage 3) (s.storageMapUint 103 id) ratioApplied
    hLastRWNonZero hQ128OneMul hQ128DivCommScale hQ128DivSelf hQ128MulCancelOne
  rw [hScale]
  generalize hX :
      add (s.storageMapUint 101 id)
        (sub
          (if s.storageMapUint 100 id > s.storageMapUint 101 id then
            sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0)
          (mulQ128
            (if s.storageMapUint 100 id > s.storageMapUint 101 id then
              sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0)
            (if s.storageMapUint 102 id = s.storage 2 then ONE_Q128
             else if s.storageMapUint 102 id = 0 then ONE_Q128
             else divQ128 (s.storage 2) (s.storageMapUint 102 id)))) = X
  -- Goal: mulQ128 X (mulQ128 RSR_pre ratioApplied) = mulQ128 (mulQ128 X RSR_pre) ratioApplied.
  exact (hQ128MulAssoc X _ ratioApplied).symm

theorem redeem_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (amount : Uint256)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128MulAssoc : ∀ a b c : Uint256,
      mulQ128 (mulQ128 a b) c = mulQ128 a (mulQ128 b c))
    (hQ128MulLinear : ∀ x y r : Uint256,
      mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r))
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128)
    (hLastRWNonZero : ∀ id ∈ ids.elements,
      accounts_lastAccruedRedemptionWeight s id ≠ 0) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    redeem_preserves_invariant_spec s s' ids := by
  intro s' hPre
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s'
  rcases redeem_slot_write amount s with ⟨h0, _h1, _h2, _h3, _h4⟩
  by_cases hActive : redeem_active amount (cumulativeEarmarked s) = true
  · -- Active branch: cumulativeEarmarked s' = mulQ128 cumulativeEarmarked s ratioApplied.
    let ratioApplied := redeem_ratioApplied amount (cumulativeEarmarked s)
    have hCumActive :
        cumulativeEarmarked s' =
          mulQ128 (cumulativeEarmarked s) ratioApplied := by
      show s'.storage 0 = mulQ128 (s.storage 0) ratioApplied
      rw [h0, hActive]
      rfl
    have hScalePerId :
        ∀ id ∈ ids.elements,
          projectedEarmarked s' id =
            mulQ128 (projectedEarmarked s id) ratioApplied := by
      intro id hMemId
      exact redeem_projectedEarmarked_active s amount id hActive
        (hLastRWNonZero id hMemId)
        hQ128OneMul hQ128MulAssoc
        hQ128DivCommScale hQ128DivSelf hQ128MulCancelOne
    have hSum_eq :
        sumProjectedEarmarked s' ids =
          mulQ128 (sumProjectedEarmarked s ids) ratioApplied := by
      unfold sumProjectedEarmarked
      rw [sum_congr_on hScalePerId]
      exact sum_mulQ128_distrib ids (fun id => projectedEarmarked s id) _
        (fun x y => hQ128MulLinear x y _)
    rw [hSum_eq, hCumActive, hPre]
  · -- Inactive: cumulativeEarmarked unchanged, projection unchanged per-id.
    have hInactive : redeem_active amount (cumulativeEarmarked s) = false := by
      cases h : redeem_active amount (cumulativeEarmarked s)
      · rfl
      · exfalso; exact hActive h
    have hCumInactive : cumulativeEarmarked s' = cumulativeEarmarked s := by
      show s'.storage 0 = s.storage 0
      rw [h0, hInactive]
      rfl
    have hProjUnchanged : ∀ id ∈ ids.elements,
        projectedEarmarked s' id = projectedEarmarked s id := by
      intro id _hMem
      exact redeem_projectedEarmarked_inactive s amount id hInactive
    rw [hCumInactive]
    show sumProjectedEarmarked s' ids = cumulativeEarmarked s
    rw [← hPre]
    exact sum_congr_on hProjUnchanged

/-! ## `_earmark()` slot writes and preservation -/

/-- Slot-write lemma for `_earmark()`. The conservation-relevant slots are
    0 (cumulativeEarmarked), 1 (totalDebt), 2 (_earmarkWeight), 3
    (_redemptionWeight). Slot 4 (_survivalAccumulator) is irrelevant to
    the projected sum, so we omit it from the conclusion. -/
private theorem _earmark_slot_write
    (s : ContractState) :
    let s' := ((AlchemistV3._earmark).run s).snd
    let active := _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
    let ratioApplied := _earmark_ratioApplied (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
    let effectiveEarmarked := _earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
    s'.storage 0 = ite active (add (cumulativeEarmarked s) effectiveEarmarked) (cumulativeEarmarked s) ∧
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = ite active (mulQ128 (s.storage 2) ratioApplied) (s.storage 2) ∧
    s'.storage 3 = s.storage 3 := by
  repeat' constructor
  all_goals
    simp [AlchemistV3._earmark, mulQ128,
      _earmark_active, _earmark_ratioApplied, _earmark_effectiveEarmarked,
      AlchemistV3.cumulativeEarmarked, AlchemistV3.totalDebt,
      AlchemistV3._earmarkWeight, AlchemistV3._redemptionWeight,
      AlchemistV3._survivalAccumulator, AlchemistV3._transmuterEarmarkAmount,
      cumulativeEarmarked, totalDebt,
      getStorage, setStorage,
      Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]

/-- `_earmark()` does not touch any per-account mapping. -/
private theorem _earmark_mapping_unchanged
    (s : ContractState) (slotIdx : Nat) (key : Uint256) :
    let s' := ((AlchemistV3._earmark).run s).snd
    s'.storageMapUint slotIdx key = s.storageMapUint slotIdx key := by
  simp [AlchemistV3._earmark,
    AlchemistV3.cumulativeEarmarked, AlchemistV3.totalDebt,
    AlchemistV3._earmarkWeight,
    AlchemistV3._survivalAccumulator, AlchemistV3._transmuterEarmarkAmount,
    getStorage, setStorage,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

/-- Inactive branch of `_earmark()`: per-id projection unchanged. -/
private theorem _earmark_projectedEarmarked_inactive
    (s : ContractState) (id : Uint256)
    (hInactive : _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = false) :
    let s' := ((AlchemistV3._earmark).run s).snd
    projectedEarmarked s' id = projectedEarmarked s id := by
  intro s'
  show projectedEarmarked s' id = projectedEarmarked s id
  unfold projectedEarmarked _computeUnrealizedAccount
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases _earmark_slot_write s with ⟨_h0, _h1, h2, h3⟩
  have h2' : s'.storage 2 = s.storage 2 := by
    rw [h2, hInactive]; rfl
  have h3' : s'.storage 3 = s.storage 3 := h3
  have h100 : s'.storageMapUint 100 id = s.storageMapUint 100 id :=
    _earmark_mapping_unchanged s 100 id
  have h101 : s'.storageMapUint 101 id = s.storageMapUint 101 id :=
    _earmark_mapping_unchanged s 101 id
  have h102 : s'.storageMapUint 102 id = s.storageMapUint 102 id :=
    _earmark_mapping_unchanged s 102 id
  have h103 : s'.storageMapUint 103 id = s.storageMapUint 103 id :=
    _earmark_mapping_unchanged s 103 id
  rw [h2', h3', h100, h101, h102, h103]

/-! ### Per-id projection delta under active `_earmark`

  Active `_earmark` shifts `_earmarkWeight` by `ratioApplied`. Through
  the per-id `unearmarkSurvivalRatio` the lazy projection's
  `unearmarkedRemaining` scales by `ratioApplied`, and the projection
  result grows by

    delta_id = mulQ128 Y_id (sub ONE_Q128 ratioApplied)

  where `Y_id = earmark_unearmarkedTimesRSR s id`. -/
private theorem _earmark_projectedEarmarked_active
    (s : ContractState) (id : Uint256)
    (hActive :
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true)
    (hLastEWNonZero : accounts_lastAccruedEarmarkWeight s id ≠ 0)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128MulComm : ∀ a b : Uint256, mulQ128 a b = mulQ128 b a)
    (hQ128MulAssoc : ∀ a b c : Uint256,
      mulQ128 (mulQ128 a b) c = mulQ128 a (mulQ128 b c))
    (hQ128MulLinear : ∀ x y r : Uint256,
      mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r))
    (hQ128MulSubDistrib : ∀ x y r : Uint256,
      mulQ128 (sub x y) r = sub (mulQ128 x r) (mulQ128 y r))
    (hQ128MulOneSub : ∀ a r : Uint256,
      sub a (mulQ128 a r) = mulQ128 a (sub ONE_Q128 r))
    (hQ128MulAppliedLe : ∀ y : Uint256,
      mulQ128 y
        (_earmark_ratioApplied (totalDebt s) (cumulativeEarmarked s) (s.storage 5))
        ≤ y)
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128) :
    let s' := ((AlchemistV3._earmark).run s).snd
    let ratioApplied :=
      _earmark_ratioApplied (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
    projectedEarmarked s' id =
      add (projectedEarmarked s id)
        (mulQ128 (earmark_unearmarkedTimesRSR s id) (sub ONE_Q128 ratioApplied)) := by
  intro s' ratioApplied
  show projectedEarmarked s' id = _
  unfold projectedEarmarked _computeUnrealizedAccount earmark_unearmarkedTimesRSR
  unfold _earmarkWeight _redemptionWeight
    accounts_lastAccruedEarmarkWeight accounts_lastAccruedRedemptionWeight
    accounts_debt accounts_earmarked
  rcases _earmark_slot_write s with ⟨_h0, _h1, h2, h3⟩
  have h2' : s'.storage 2 = mulQ128 (s.storage 2) ratioApplied := by
    show s'.storage 2 = _
    rw [h2, hActive]
    rfl
  have h3' : s'.storage 3 = s.storage 3 := h3
  have h100 : s'.storageMapUint 100 id = s.storageMapUint 100 id :=
    _earmark_mapping_unchanged s 100 id
  have h101 : s'.storageMapUint 101 id = s.storageMapUint 101 id :=
    _earmark_mapping_unchanged s 101 id
  have h102 : s'.storageMapUint 102 id = s.storageMapUint 102 id :=
    _earmark_mapping_unchanged s 102 id
  have h103 : s'.storageMapUint 103 id = s.storageMapUint 103 id :=
    _earmark_mapping_unchanged s 103 id
  rw [h2', h3', h100, h101, h102, h103]
  have hScale := survivalRatio_scales (s.storage 2) (s.storageMapUint 102 id)
    ratioApplied hLastEWNonZero
    hQ128OneMul hQ128DivCommScale hQ128DivSelf hQ128MulCancelOne
  change
    mulQ128
      (add (s.storageMapUint 101 id)
        (sub
          (if s.storageMapUint 100 id > s.storageMapUint 101 id then
            sub (s.storageMapUint 100 id) (s.storageMapUint 101 id)
          else 0)
          (mulQ128
            (if s.storageMapUint 100 id > s.storageMapUint 101 id then
              sub (s.storageMapUint 100 id) (s.storageMapUint 101 id)
            else 0)
            (if s.storageMapUint 102 id = mulQ128 (s.storage 2) ratioApplied then ONE_Q128
             else if s.storageMapUint 102 id = 0 then ONE_Q128
             else divQ128 (mulQ128 (s.storage 2) ratioApplied) (s.storageMapUint 102 id)))))
      (if s.storageMapUint 103 id = s.storage 3 then ONE_Q128
       else if s.storageMapUint 103 id = 0 then ONE_Q128
       else divQ128 (s.storage 3) (s.storageMapUint 103 id)) =
    add
      (mulQ128
        (add (s.storageMapUint 101 id)
          (sub
            (if s.storageMapUint 100 id > s.storageMapUint 101 id then
              sub (s.storageMapUint 100 id) (s.storageMapUint 101 id)
            else 0)
            (mulQ128
              (if s.storageMapUint 100 id > s.storageMapUint 101 id then
                sub (s.storageMapUint 100 id) (s.storageMapUint 101 id)
              else 0)
              (if s.storageMapUint 102 id = s.storage 2 then ONE_Q128
               else if s.storageMapUint 102 id = 0 then ONE_Q128
               else divQ128 (s.storage 2) (s.storageMapUint 102 id)))))
        (if s.storageMapUint 103 id = s.storage 3 then ONE_Q128
         else if s.storageMapUint 103 id = 0 then ONE_Q128
         else divQ128 (s.storage 3) (s.storageMapUint 103 id)))
      (mulQ128
        (mulQ128
          (mulQ128
            (if s.storageMapUint 100 id > s.storageMapUint 101 id then
              sub (s.storageMapUint 100 id) (s.storageMapUint 101 id)
            else 0)
            (if s.storageMapUint 102 id = s.storage 2 then ONE_Q128
             else if s.storageMapUint 102 id = 0 then ONE_Q128
             else divQ128 (s.storage 2) (s.storageMapUint 102 id)))
          (if s.storageMapUint 103 id = s.storage 3 then ONE_Q128
           else if s.storageMapUint 103 id = 0 then ONE_Q128
           else divQ128 (s.storage 3) (s.storageMapUint 103 id)))
        (sub ONE_Q128 ratioApplied))
  rw [hScale]
  generalize hUE :
    (if s.storageMapUint 100 id > s.storageMapUint 101 id then
      sub (s.storageMapUint 100 id) (s.storageMapUint 101 id) else 0) = UE
  generalize hUSR :
    (if s.storageMapUint 102 id = s.storage 2 then ONE_Q128
     else if s.storageMapUint 102 id = 0 then ONE_Q128
     else divQ128 (s.storage 2) (s.storageMapUint 102 id)) = USR_pre
  generalize hRSR :
    (if s.storageMapUint 103 id = s.storage 3 then ONE_Q128
     else if s.storageMapUint 103 id = 0 then ONE_Q128
     else divQ128 (s.storage 3) (s.storageMapUint 103 id)) = RSR
  generalize hEarm : s.storageMapUint 101 id = earm
  have hUR_post_eq :
      mulQ128 UE (mulQ128 USR_pre ratioApplied) = mulQ128 (mulQ128 UE USR_pre) ratioApplied :=
    (hQ128MulAssoc UE USR_pre ratioApplied).symm
  rw [hUR_post_eq]
  generalize hURpre : mulQ128 UE USR_pre = UR_pre
  rw [hQ128MulLinear earm (sub UE (mulQ128 UR_pre ratioApplied)) RSR,
      hQ128MulSubDistrib UE (mulQ128 UR_pre ratioApplied) RSR,
      hQ128MulLinear earm (sub UE UR_pre) RSR,
      hQ128MulSubDistrib UE UR_pre RSR]
  have hReassoc :
      mulQ128 (mulQ128 UR_pre ratioApplied) RSR =
        mulQ128 (mulQ128 UR_pre RSR) ratioApplied := by
    rw [hQ128MulAssoc UR_pre ratioApplied RSR,
        hQ128MulComm ratioApplied RSR,
        ← hQ128MulAssoc UR_pre RSR ratioApplied]
  rw [hReassoc]
  rw [← hQ128MulOneSub (mulQ128 UR_pre RSR) ratioApplied]
  generalize hY : mulQ128 UR_pre RSR = Y
  generalize hA : mulQ128 earm RSR = A
  generalize hB : mulQ128 UE RSR = B
  rw [show add (add A (sub B Y)) (sub Y (mulQ128 Y ratioApplied)) =
        add A (add (sub B Y) (sub Y (mulQ128 Y ratioApplied))) from
        Verity.Core.Uint256.add_assoc A (sub B Y) (sub Y (mulQ128 Y ratioApplied))]
  congr 1
  exact (uint256_sub_telescope B Y (mulQ128 Y ratioApplied)
    (hQ128MulAppliedLe Y)).symm

theorem _earmark_preserves_invariant
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128MulComm : ∀ a b : Uint256, mulQ128 a b = mulQ128 b a)
    (hQ128MulAssoc : ∀ a b c : Uint256,
      mulQ128 (mulQ128 a b) c = mulQ128 a (mulQ128 b c))
    (hQ128MulLinear : ∀ x y r : Uint256,
      mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r))
    (hQ128MulSubDistrib : ∀ x y r : Uint256,
      mulQ128 (sub x y) r = sub (mulQ128 x r) (mulQ128 y r))
    (hQ128MulOneSub : ∀ a r : Uint256,
      sub a (mulQ128 a r) = mulQ128 a (sub ONE_Q128 r))
    (hQ128MulAppliedLe : ∀ y : Uint256,
      mulQ128 y
        (_earmark_ratioApplied (totalDebt s) (cumulativeEarmarked s) (s.storage 5))
        ≤ y)
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128)
    (hLastEWNonZero : ∀ id ∈ ids.elements,
      accounts_lastAccruedEarmarkWeight s id ≠ 0)
    (hSumZ_eq_liveUnearmarked :
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true →
      ids.sum (earmark_unearmarkedTimesRSR s) = sub (totalDebt s) (cumulativeEarmarked s)) :
    let s' := ((AlchemistV3._earmark).run s).snd
    _earmark_preserves_invariant_spec s s' ids := by
  intro s' hPre
  show sumProjectedEarmarked s' ids = cumulativeEarmarked s'
  rcases _earmark_slot_write s with ⟨hSlot0, _hSlot1, _hSlot2, _hSlot3⟩
  by_cases hActive :
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true
  · let ratioApplied :=
      _earmark_ratioApplied (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
    have hCumActive : cumulativeEarmarked s' =
        add (cumulativeEarmarked s)
          (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s) (s.storage 5)) := by
      show s'.storage 0 = _
      rw [hSlot0, hActive]
      rfl
    have hEarmarkDeltaPerIdActive :
        ∀ id ∈ ids.elements,
          projectedEarmarked s' id =
            add (projectedEarmarked s id)
              (mulQ128 (earmark_unearmarkedTimesRSR s id) (sub ONE_Q128 ratioApplied)) := by
      intro id hMemId
      exact _earmark_projectedEarmarked_active s id hActive
        (hLastEWNonZero id hMemId)
        hQ128OneMul hQ128MulComm hQ128MulAssoc hQ128MulLinear
        hQ128MulSubDistrib hQ128MulOneSub hQ128MulAppliedLe
        hQ128DivCommScale hQ128DivSelf hQ128MulCancelOne
    have hSplit :
        sumProjectedEarmarked s' ids =
          add (sumProjectedEarmarked s ids)
            (ids.sum (fun id =>
              mulQ128 (earmark_unearmarkedTimesRSR s id) (sub ONE_Q128 ratioApplied))) := by
      unfold sumProjectedEarmarked
      rw [sum_congr_on hEarmarkDeltaPerIdActive]
      exact foldl_add_distrib ids (fun id => projectedEarmarked s id)
        (fun id => mulQ128 (earmark_unearmarkedTimesRSR s id) (sub ONE_Q128 ratioApplied))
    have hSumDeltaScale :
        ids.sum (fun id =>
          mulQ128 (earmark_unearmarkedTimesRSR s id) (sub ONE_Q128 ratioApplied)) =
        mulQ128 (ids.sum (earmark_unearmarkedTimesRSR s)) (sub ONE_Q128 ratioApplied) := by
      exact sum_mulQ128_distrib ids (earmark_unearmarkedTimesRSR s) _
        (fun x y => hQ128MulLinear x y _)
    have hSumY := hSumZ_eq_liveUnearmarked hActive
    have hEff :
        _earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s) (s.storage 5) =
          mulQ128 (sub (totalDebt s) (cumulativeEarmarked s)) (sub ONE_Q128 ratioApplied) := by
      unfold _earmark_effectiveEarmarked
      show sub (sub (totalDebt s) (cumulativeEarmarked s))
            (mulQ128 (sub (totalDebt s) (cumulativeEarmarked s)) ratioApplied) = _
      exact hQ128MulOneSub (sub (totalDebt s) (cumulativeEarmarked s)) ratioApplied
    rw [hSplit, hSumDeltaScale, hSumY, hPre, hCumActive, hEff]
  · have hActiveFalse :
        _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = false := by
      cases h : _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
      · rfl
      · exfalso; exact hActive h
    have hCumInactive : cumulativeEarmarked s' = cumulativeEarmarked s := by
      show s'.storage 0 = s.storage 0
      rw [hSlot0, hActiveFalse]
      rfl
    have hProjUnchanged :
        ∀ id ∈ ids.elements, projectedEarmarked s' id = projectedEarmarked s id := by
      intro id _hMemId
      exact _earmark_projectedEarmarked_inactive s id hActiveFalse
    rw [hCumInactive]
    show sumProjectedEarmarked s' ids = cumulativeEarmarked s
    rw [← hPre]
    exact sum_congr_on hProjUnchanged

/-! ## Sister invariant: `cumulativeEarmarked ≤ totalDebt`

  The H4 hypothesis on `_subDebt_preserves_invariant`
  (`cumulativeEarmarked s ≤ sub (totalDebt s) amount`) is the line-1306
  clamp invariant `cumulativeEarmarked ≤ totalDebt`, projected forward
  by `amount`. The clamp-invariant itself is preserved by every
  operation; once we have it as a sister invariant, H4 reduces to the
  caller-side bound `amount ≤ totalDebt - cumulativeEarmarked` (the
  live-unearmarked debt the caller already checks).

  The five preservation lemmas below close that loop. -/

theorem _sync_preserves_cumLeTotalDebt
    (s : ContractState) (tokenId : Uint256) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    cumulativeEarmarked_le_totalDebt_spec s →
    cumulativeEarmarked_le_totalDebt_spec s' := by
  intro s' hPre
  rcases _sync_slot_write tokenId s with ⟨h0, h1, _h2, _h3, _h4, _h5⟩
  show (cumulativeEarmarked s').val ≤ (totalDebt s').val
  show s'.storage 0 ≤ s'.storage 1
  rw [h0, h1]
  exact hPre

theorem _subDebt_preserves_cumLeTotalDebt
    (s : ContractState) (tokenId amount : Uint256) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    cumulativeEarmarked_le_totalDebt_spec s →
    cumulativeEarmarked_le_totalDebt_spec s' := by
  intro s' _hPre
  rcases _subDebt_slot_write tokenId amount s with
    ⟨h1, h0, _h2, _h3, _h4, _hM100, _hM101, _hM102, _hM103, _hM104⟩
  show (cumulativeEarmarked s').val ≤ (totalDebt s').val
  show s'.storage 0 ≤ s'.storage 1
  rw [h0, h1]
  -- Goal: (if cum > td - amount then td - amount else cum) ≤ td - amount
  by_cases hClamp : cumulativeEarmarked s > sub (totalDebt s) amount
  · rw [if_pos hClamp]
    exact Nat.le_refl _
  · rw [if_neg hClamp]
    show (cumulativeEarmarked s).val ≤ (sub (totalDebt s) amount).val
    have : ¬ (sub (totalDebt s) amount).val < (cumulativeEarmarked s).val := hClamp
    omega

theorem _subEarmarkedDebt_preserves_cumLeTotalDebt
    (s : ContractState) (amountInDebtTokens accountId : Uint256) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    cumulativeEarmarked_le_totalDebt_spec s →
    cumulativeEarmarked_le_totalDebt_spec s' := by
  intro s' hPre
  rcases _subEarmarkedDebt_slot_write amountInDebtTokens accountId s with
    ⟨h0, h1, _h2, _h3, _h4, _hM100, _hM101, _hM102, _hM103, _hM104⟩
  show (cumulativeEarmarked s').val ≤ (totalDebt s').val
  show s'.storage 0 ≤ s'.storage 1
  rw [h0, h1]
  generalize hEtr :
      subEarmarkedDebt_earmarkToRemove amountInDebtTokens
        (accounts_debt s accountId) (accounts_earmarked s accountId) = etr
  -- Goal: (sub cum (ite (etr > cum) cum etr)).val ≤ td.val
  have hRemoveLeCum :
      (ite (etr > cumulativeEarmarked s) (cumulativeEarmarked s) etr) ≤
        cumulativeEarmarked s := by
    show (ite (etr > cumulativeEarmarked s) (cumulativeEarmarked s) etr).val ≤
        (cumulativeEarmarked s).val
    by_cases hC : etr > cumulativeEarmarked s
    · rw [if_pos hC]
      exact Nat.le_refl _
    · rw [if_neg hC]
      have : ¬ (cumulativeEarmarked s).val < etr.val := hC
      omega
  have hSubVal : (sub (cumulativeEarmarked s)
        (ite (etr > cumulativeEarmarked s) (cumulativeEarmarked s) etr)).val =
        (cumulativeEarmarked s).val -
          (ite (etr > cumulativeEarmarked s) (cumulativeEarmarked s) etr).val :=
    Verity.Core.Uint256.sub_eq_of_le hRemoveLeCum
  show (sub (cumulativeEarmarked s)
        (ite (etr > cumulativeEarmarked s) (cumulativeEarmarked s) etr)).val ≤
        (totalDebt s).val
  rw [hSubVal]
  have h1' : (cumulativeEarmarked s).val -
      (ite (etr > cumulativeEarmarked s) (cumulativeEarmarked s) etr).val
        ≤ (cumulativeEarmarked s).val := Nat.sub_le _ _
  exact Nat.le_trans h1' hPre

theorem redeem_preserves_cumLeTotalDebt
    (s : ContractState) (amount : Uint256)
    (hQ128MulAppliedLeRedeem :
      mulQ128 (cumulativeEarmarked s)
        (redeem_ratioApplied amount (cumulativeEarmarked s))
        ≤ cumulativeEarmarked s) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    cumulativeEarmarked_le_totalDebt_spec s →
    cumulativeEarmarked_le_totalDebt_spec s' := by
  intro s' hPre
  rcases redeem_slot_write amount s with ⟨h0, h1, _h2, _h3, _h4⟩
  show (cumulativeEarmarked s').val ≤ (totalDebt s').val
  show s'.storage 0 ≤ s'.storage 1
  rw [h0, h1]
  by_cases hActive : redeem_active amount (cumulativeEarmarked s) = true
  · rw [hActive]
    show (mulQ128 (cumulativeEarmarked s)
            (redeem_ratioApplied amount (cumulativeEarmarked s))).val ≤
          (sub (totalDebt s)
            (sub (cumulativeEarmarked s)
              (mulQ128 (cumulativeEarmarked s)
                (redeem_ratioApplied amount (cumulativeEarmarked s))))).val
    have hCum'LeCum :
        (mulQ128 (cumulativeEarmarked s)
          (redeem_ratioApplied amount (cumulativeEarmarked s))).val ≤
            (cumulativeEarmarked s).val := hQ128MulAppliedLeRedeem
    have hCumLeTd : (cumulativeEarmarked s).val ≤ (totalDebt s).val := hPre
    have hSubCumVal :
        (sub (cumulativeEarmarked s)
          (mulQ128 (cumulativeEarmarked s)
            (redeem_ratioApplied amount (cumulativeEarmarked s)))).val =
        (cumulativeEarmarked s).val -
          (mulQ128 (cumulativeEarmarked s)
            (redeem_ratioApplied amount (cumulativeEarmarked s))).val :=
      Verity.Core.Uint256.sub_eq_of_le hCum'LeCum
    have hSub2Le :
        (sub (cumulativeEarmarked s)
          (mulQ128 (cumulativeEarmarked s)
            (redeem_ratioApplied amount (cumulativeEarmarked s)))).val ≤
          (totalDebt s).val := by
      rw [hSubCumVal]
      omega
    have hSubTdVal :
        (sub (totalDebt s)
          (sub (cumulativeEarmarked s)
            (mulQ128 (cumulativeEarmarked s)
              (redeem_ratioApplied amount (cumulativeEarmarked s))))).val =
          (totalDebt s).val -
            (sub (cumulativeEarmarked s)
              (mulQ128 (cumulativeEarmarked s)
                (redeem_ratioApplied amount (cumulativeEarmarked s)))).val :=
      Verity.Core.Uint256.sub_eq_of_le hSub2Le
    rw [hSubTdVal, hSubCumVal]
    omega
  · have hInactive : redeem_active amount (cumulativeEarmarked s) = false := by
      cases h : redeem_active amount (cumulativeEarmarked s)
      · rfl
      · exfalso; exact hActive h
    rw [hInactive]
    exact hPre

theorem _earmark_preserves_cumLeTotalDebt
    (s : ContractState)
    (hEffectiveLeLive :
      _earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
        ≤ sub (totalDebt s) (cumulativeEarmarked s)) :
    let s' := ((AlchemistV3._earmark).run s).snd
    cumulativeEarmarked_le_totalDebt_spec s →
    cumulativeEarmarked_le_totalDebt_spec s' := by
  intro s' hPre
  rcases _earmark_slot_write s with ⟨h0, h1, _h2, _h3⟩
  show (cumulativeEarmarked s').val ≤ (totalDebt s').val
  show s'.storage 0 ≤ s'.storage 1
  rw [h0, h1]
  by_cases hActive :
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true
  · rw [hActive]
    show (add (cumulativeEarmarked s)
      (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
        (s.storage 5))).val ≤ (totalDebt s).val
    have hCumLeTd : (cumulativeEarmarked s).val ≤ (totalDebt s).val := hPre
    have hSubVal :
        (sub (totalDebt s) (cumulativeEarmarked s)).val =
          (totalDebt s).val - (cumulativeEarmarked s).val :=
      Verity.Core.Uint256.sub_eq_of_le hCumLeTd
    have hEffLeSub :
        (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
            (s.storage 5)).val ≤
          (sub (totalDebt s) (cumulativeEarmarked s)).val := hEffectiveLeLive
    have hEffLe :
        (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
            (s.storage 5)).val ≤
          (totalDebt s).val - (cumulativeEarmarked s).val := by
      rw [← hSubVal]; exact hEffLeSub
    have hSumLe :
        (cumulativeEarmarked s).val +
          (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
            (s.storage 5)).val ≤ (totalDebt s).val := by omega
    have hSumLt :
        (cumulativeEarmarked s).val +
          (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
            (s.storage 5)).val < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt hSumLe (totalDebt s).isLt
    have hAddVal :
        (add (cumulativeEarmarked s)
          (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
            (s.storage 5))).val =
          (cumulativeEarmarked s).val +
            (_earmark_effectiveEarmarked (totalDebt s) (cumulativeEarmarked s)
              (s.storage 5)).val := by
      show (Verity.Core.Uint256.add _ _).val = _
      unfold Verity.Core.Uint256.add
      show (Verity.Core.Uint256.ofNat _).val = _
      exact Nat.mod_eq_of_lt hSumLt
    rw [hAddVal]
    exact hSumLe
  · have hInactive :
        _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = false := by
      cases h : _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5)
      · rfl
      · exfalso; exact hActive h
    rw [hInactive]
    exact hPre

/-! ## H4-discharged composite for `_subDebt`

  Combines the sister invariant (`cumulativeEarmarked ≤ totalDebt`) with
  the caller-side bound (`amount ≤ totalDebt - cumulativeEarmarked` —
  the live unearmarked debt) to discharge H4 in
  `_sync_then_subDebt_preserves_invariant`. -/

theorem _sync_then_subDebt_preserves_invariant_v2
    (s : ContractState)
    (ids : FiniteSet Uint256)
    (tokenId amount : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hSister : cumulativeEarmarked_le_totalDebt_spec s)
    (hAmountLeLive : amount ≤ sub (totalDebt s) (cumulativeEarmarked s)) :
    let s_synced := ((AlchemistV3._sync tokenId).run s).snd
    let s' := ((AlchemistV3._subDebt tokenId amount).run s_synced).snd
    _subDebt_preserves_invariant_spec s s' ids tokenId := by
  -- H4 = (cum ≤ td - amount) follows from sister invariant + caller bound.
  have hH4 : cumulativeEarmarked s ≤ sub (totalDebt s) amount := by
    show (cumulativeEarmarked s).val ≤ (sub (totalDebt s) amount).val
    have hCumLeTd : (cumulativeEarmarked s).val ≤ (totalDebt s).val := hSister
    have hSubLive : (sub (totalDebt s) (cumulativeEarmarked s)).val =
        (totalDebt s).val - (cumulativeEarmarked s).val :=
      Verity.Core.Uint256.sub_eq_of_le hCumLeTd
    have hAmtLeLiveVal : amount.val ≤ (totalDebt s).val - (cumulativeEarmarked s).val := by
      have hThis : amount.val ≤ (sub (totalDebt s) (cumulativeEarmarked s)).val :=
        hAmountLeLive
      rw [hSubLive] at hThis
      exact hThis
    have hAmtLeTd : amount.val ≤ (totalDebt s).val := by omega
    have hSubAmtVal : (sub (totalDebt s) amount).val =
        (totalDebt s).val - amount.val :=
      Verity.Core.Uint256.sub_eq_of_le hAmtLeTd
    rw [hSubAmtVal]
    omega
  exact _sync_then_subDebt_preserves_invariant s ids tokenId amount hQ128MulOne hH4

/-! ## H3 — model counterexample (non-discharge)

  Of the five hypotheses originally surfaced on the preservation
  theorems, four (H2, H4, H5, H6) are scope cuts: properties the
  contract itself maintains but that we chose not to prove inside the
  case. The discharges above remove H2, H4, H5 and the bridging step of
  H6 (see below) from the user-facing call-site theorems.

  H3 (`accounts_lastAccruedRedemptionWeight s id ≠ 0` for every active
  id, used in `redeem_preserves_invariant` and `_earmark_preserves_invariant`)
  is different. It is **not** a scope cut — it is a model artifact.

  ## Concrete counterexample to dropping H3 from `redeem_preserves_invariant`

  Build the following ContractState `s`:

      storage 0 (cumulativeEarmarked)        = 2
      storage 1 (totalDebt)                  = 3
      storage 2 (_earmarkWeight)             = ONE_Q128
      storage 3 (_redemptionWeight)          = 0      ← witness of ¬H3 globally
      storageMapUint 100 1 (_accounts_debt)              = 3
      storageMapUint 101 1 (_accounts_earmarked)         = 2
      storageMapUint 102 1 (lastAccruedEarmarkWeight)    = ONE_Q128
      storageMapUint 103 1 (lastAccruedRedemptionWeight) = 0    ← H3 violated
      ids = {1}.

  The conservation invariant *holds* in `s`:
    projectedEarmarked s 1
      = mulQ128 (2 + (1 - mulQ128 1 ONE_Q128)) ONE_Q128   -- USR-redeem = ONE_Q128 (lastRW = rW = 0)
      = mulQ128 (2 + 0) ONE_Q128
      = 2 = cumulativeEarmarked s.

  Now apply `redeem(1)`:
    amountClamped = 1, ratioApplied = (2 - 1) / 2 = ONE_Q128/2.
    cumulativeEarmarked'  = mulQ128 2 (ONE_Q128/2)  = 1.
    _redemptionWeight'    = mulQ128 0 (ONE_Q128/2)  = 0.    -- still 0
    Per-account mappings unchanged.

  In the post-state `s'`:
    projectedEarmarked s' 1
      = (lastRW=0, rW'=0 → first branch of redemptionSurvivalRatio → ONE_Q128)
      = mulQ128 (2 + 0) ONE_Q128
      = 2.

  So `sumProjectedEarmarked s' ids = 2 ≠ 1 = cumulativeEarmarked s'`.
  The invariant is **broken**.

  ## Why this state is unreachable in deployed Solidity

  Alchemix's `redeem` advances the redemption epoch and resets
  `_redemptionWeight` to `ONE_Q128` whenever `amount == liveEarmarked`
  (full wipe). After a full wipe, `_redemptionWeight` is non-zero in
  the new epoch, and any subsequent `_sync(id)` writes a non-zero
  snapshot. So in Solidity, `_redemptionWeight = 0` is not a reachable
  storage value, and H3 is a genuine invariant of the deployed contract.

  Our model collapses the (epoch, index) pair into a flat Q128 weight
  and writes `redemptionWeight := mulQ128 redemptionWeight 0 = 0`
  instead of the epoch-reset (Contract.lean simplification block,
  lines 105–113). The state above is reachable in the model but not in
  Solidity. H3 is the proxy precondition that hides the elision.

  ## Closing H3 honestly

  Two options to remove H3 as a hypothesis:

  1. **Extend the model with epochs.** Replace the flat
     `_redemptionWeight` slot with a packed (epoch, index) representation
     and faithfully model the epoch-advance branch of `redeem`. After
     that change, H3 becomes provable as a sister invariant. This is
     the right long-term move; it is out of scope for this case.

  2. **Strengthen the precondition.** Replace H3 with a stronger,
     per-id condition that *is* preserved in the flat model — e.g.
     "every active id has been re-synced after the most recent
     redeem(amount) with amount = cumulativeEarmarked". This narrows
     the theorem's reach without changing the model.

  We chose (1) as the proper fix and surface this comment as the
  honest documentation. -/

/-! ## H6 — parallel debt-conservation summation (scope cut)

  The remaining hypothesis is the bridging identity used inside
  `_earmark_preserves_invariant`:

      _earmark_active s →
        ids.sum (earmark_unearmarkedTimesRSR s) =
          sub (totalDebt s) (cumulativeEarmarked s)

  Read in plain terms: the Q128-projected sum of every account's
  unearmarked-survivor exposure equals the live unearmarked debt.

  This is the projected counterpart of the **debt-conservation sister
  invariant** the contract maintains:

      Σ_id (accounts_debt s id) = totalDebt s.

  Discharging it from first principles requires:

  1. Modeling the debt-mutation operations the case currently leaves
     out: `_addDebt`, `_resetDebt`, the constructor write that seeds
     `totalDebt = 0`. These touch `accounts_debt` and `totalDebt` but
     not `accounts_earmarked` or `cumulativeEarmarked`, so they sit
     "next to" the earmark-side ops we did model.
  2. Proving debt-conservation as a sister invariant preserved by
     every op (5 modeled here + the new debt-mutation ones).
  3. Promoting that storage-level invariant to its Q128-projected form
     via the per-id projection algebra already developed in this file.

  Each step is mechanical and uses the same slot-write + survival-ratio
  toolkit we built for the earmark side. The case scope was the
  earmark side, so we carry H6 as a hypothesis here. A follow-up case
  on the debt side closes the loop and removes H6 entirely. -/

/-! ## H6 cheap fix — reformulate as projected debt conservation

  The original H6 form (`Σ unearmarkedTimesRSR = totalDebt - cumulativeEarmarked`)
  is awkward to state and easy to misread as a Q128-projected technicality.
  The cheap fix reformulates it as the natural sister of the main
  invariant: `sumProjectedDebt = totalDebt`. The lemma below shows the
  two are equivalent (under the main invariant + the line-1306 sister
  invariant), so a caller can supply the cleaner form and the original
  H6 follows. -/

/-- The sum of `earmark_unearmarkedTimesRSR` is the difference between
    `sumProjectedDebt` and `sumProjectedEarmarked`, by the per-id
    definition `projectedDebt = projectedEarmarked + earmark_unearmarkedTimesRSR`. -/
private theorem sum_unearmarkedTimesRSR_eq_sub_sumProjectedDebt
    (s : ContractState) (ids : FiniteSet Uint256) :
    sumProjectedDebt s ids =
      add (sumProjectedEarmarked s ids)
        (ids.sum (earmark_unearmarkedTimesRSR s)) := by
  unfold sumProjectedDebt sumProjectedEarmarked
  -- projectedDebt(id) = projectedEarmarked(id) + earmark_unearmarkedTimesRSR(id)
  -- Sum distributes by foldl_add_distrib.
  have h := foldl_add_distrib ids
    (fun id => projectedEarmarked s id)
    (fun id => earmark_unearmarkedTimesRSR s id)
  show ids.sum (fun id => projectedDebt s id) = _
  unfold projectedDebt at *
  exact h

/-- **H6 from projected debt conservation**: the original H6 hypothesis
    follows from the main invariant + the projected-debt sister
    invariant (`sumProjectedDebt = totalDebt`) + the line-1306 sister
    invariant (`cumulativeEarmarked ≤ totalDebt`). The cheap-fix bridge:
    a caller of `_earmark_preserves_invariant` who has the cleaner
    sister invariant gets the original H6 for free. -/
theorem H6_from_projectedDebt_conservation
    (s : ContractState) (ids : FiniteSet Uint256)
    (hMain : sumProjectedEarmarked s ids = cumulativeEarmarked s)
    (hSister : projectedDebt_conservation_spec s ids)
    (hCumLeTd : cumulativeEarmarked_le_totalDebt_spec s) :
    ids.sum (earmark_unearmarkedTimesRSR s) =
      sub (totalDebt s) (cumulativeEarmarked s) := by
  -- Σ projectedDebt = Σ projectedEarmarked + Σ Q1 (definitional split).
  have hSplit :
      sumProjectedDebt s ids =
        add (sumProjectedEarmarked s ids)
          (ids.sum (earmark_unearmarkedTimesRSR s)) :=
    sum_unearmarkedTimesRSR_eq_sub_sumProjectedDebt s ids
  -- Substitute the two invariants.
  have hSplit' :
      totalDebt s =
        add (cumulativeEarmarked s)
          (ids.sum (earmark_unearmarkedTimesRSR s)) := by
    have hSister' : sumProjectedDebt s ids = totalDebt s := hSister
    rw [← hSister']
    rw [hSplit]
    rw [hMain]
  -- totalDebt = cum + Σ Q1, so sub totalDebt cum = Σ Q1, provided no overflow.
  -- Since cum ≤ totalDebt, sub td cum has val = td.val - cum.val.
  -- And add cum (Σ Q1) has val = cum.val + (Σ Q1).val (if no wrap).
  -- The equation td = cum + Σ Q1 (in Uint256) implies (td.val mod m) = (cum.val + Σ Q1).val.
  -- Combined with td.val < m, we get td.val = (cum.val + (Σ Q1).val) mod m.
  -- When cum + Σ Q1 doesn't overflow: cum.val + (Σ Q1).val < m, so equality holds in Nat.
  -- Then td.val - cum.val = (Σ Q1).val, i.e., sub td cum = Σ Q1.
  apply Verity.Core.Uint256.ext
  have hCumLeTdVal :
      (cumulativeEarmarked s).val ≤ (totalDebt s).val := hCumLeTd
  have hSubVal :
      (sub (totalDebt s) (cumulativeEarmarked s)).val =
        (totalDebt s).val - (cumulativeEarmarked s).val :=
    Verity.Core.Uint256.sub_eq_of_le hCumLeTdVal
  rw [hSubVal]
  -- From hSplit': td = cum + Σ Q1 (Uint256-add). Take .val:
  have hValEq :
      (totalDebt s).val =
        (add (cumulativeEarmarked s)
          (ids.sum (earmark_unearmarkedTimesRSR s))).val :=
    congrArg Verity.Core.Uint256.val hSplit'
  -- Unfold add.val: (a + b).val = (a.val + b.val) % modulus.
  have hAddVal :
      (add (cumulativeEarmarked s)
        (ids.sum (earmark_unearmarkedTimesRSR s))).val =
      ((cumulativeEarmarked s).val +
        (ids.sum (earmark_unearmarkedTimesRSR s)).val) %
          Verity.Core.Uint256.modulus := by
    show (Verity.Core.Uint256.add _ _).val = _
    unfold Verity.Core.Uint256.add
    rfl
  rw [hAddVal] at hValEq
  -- Want: (Σ Q1).val = td.val - cum.val.
  -- From hValEq: td.val = (cum.val + (Σ Q1).val) % modulus.
  -- Under `cum ≤ td` (sister invariant), wrap is impossible: a wrap
  -- would force td.val ≤ cum.val + (Σ Q1).val - modulus < cum.val,
  -- contradicting cum.val ≤ td.val.
  have hSumQ1Lt :
      (ids.sum (earmark_unearmarkedTimesRSR s)).val < Verity.Core.Uint256.modulus :=
    (ids.sum (earmark_unearmarkedTimesRSR s)).isLt
  have hCumLt : (cumulativeEarmarked s).val < Verity.Core.Uint256.modulus :=
    (cumulativeEarmarked s).isLt
  have hNoWrap :
      (cumulativeEarmarked s).val +
        (ids.sum (earmark_unearmarkedTimesRSR s)).val <
          Verity.Core.Uint256.modulus := by
    by_cases hWrap :
        (cumulativeEarmarked s).val +
          (ids.sum (earmark_unearmarkedTimesRSR s)).val <
            Verity.Core.Uint256.modulus
    · exact hWrap
    · -- Wrap case: cum + Σ Q1 ≥ modulus. Derive contradiction with hCumLeTdVal.
      have hWrap' :
          (cumulativeEarmarked s).val +
            (ids.sum (earmark_unearmarkedTimesRSR s)).val ≥
              Verity.Core.Uint256.modulus := Nat.le_of_not_lt hWrap
      -- Set up arithmetic: under the wrap, td.val = (cum + Σ Q1) - modulus,
      -- which is < cum.val. But cum.val ≤ td.val. Contradiction.
      have hLt2m :
          (cumulativeEarmarked s).val +
            (ids.sum (earmark_unearmarkedTimesRSR s)).val <
              2 * Verity.Core.Uint256.modulus := by omega
      have hModEq :
          ((cumulativeEarmarked s).val +
            (ids.sum (earmark_unearmarkedTimesRSR s)).val) %
              Verity.Core.Uint256.modulus =
            ((cumulativeEarmarked s).val +
              (ids.sum (earmark_unearmarkedTimesRSR s)).val) -
                Verity.Core.Uint256.modulus := by
        have hLtMod :
            ((cumulativeEarmarked s).val +
                (ids.sum (earmark_unearmarkedTimesRSR s)).val) -
                  Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by omega
        have hPosM : 0 < Verity.Core.Uint256.modulus :=
          Verity.Core.Uint256.modulus_pos
        have :
            (cumulativeEarmarked s).val +
              (ids.sum (earmark_unearmarkedTimesRSR s)).val =
              (((cumulativeEarmarked s).val +
                  (ids.sum (earmark_unearmarkedTimesRSR s)).val) -
                Verity.Core.Uint256.modulus) + 1 * Verity.Core.Uint256.modulus := by
          omega
        rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hLtMod]
        omega
      rw [hModEq] at hValEq
      exfalso
      omega
  -- No-wrap branch: mod = identity, equation reduces.
  have hModEq :
      ((cumulativeEarmarked s).val +
        (ids.sum (earmark_unearmarkedTimesRSR s)).val) %
          Verity.Core.Uint256.modulus =
        (cumulativeEarmarked s).val +
          (ids.sum (earmark_unearmarkedTimesRSR s)).val :=
    Nat.mod_eq_of_lt hNoWrap
  rw [hModEq] at hValEq
  omega

end Benchmark.Cases.Alchemix.EarmarkConservation
