import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.AccountingLemmas
import Mathlib.Tactic

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.IntervalLemmas

/-- Half-open intervals encoded by `(start, length)` are separated in either order. -/
def separated (a b : ℕ × ℕ) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

/-- The actual positions occupied by a half-open interval. -/
def positions (p : ℕ × ℕ) : Finset ℕ := Finset.Ico p.1 (p.1 + p.2)

/-- The union of positions occupied by a finite list of intervals. -/
def occupied (xs : List (ℕ × ℕ)) : Finset ℕ :=
  xs.foldr (fun p acc => positions p ∪ acc) ∅

private theorem positions_card (p : ℕ × ℕ) : (positions p).card = p.2 := by
  simp [positions]

private theorem positions_disjoint (a b : ℕ × ℕ) (h : separated a b) :
    Disjoint (positions a) (positions b) := by
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  simp only [positions, Finset.mem_Ico] at hja hjb
  rcases h with h | h <;> omega

private theorem mem_occupied_iff (xs : List (ℕ × ℕ)) (j : ℕ) :
    j ∈ occupied xs ↔ ∃ p ∈ xs, j ∈ positions p := by
  induction xs with
  | nil => simp [occupied]
  | cons p ps ih =>
    change j ∈ positions p ∪ occupied ps ↔ ∃ q ∈ p :: ps, j ∈ positions q
    simp only [Finset.mem_union, List.mem_cons, exists_eq_or_imp, ih]

private theorem occupied_card_eq_sum (xs : List (ℕ × ℕ))
    (hsep : xs.Pairwise separated) :
    (occupied xs).card = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => simp [occupied]
  | cons p ps ih =>
    have hp : ∀ q ∈ ps, separated p q := (List.pairwise_cons.mp hsep).1
    have hps : ps.Pairwise separated := (List.pairwise_cons.mp hsep).2
    have hd : Disjoint (positions p) (occupied ps) := by
      apply Finset.disjoint_left.mpr
      intro j hjp hjs
      obtain ⟨q, hq, hjq⟩ := (mem_occupied_iff ps j).mp hjs
      exact (Finset.disjoint_left.mp (positions_disjoint p q (hp q hq))) hjp hjq
    change (positions p ∪ occupied ps).card =
      p.2 + (ps.map Prod.snd).sum
    rw [Finset.card_union_of_disjoint hd, positions_card, ih hps]

private theorem occupied_subset (xs : List (ℕ × ℕ)) (L : ℕ)
    (hend : ∀ p ∈ xs, p.1 + p.2 ≤ L) : occupied xs ⊆ Finset.Ico 0 L := by
  intro j hj
  obtain ⟨p, hp, hjp⟩ := (mem_occupied_iff xs j).mp hj
  simp only [positions, Finset.mem_Ico] at hjp
  simp only [Finset.mem_Ico]
  exact ⟨Nat.zero_le j, lt_of_lt_of_le hjp.2 (hend p hp)⟩

/-- Arbitrary-order pairwise-separated half-open Nat intervals inside `[0,L)`
occupy no more than `L` positions in total. Zero-length intervals are allowed. -/
theorem sum_widths_le (xs : List (ℕ × ℕ)) (L : ℕ)
    (hsep : xs.Pairwise separated)
    (hend : ∀ p ∈ xs, p.1 + p.2 ≤ L) :
    (xs.map Prod.snd).sum ≤ L := by
  calc
    (xs.map Prod.snd).sum = (occupied xs).card := (occupied_card_eq_sum xs hsep).symm
    _ ≤ (Finset.Ico 0 L).card := Finset.card_le_card (occupied_subset xs L hend)
    _ = L := by simp

/-- Capacity accounting splits at any interior boundary. The summands are
computed by the existing telescoping `capacity_sum_Ico` theorem. -/
theorem capacity_sum_split (a m b A L : ℕ) (ham : a ≤ m) (hmb : m ≤ b) :
    (∑ j ∈ Finset.Ico a m, AccountingLemmas.capacity j A L) +
      (∑ j ∈ Finset.Ico m b, AccountingLemmas.capacity j A L) =
        ∑ j ∈ Finset.Ico a b, AccountingLemmas.capacity j A L := by
  rw [AccountingLemmas.capacity_sum_Ico a m A L ham,
    AccountingLemmas.capacity_sum_Ico m b A L hmb,
    AccountingLemmas.capacity_sum_Ico a b A L (ham.trans hmb)]
  have h₁ : a * A / L ≤ m * A / L :=
    Nat.div_le_div_right (Nat.mul_le_mul_right A ham)
  have h₂ : m * A / L ≤ b * A / L :=
    Nat.div_le_div_right (Nat.mul_le_mul_right A hmb)
  omega

/-- The same capacity bound translated to an arbitrary base position `p`.
    No uint256 bound is imposed on the arithmetic sum. -/
theorem sum_widths_le_offset (xs : List (ℕ × ℕ)) (p L : ℕ)
    (hsep : xs.Pairwise separated)
    (hstart : ∀ a ∈ xs, p ≤ a.1)
    (hend : ∀ a ∈ xs, a.1 + a.2 ≤ p + L) :
    (xs.map Prod.snd).sum ≤ L := by
  have hsubset : occupied xs ⊆ Finset.Ico p (p + L) := by
    intro j hj
    obtain ⟨a, ha, hja⟩ := (mem_occupied_iff xs j).mp hj
    simp only [positions, Finset.mem_Ico] at hja
    exact Finset.mem_Ico.mpr ⟨(hstart a ha).trans hja.1,
      lt_of_lt_of_le hja.2 (hend a ha)⟩
  calc
    (xs.map Prod.snd).sum = (occupied xs).card := (occupied_card_eq_sum xs hsep).symm
    _ ≤ (Finset.Ico p (p + L)).card := Finset.card_le_card hsubset
    _ = L := by simp

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.IntervalLemmas
