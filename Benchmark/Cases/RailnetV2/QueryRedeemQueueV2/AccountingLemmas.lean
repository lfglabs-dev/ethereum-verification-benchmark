import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Group.Nat

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.AccountingLemmas

/-- Integer-floor allocation is superadditive in the allocated width. -/
theorem floor_add_le (x y A L : ℕ) (_hL : 0 < L) :
    x * A / L + y * A / L ≤ (x + y) * A / L := by
  simpa only [add_mul] using Nat.add_div_le_add_div (x * A) (y * A) L

/-- Arbitrarily many widths totalling at most `L` allocate at most `A`. -/
theorem floor_list_sum_le (xs : List ℕ) (A L : ℕ) (hL : 0 < L)
    (hxs : xs.sum ≤ L) :
    (xs.map (fun x => x * A / L)).sum ≤ A := by
  have hgeneral (ys : List ℕ) :
      (ys.map (fun x => x * A / L)).sum ≤ ys.sum * A / L := by
    induction ys with
    | nil => simp
    | cons x ys ih =>
      simpa only [List.map_cons, List.sum_cons] using
        (le_trans (add_le_add_right ih (x * A / L))
          (by simpa only [add_mul] using
            (Nat.add_div_le_add_div (x * A) (ys.sum * A) L)))
  calc
    (xs.map (fun x => x * A / L)).sum ≤ xs.sum * A / L := hgeneral xs
    _ ≤ L * A / L := Nat.div_le_div_right (Nat.mul_le_mul_right A hxs)
    _ = A := Nat.mul_div_cancel_left A hL

/-- The capacity of an interval dominates the floor allocation of its width,
without requiring that the interval lie inside `[0,L)`. -/
theorem floor_width_le_interval (a x A L : ℕ) (hL : 0 < L) :
    x * A / L ≤ (a + x) * A / L - a * A / L := by
  have h := floor_add_le a x A L hL
  exact Nat.le_sub_of_add_le (by simpa only [add_comm] using h)

/-- Nonnegative integer capacity assigned to raw position `j`. -/
def capacity (j A L : ℕ) : ℕ := (j + 1) * A / L - j * A / L

theorem capacity_nonneg (j A L : ℕ) : 0 ≤ capacity j A L := Nat.zero_le _

/-- Capacities telescope over any ordered finite position interval. -/
theorem capacity_sum_Ico (a b A L : ℕ) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, capacity j A L = b * A / L - a * A / L := by
  have hmono : Monotone (fun j : ℕ => j * A / L) := by
    intro i j hij
    exact Nat.div_le_div_right (Nat.mul_le_mul_right A hij)
  have hr (n : ℕ) : ∑ j ∈ Finset.range n, capacity j A L = n * A / L := by
    simp only [capacity, Finset.sum_range_tsub hmono, Nat.zero_mul,
      Nat.zero_div, Nat.sub_zero]
  have hs := Finset.sum_range_add_sum_Ico (fun j => capacity j A L) hab
  rw [hr a, hr b] at hs
  exact Nat.eq_sub_of_add_eq ((add_comm _ _).trans hs)

/-- The capacities across all `L` raw positions add up to `A`. -/
theorem capacity_sum_full (A L : ℕ) (hL : 0 < L) :
    ∑ j ∈ Finset.Ico 0 L, capacity j A L = A := by
  simpa only [Nat.zero_mul, Nat.zero_div, Nat.sub_zero, Nat.mul_div_cancel_left A hL]
    using capacity_sum_Ico 0 L A L (Nat.zero_le L)

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.AccountingLemmas
