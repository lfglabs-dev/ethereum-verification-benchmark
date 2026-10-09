import Benchmark.Cases.Dromos.AllocationConservation.Specs
import Init.Data.List.Nat.Pairwise

/-! Concrete logical-array and stored-position refinement lemmas. No domain axioms. -/
namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity
set_option maxHeartbeats 1000000

namespace SetRefinement

def PositionLaw (xs : List Uint256) (p : Uint256 → Nat) : Prop :=
  (∀ c, c ∉ xs → p c = 0) ∧ ∀ i (h : i < xs.length), p xs[i] = i + 1

theorem expected_at (xs : List Uint256) (hn : xs.Nodup) (i : Nat)
    (hi : i < xs.length) : expectedPosition xs xs[i] = i + 1 := by
  have hf : xs.findIdx? (fun c => c == xs[i]) = some i := by
    apply List.findIdx?_eq_some_iff_getElem.mpr
    refine ⟨hi, by simp, ?_⟩
    intro j hj he
    have heq : xs[j] = xs[i] := by simpa using he
    have hij := (List.getElem_inj hn).mp heq
    omega
  simp [expectedPosition, hf]

theorem expected_absent (xs : List Uint256) (c : Uint256) (hc : c ∉ xs) :
    expectedPosition xs c = 0 := by
  have hf : xs.findIdx? (fun d => d == c) = none :=
    List.findIdx?_eq_none_iff.mpr (fun d hd => by
      have hne : d ≠ c := by intro h; subst d; exact hc hd
      simpa using hne)
  simp [expectedPosition, hf]

theorem law_expected (xs : List Uint256) (hn : xs.Nodup) :
    PositionLaw xs (expectedPosition xs) :=
  ⟨fun c hc => expected_absent xs c hc, fun i hi => expected_at xs hn i hi⟩

theorem law_nodup {xs : List Uint256} {p : Uint256 → Nat} (h : PositionLaw xs p) :
    xs.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  have hp := congrArg p he
  rw [h.2 i hi, h.2 j hj] at hp
  omega

theorem law_eq_expected {xs : List Uint256} {p : Uint256 → Nat}
    (h : PositionLaw xs p) (c : Uint256) : p c = expectedPosition xs c := by
  by_cases hc : c ∈ xs
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
    rw [← he, h.2 i hi, expected_at xs (law_nodup h) i hi]
  · rw [h.1 c hc, expected_absent xs c hc]

def swapPop (xs : List Uint256) (i : Nat) : List Uint256 :=
  (xs.set i xs.getLast!).dropLast

@[simp] theorem swap_length (xs : List Uint256) (i : Nat) :
    (swapPop xs i).length = xs.length - 1 := by simp [swapPop]

theorem last_eq_index (xs : List Uint256) (h : 0 < xs.length) :
    xs.getLast! = xs[xs.length - 1]'(by omega) := by
  have hn : xs ≠ [] := by intro he; simp [he] at h
  simp [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast hn,
    List.getLast_eq_getElem]

theorem swap_at (xs : List Uint256) (i j : Nat) (hj : j < (swapPop xs i).length) :
    (swapPop xs i)[j] = if j = i then xs.getLast! else xs[j]'(by simp at hj; omega) := by
  simp only [swapPop, List.getElem_dropLast]
  by_cases he : j = i
  · subst j; simp
  · simp only [he, ite_false]
    exact List.getElem_set_ne (Ne.symm he) _

theorem swap_members (xs : List Uint256) (hn : xs.Nodup) (i : Nat) (hi : i < xs.length)
    (d : Uint256) : d ∈ swapPop xs i ↔ d ≠ xs[i] ∧ d ∈ xs := by
  have hl : 0 < xs.length := by omega
  have hlast := last_eq_index xs hl
  constructor
  · intro hm
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
    rw [swap_at] at he
    by_cases hji : j = i
    · simp only [hji, ite_true] at he
      refine ⟨?_, ?_⟩
      · intro hd
        have hidx := (List.getElem_inj hn).mp (hlast.symm.trans (he.trans hd))
        simp only [swap_length] at hj
        omega
      · rw [← he, hlast]; exact List.getElem_mem _
    · simp only [hji, ite_false] at he
      refine ⟨?_, ?_⟩
      · intro hd
        have hidx := (List.getElem_inj hn).mp (he.trans hd)
        exact hji hidx
      · rw [← he]; exact List.getElem_mem _
  · rintro ⟨hne, hm⟩
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
    have hji : j ≠ i := by intro h; subst j; exact hne he.symm
    by_cases hjlast : j = xs.length - 1
    · have hil : i < xs.length - 1 := by omega
      apply List.mem_iff_getElem.mpr
      refine ⟨i, by simpa using hil, ?_⟩
      rw [swap_at]
      simp only [ite_true]
      rw [hlast]
      simpa only [hjlast] using he
    · apply List.mem_iff_getElem.mpr
      refine ⟨j, by simp; omega, ?_⟩
      rw [swap_at]
      simp [hji, he]

def removedPosition (xs : List Uint256) (i : Nat) (p : Uint256 → Nat) (d : Uint256) : Nat :=
  if d = xs[i]! then 0 else if d = xs.getLast! then i + 1 else p d

theorem swap_law (xs : List Uint256) (p : Uint256 → Nat) (h : PositionLaw xs p)
    (i : Nat) (hi : i < xs.length) : PositionLaw (swapPop xs i) (removedPosition xs i p) := by
  have hn := law_nodup h
  have hl : 0 < xs.length := by omega
  have hlast := last_eq_index xs hl
  have hbang : xs[i]! = xs[i] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  refine ⟨?_, ?_⟩
  · intro d hd
    by_cases hdi : d = xs[i]
    · simp [removedPosition, hbang, hdi]
    · have hnot : d ∉ xs := by
        intro hm; exact hd ((swap_members xs hn i hi d).mpr ⟨hdi, hm⟩)
      have hdlast : d ≠ xs.getLast! := by
        intro he; apply hnot; rw [he, hlast]; exact List.getElem_mem _
      simp only [removedPosition, hbang, hdi, hdlast, ite_false, h.1 d hnot]
  · intro j hj
    have hjx : j < xs.length := by simp only [swap_length] at hj; omega
    have hmem : (swapPop xs i)[j] ∈ swapPop xs i := List.getElem_mem _
    have hne := ((swap_members xs hn i hi _).mp hmem).1
    rw [removedPosition, hbang]
    simp only [hne, ite_false]
    rw [swap_at]
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ite_false]
      have hnotlast : xs[j] ≠ xs.getLast! := by
        intro he
        have hjl := (List.getElem_inj hn).mp (he.trans hlast)
        simp only [swap_length] at hj
        omega
      simp only [hnotlast, ite_false, h.2 j hjx]

theorem append_law (xs : List Uint256) (p : Uint256 → Nat) (h : PositionLaw xs p)
    (c : Uint256) (hc : c ∉ xs) :
    PositionLaw (xs ++ [c]) (fun d => if d = c then xs.length + 1 else p d) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    have hd' : d ∉ xs ∧ d ≠ c := by simpa using hd
    simp [hd'.2, h.1 d hd'.1]
  · intro i hi
    by_cases hil : i < xs.length
    · rw [List.getElem_append_left hil]
      have hne : xs[i] ≠ c := by intro he; exact hc (he ▸ List.getElem_mem hil)
      simp [hne, h.2 i hil]
    · have hie : i = xs.length := by simp at hi; omega
      subst i
      simp

end SetRefinement
end Benchmark.Cases.Dromos.AllocationConservation
