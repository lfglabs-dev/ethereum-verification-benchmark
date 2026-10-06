import Mathlib.Init

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

@[simp] theorem get_set_bang_self [Inhabited α] (xs : Array α)
    (i : Nat) (v : α) (hi : i < xs.size) : (xs.set! i v)[i]! = v := by
  rw [← Array.getElem!_toList]
  simp [Array.set!, Array.toList_setIfInBounds, hi]

@[simp] theorem get_set_bang_ne [Inhabited α] (xs : Array α)
    (i j : Nat) (v : α) (hij : i ≠ j) : (xs.set! i v)[j]! = xs[j]! := by
  rw [← Array.getElem!_toList, ← Array.getElem!_toList]
  simp [Array.set!, Array.toList_setIfInBounds, hij]

@[simp] theorem get_push_old [Inhabited α] (xs : Array α)
    (i : Nat) (v : α) (hi : i < xs.size) : (xs.push v)[i]! = xs[i]! := by
  rw [← Array.getElem!_toList, ← Array.getElem!_toList]
  simp [Array.toList_push, List.getElem!_eq_getElem?_getD, List.getElem?_append_left, hi]

@[simp] theorem get_push_new [Inhabited α] (xs : Array α)
    (v : α) : (xs.push v)[xs.size]! = v := by
  rw [← Array.getElem!_toList]
  simp [Array.toList_push]

@[simp] theorem size_set_bang (xs : Array α) (i : Nat) (v : α) :
    (xs.set! i v).size = xs.size := by
  simp [Array.set!]

/-- A pushed array retains the membership of every old element. -/
theorem mem_push_of_mem (xs : Array α) (v a : α)
    (ha : a ∈ xs.toList) : a ∈ (xs.push v).toList := by
  simpa only [Array.toList_push, List.mem_append] using Or.inl ha

/-- The source uses `.back!` to read its last endpoint on append. -/
theorem back_bang_eq_get (xs : Array α) [Inhabited α] (h : 0 < xs.size) :
    xs.back! = xs[xs.size - 1]! := by
  simp only [Array.back!, Array.getElem!_eq_getD]

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
