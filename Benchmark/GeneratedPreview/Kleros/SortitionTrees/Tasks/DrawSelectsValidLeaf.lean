import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

private theorem draw_selected_node
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    s'.storage 9 =
      ite (ticket < s.storage 1)
        (ite (ticket < s.storage 3) 3 4)
        (ite (sub ticket (s.storage 1) < s.storage 5) 5 6) := by
  have hRoot' : ¬ s.storage 0 = 0 := by
    intro hEq
    simp [hEq] at hRoot
  simp [SortitionTrees.draw, SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.leaf0,
    SortitionTrees.leaf2, SortitionTrees.selectedNode, hRoot', hInRange, getStorage, setStorage,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

/--
Any successful `draw` resolves to one of the four leaf node indices.
-/
theorem draw_selects_valid_leaf
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_selects_valid_leaf_spec s' := by
  unfold draw_selects_valid_leaf_spec
  dsimp
  rw [draw_selected_node ticket s hRoot hInRange]
  by_cases hLeft : ticket < s.storage 1
  · by_cases hLeaf0 : ticket < s.storage 3
    · simp [hLeft, hLeaf0]
      decide
    · simp [hLeft, hLeaf0]
      decide
  · by_cases hLeaf2 : sub ticket (s.storage 1) < s.storage 5
    · simp [hLeft, hLeaf2]
      decide
    · simp [hLeft, hLeaf2]
      decide

end Benchmark.Cases.Kleros.SortitionTrees
