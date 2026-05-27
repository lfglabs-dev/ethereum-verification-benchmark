import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
Any successful `draw` resolves to one of the four leaf node indices.
-/
theorem draw_selects_valid_leaf
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_selects_valid_leaf_spec s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold draw_selects_valid_leaf_spec
  grind [SortitionTrees.draw, SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes, SortitionTrees.selectedNode]

end Benchmark.Cases.Kleros.SortitionTrees
