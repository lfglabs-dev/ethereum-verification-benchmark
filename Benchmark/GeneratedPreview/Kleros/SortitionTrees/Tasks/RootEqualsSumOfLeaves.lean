import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
Executing `setLeaf` recomputes the root as the sum of the four leaf weights.
-/
theorem root_equals_sum_of_leaves
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 3)
    (hHigh : nodeIndex <= 6) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    root_equals_sum_of_leaves_spec s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold root_equals_sum_of_leaves_spec
  grind [SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes, SortitionTrees.selectedNode]

end Benchmark.Cases.Kleros.SortitionTrees
