import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
Executing `draw` follows the encoded ticket intervals used by the
implementation.
-/
theorem draw_interval_matches_weights
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_interval_matches_weights_spec ticket s s' := by
  try simp only [grind_norm] at *
  try unfold draw_interval_matches_weights_spec
  try unfold SortitionTrees.rootSum
  try unfold SortitionTrees.leftSum
  try unfold SortitionTrees.rightSum
  try unfold SortitionTrees.leaf0
  try unfold SortitionTrees.leaf1
  try unfold SortitionTrees.leaf2
  try unfold SortitionTrees.leaf3
  try unfold SortitionTrees.nodeIndexesToIDs
  try unfold SortitionTrees.IDsToNodeIndexes
  try unfold SortitionTrees.selectedNode
  try unfold SortitionTrees.setLeaf
  try unfold SortitionTrees.draw
  try unfold leaf_sum
  try unfold parent_equals_sum_of_children_spec
  try unfold root_equals_sum_of_leaves_spec
  try unfold draw_interval_matches_weights_spec
  try unfold draw_selects_valid_leaf_spec
  try unfold node_id_bijection_spec
  try unfold root_minus_left_equals_right_subtree_spec
  simp [grind_norm, SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes, SortitionTrees.selectedNode, SortitionTrees.setLeaf, SortitionTrees.draw, leaf_sum, parent_equals_sum_of_children_spec, root_equals_sum_of_leaves_spec, draw_interval_matches_weights_spec, draw_selects_valid_leaf_spec, node_id_bijection_spec, root_minus_left_equals_right_subtree_spec, *]
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega

end Benchmark.Cases.Kleros.SortitionTrees
