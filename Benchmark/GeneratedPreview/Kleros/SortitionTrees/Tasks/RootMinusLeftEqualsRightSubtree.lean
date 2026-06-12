import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

private theorem parent_equals_sum_of_children
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 3)
    (hHigh : nodeIndex <= 6) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    parent_equals_sum_of_children_spec s' := by
  by_cases h3 : nodeIndex == 3
  · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, parent_equals_sum_of_children_spec,
      SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0,
      SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs,
      SortitionTrees.IDsToNodeIndexes, getStorage, setStorage, setMappingUint, Verity.require,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
  · by_cases h4 : nodeIndex == 4
    · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h4, parent_equals_sum_of_children_spec,
        SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0,
        SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs,
        SortitionTrees.IDsToNodeIndexes, getStorage, setStorage, setMappingUint, Verity.require,
        Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
    · by_cases h5 : nodeIndex == 5
      · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h4, h5, parent_equals_sum_of_children_spec,
          SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0,
          SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs,
          SortitionTrees.IDsToNodeIndexes, getStorage, setStorage, setMappingUint, Verity.require,
          Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
      · by_cases h6 : nodeIndex == 6
        · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h4, h5, h6, parent_equals_sum_of_children_spec,
            SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.rightSum, SortitionTrees.leaf0,
            SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3, SortitionTrees.nodeIndexesToIDs,
            SortitionTrees.IDsToNodeIndexes, getStorage, setStorage, setMappingUint, Verity.require,
            Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
        · exfalso
          have hLow' : (3 : Nat) ≤ nodeIndex.val := by simpa using hLow
          have hHigh' : nodeIndex.val ≤ 6 := by simpa using hHigh
          have h3ne : nodeIndex ≠ 3 := by simpa using h3
          have h4ne : nodeIndex ≠ 4 := by simpa using h4
          have h5ne : nodeIndex ≠ 5 := by simpa using h5
          have h6ne : nodeIndex ≠ 6 := by simpa using h6
          have h3' : nodeIndex.val ≠ 3 := by intro hv; apply h3ne; exact Verity.Core.Uint256.ext hv
          have h4' : nodeIndex.val ≠ 4 := by intro hv; apply h4ne; exact Verity.Core.Uint256.ext hv
          have h5' : nodeIndex.val ≠ 5 := by intro hv; apply h5ne; exact Verity.Core.Uint256.ext hv
          have h6' : nodeIndex.val ≠ 6 := by intro hv; apply h6ne; exact Verity.Core.Uint256.ext hv
          omega

private theorem root_equals_sum_of_leaves
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 3)
    (hHigh : nodeIndex <= 6) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    root_equals_sum_of_leaves_spec s' := by
  let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
  have hParents : parent_equals_sum_of_children_spec s' := by
    simpa [s'] using parent_equals_sum_of_children nodeIndex stakePathID weight s hLow hHigh
  have hRootParents : s'.storage 0 = add (s'.storage 1) (s'.storage 2) := by
    by_cases h3 : nodeIndex == 3
    · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.leftSum,
        SortitionTrees.rightSum, hLow, hHigh, h3, getStorage, setStorage, setMappingUint,
        Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
    · by_cases h4 : nodeIndex == 4
      · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.leftSum,
          SortitionTrees.rightSum, hLow, hHigh, h3, h4, getStorage, setStorage, setMappingUint,
          Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
      · by_cases h5 : nodeIndex == 5
        · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.leftSum,
            SortitionTrees.rightSum, hLow, hHigh, h3, h4, h5, getStorage, setStorage, setMappingUint,
            Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
        · by_cases h6 : nodeIndex == 6
          · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.leftSum,
              SortitionTrees.rightSum, hLow, hHigh, h3, h4, h5, h6, getStorage, setStorage,
              setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
          · exfalso
            have hLow' : (3 : Nat) ≤ nodeIndex.val := by simpa using hLow
            have hHigh' : nodeIndex.val ≤ 6 := by simpa using hHigh
            have h3ne : nodeIndex ≠ 3 := by simpa using h3
            have h4ne : nodeIndex ≠ 4 := by simpa using h4
            have h5ne : nodeIndex ≠ 5 := by simpa using h5
            have h6ne : nodeIndex ≠ 6 := by simpa using h6
            have h3' : nodeIndex.val ≠ 3 := by intro hv; apply h3ne; exact Verity.Core.Uint256.ext hv
            have h4' : nodeIndex.val ≠ 4 := by intro hv; apply h4ne; exact Verity.Core.Uint256.ext hv
            have h5' : nodeIndex.val ≠ 5 := by intro hv; apply h5ne; exact Verity.Core.Uint256.ext hv
            have h6' : nodeIndex.val ≠ 6 := by intro hv; apply h6ne; exact Verity.Core.Uint256.ext hv
            omega
  rcases hParents with ⟨hLeft, hRight⟩
  unfold root_equals_sum_of_leaves_spec leaf_sum
  calc
    s'.storage 0 = add (s'.storage 1) (s'.storage 2) := hRootParents
    _ = add (add (s'.storage 3) (s'.storage 4)) (add (s'.storage 5) (s'.storage 6)) := by
          rw [hLeft, hRight]

/--
Executing `setLeaf` keeps the root partitioned into left and right subtree
weights.
-/
theorem root_minus_left_equals_right_subtree
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 3)
    (hHigh : nodeIndex <= 6) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    root_minus_left_equals_right_subtree_spec s' := by
  let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
  have hParents : parent_equals_sum_of_children_spec s' := by
    simpa [s'] using parent_equals_sum_of_children nodeIndex stakePathID weight s hLow hHigh
  have hRoot : root_equals_sum_of_leaves_spec s' := by
    simpa [s'] using root_equals_sum_of_leaves nodeIndex stakePathID weight s hLow hHigh
  have hRootLR : s'.storage 0 = add (s'.storage 1) (s'.storage 2) := by
    rcases hParents with ⟨hLeft, hRight⟩
    unfold root_equals_sum_of_leaves_spec at hRoot
    unfold leaf_sum at hRoot
    calc
      s'.storage 0 = add (add (s'.storage 3) (s'.storage 4)) (add (s'.storage 5) (s'.storage 6)) := hRoot
      _ = add (s'.storage 1) (s'.storage 2) := by rw [← hLeft, ← hRight]
  unfold root_minus_left_equals_right_subtree_spec
  dsimp
  apply Verity.Core.Uint256.add_right_cancel
  calc
    ((s'.storage 0 - s'.storage 1) + s'.storage 1) = s'.storage 0 := by
      exact Verity.Core.Uint256.sub_add_cancel_left (s'.storage 0) (s'.storage 1)
    _ = add (s'.storage 1) (s'.storage 2) := hRootLR
    _ = (s'.storage 2) + (s'.storage 1) := by
          exact Verity.Core.Uint256.add_comm (s'.storage 1) (s'.storage 2)

end Benchmark.Cases.Kleros.SortitionTrees
