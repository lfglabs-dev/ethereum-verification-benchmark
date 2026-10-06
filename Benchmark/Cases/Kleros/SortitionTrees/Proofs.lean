import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

@[simp] private theorem readSlot_eq_storage (s : ContractState) (slotIdx : Nat) :
    s.readSlot slotIdx = s.storage slotIdx := rfl
@[simp] private theorem readAddrSlot_eq_storageAddr (s : ContractState) (slotIdx : Nat) :
    s.readAddrSlot slotIdx = s.storageAddr slotIdx := rfl
@[simp] private theorem readMap_eq_storageMap (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.readMap slotIdx k = s.storageMap slotIdx k := rfl
@[simp] private theorem readMapUint_eq_storageMapUint (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.readMapUint slotIdx k = s.storageMapUint slotIdx k := rfl
@[simp] private theorem readMap2_eq_storageMap2 (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.readMap2 slotIdx k1 k2 = s.storageMap2 slotIdx k1 k2 := rfl
@[simp] private theorem readTransient_eq_transientStorage (s : ContractState) (slotIdx : Nat) :
    s.readTransient slotIdx = s.transientStorage slotIdx := rfl
@[simp] private theorem storage_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storage =
      s.storage := rfl
@[simp] private theorem storageAddr_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageAddr =
      s.storageAddr := rfl
@[simp] private theorem storageMap_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap =
      s.storageMap := rfl
@[simp] private theorem storageMapUint_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMapUint =
      s.storageMapUint := rfl
@[simp] private theorem storageMap2_mk_storageWords
    (s : ContractState) (sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd) :
    (ContractState.mk s.storageWords sa snd this txo mv sb bt bn cid bbf cds cd sel mem ka ev calls cs rd).storageMap2 =
      s.storageMap2 := rfl
@[simp] private theorem storage_writeSlot (s : ContractState) (slotIdx : Nat) (value : Uint256) (slotIdx' : Nat) :
    (s.writeSlot slotIdx value).storage slotIdx' = if slotIdx' == slotIdx then value else s.storage slotIdx' := by
  simp [ContractState.storage, ContractState.writeSlot]
@[simp] private theorem storageAddr_writeAddrSlot (s : ContractState) (slotIdx : Nat) (value : Address) (slotIdx' : Nat) :
    (s.writeAddrSlot slotIdx value).storageAddr slotIdx' =
      if slotIdx' == slotIdx then value else s.storageAddr slotIdx' := by
  by_cases h : slotIdx' = slotIdx
  · subst h; simp
  · simp [ContractState.storageAddr_writeAddrSlot_other s h value, h]
@[simp] private theorem storageMap_writeMap (s : ContractState) (slotIdx : Nat) (key : Address) (value : Uint256)
    (slotIdx' : Nat) (key' : Address) :
    (s.writeMap slotIdx key value).storageMap slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMap slotIdx' key' := by
  simp [ContractState.storageMap, ContractState.writeMap]
@[simp] private theorem storageMapUint_writeMapUint (s : ContractState) (slotIdx : Nat) (key value : Uint256)
    (slotIdx' : Nat) (key' : Uint256) :
    (s.writeMapUint slotIdx key value).storageMapUint slotIdx' key' =
      if slotIdx' == slotIdx && key' == key then value else s.storageMapUint slotIdx' key' := by
  simp [ContractState.storageMapUint, ContractState.writeMapUint]
@[simp] private theorem storage_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storage = s.storage := by
  funext wordSlot; simp [ContractState.storage, ContractState.writeMap2]
@[simp] private theorem storageAddr_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageAddr = s.storageAddr := by
  funext addrSlot; simp [ContractState.storageAddr, ContractState.writeMap2]
@[simp] private theorem storageMap_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap = s.storageMap := by
  funext mapSlot mapKey; simp [ContractState.storageMap, ContractState.writeMap2]
@[simp] private theorem storageMapUint_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256) :
    (s.writeMap2 slotIdx key1 key2 value).storageMapUint = s.storageMapUint := by
  funext mapSlot mapKey; simp [ContractState.storageMapUint, ContractState.writeMap2]
@[simp] private theorem storageMap2_writeMap2 (s : ContractState) (slotIdx : Nat) (key1 key2 : Address) (value : Uint256)
    (slotIdx' : Nat) (key1' key2' : Address) :
    (s.writeMap2 slotIdx key1 key2 value).storageMap2 slotIdx' key1' key2' =
      if slotIdx' == slotIdx && key1' == key1 && key2' == key2 then value else s.storageMap2 slotIdx' key1' key2' := by
  simp [ContractState.storageMap2, ContractState.writeMap2, and_assoc]
@[simp] private theorem storageWords_slot_eq (s : ContractState) (slotIdx : Nat) :
    s.storageWords (.slot slotIdx) = s.storage slotIdx := rfl
@[simp] private theorem storageWords_map_eq (s : ContractState) (slotIdx : Nat) (k : Address) :
    s.storageWords (.map slotIdx k) = s.storageMap slotIdx k := rfl
@[simp] private theorem storageWords_mapUint_eq (s : ContractState) (slotIdx : Nat) (k : Uint256) :
    s.storageWords (.mapUint slotIdx k) = s.storageMapUint slotIdx k := rfl
@[simp] private theorem storageWords_map2_eq (s : ContractState) (slotIdx : Nat) (k1 k2 : Address) :
    s.storageWords (.map2 slotIdx k1 k2) = s.storageMap2 slotIdx k1 k2 := rfl


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
Executing `setLeaf` recomputes each parent node from its direct children.
-/
theorem parent_equals_sum_of_children
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
          have hLow' : (3 : Nat) ≤ nodeIndex.val := by
            change (3 : Nat) ≤ nodeIndex.val at hLow
            exact hLow
          have hHigh' : nodeIndex.val ≤ 6 := by
            change nodeIndex.val ≤ 6 at hHigh
            exact hHigh
          have h3ne : nodeIndex ≠ 3 := by simpa using h3
          have h4ne : nodeIndex ≠ 4 := by simpa using h4
          have h5ne : nodeIndex ≠ 5 := by simpa using h5
          have h6ne : nodeIndex ≠ 6 := by simpa using h6
          have h3' : nodeIndex.val ≠ 3 := by intro hv; apply h3ne; exact Verity.Core.Uint256.ext hv
          have h4' : nodeIndex.val ≠ 4 := by intro hv; apply h4ne; exact Verity.Core.Uint256.ext hv
          have h5' : nodeIndex.val ≠ 5 := by intro hv; apply h5ne; exact Verity.Core.Uint256.ext hv
          have h6' : nodeIndex.val ≠ 6 := by intro hv; apply h6ne; exact Verity.Core.Uint256.ext hv
          omega

/--
Executing `setLeaf` recomputes the root as the sum of the four leaf weights.
-/
theorem root_equals_sum_of_leaves
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
            have hLow' : (3 : Nat) ≤ nodeIndex.val := by
              change (3 : Nat) ≤ nodeIndex.val at hLow
              exact hLow
            have hHigh' : nodeIndex.val ≤ 6 := by
              change nodeIndex.val ≤ 6 at hHigh
              exact hHigh
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
Executing `draw` follows the encoded ticket intervals used by the
implementation.
-/
theorem draw_interval_matches_weights
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_interval_matches_weights_spec ticket s s' := by
  unfold draw_interval_matches_weights_spec
  dsimp
  intro _
  refine ⟨?_, ?_⟩
  · intro hLeaf0
    rw [draw_selected_node ticket s hRoot hInRange]
    simp [hLeaf0]
  refine ⟨?_, ?_⟩
  · intro hLeft
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotLeaf0 : ¬ ticket < s.storage 3 := Nat.not_lt_of_ge hLeft.2
    simp [hLeft.1, hNotLeaf0]
  refine ⟨?_, ?_⟩
  · intro hRight
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotLeft : ¬ ticket < s.storage 1 := Nat.not_lt_of_ge hRight.1
    simp [hNotLeft, hRight.2]
  · intro hLast
    rw [draw_selected_node ticket s hRoot hInRange]
    have hRight : s.storage 1 ≤ ticket := hLast.1
    have hNotLeft : ¬ ticket < s.storage 1 := Nat.not_lt_of_ge hRight
    have hNotLeaf2 : ¬ sub ticket (s.storage 1) < s.storage 5 := Nat.not_lt_of_ge hLast.2
    simp [hNotLeft, hNotLeaf2]

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

/--
Executing `setLeaf` writes matching forward and reverse mapping entries for the
updated node and stake-path id.
-/
theorem node_id_bijection
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 3)
    (hHigh : nodeIndex <= 6) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    node_id_bijection_spec nodeIndex stakePathID s' := by
  have h7eq : 7 = SortitionTrees.nodeIndexesToIDs.slot := by decide
  have h8eq : 8 = SortitionTrees.IDsToNodeIndexes.slot := by decide
  by_cases h3 : nodeIndex == 3
  · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h7eq, h8eq, node_id_bijection_spec, getStorage,
      setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
  · by_cases h4 : nodeIndex == 4
    · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h4, h7eq, h8eq, node_id_bijection_spec,
        getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
        ContractResult.snd]
    · by_cases h5 : nodeIndex == 5
      · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h4, h5, h7eq, h8eq, node_id_bijection_spec,
          getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
          ContractResult.snd]
      · by_cases h6 : nodeIndex == 6
        · simp [SortitionTrees.setLeaf, hLow, hHigh, h3, h4, h5, h6, h7eq, h8eq, node_id_bijection_spec,
            getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
            ContractResult.snd]
        · exfalso
          have hLow' : (3 : Nat) ≤ nodeIndex.val := by
            change (3 : Nat) ≤ nodeIndex.val at hLow
            exact hLow
          have hHigh' : nodeIndex.val ≤ 6 := by
            change nodeIndex.val ≤ 6 at hHigh
            exact hHigh
          have h3ne : nodeIndex ≠ 3 := by simpa using h3
          have h4ne : nodeIndex ≠ 4 := by simpa using h4
          have h5ne : nodeIndex ≠ 5 := by simpa using h5
          have h6ne : nodeIndex ≠ 6 := by simpa using h6
          have h3' : nodeIndex.val ≠ 3 := by intro hv; apply h3ne; exact Verity.Core.Uint256.ext hv
          have h4' : nodeIndex.val ≠ 4 := by intro hv; apply h4ne; exact Verity.Core.Uint256.ext hv
          have h5' : nodeIndex.val ≠ 5 := by intro hv; apply h5ne; exact Verity.Core.Uint256.ext hv
          have h6' : nodeIndex.val ≠ 6 := by intro hv; apply h6ne; exact Verity.Core.Uint256.ext hv
          omega

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
