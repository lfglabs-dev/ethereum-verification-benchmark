import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.MappingAutomation
import Verity.Proofs.Stdlib.Math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Core.Uint256

/-
  Reference proofs for IMT linked-list order.

  Theorems:
  - `setup_establishes_order` (proved)
  - `insert_leaf_frame` (unfolding of `insertPost` from `insert_run_of_success`)
  - `insert_preserves_order` (covering-chain splice; no custom axioms)
-/

private theorem one_ne_zero_uint : (1 : Uint256) ≠ 0 := by
  intro h
  have : (1 : Nat) = 0 := by
    have := congrArg Verity.Core.Uint256.val h
    simpa [val_one, val_zero] using this
  cases this

/-- Post-state of `setup`: sentinel leaf at index 0 and `leafNumber = 1`. -/
private def setupPost (s : ContractState) : ContractState :=
  { s with
    storageMapUint := fun sl k =>
      if sl == 3 && k == 0 then 0
      else if sl == 2 && k == 0 then 0
      else if sl == 1 && k == 0 then 0
      else s.storageMapUint sl k
    «storage» := fun sl => if sl == 0 then 1 else s.storage sl }

private theorem leafNumber_setupPost (s : ContractState) :
    leafNumber (setupPost s) = 1 := by
  simp [leafNumber, setupPost]

private theorem occupied_setupPost (s : ContractState) (i : Uint256) :
    occupied (setupPost s) i ↔ i = 0 := by
  constructor
  · intro hi
    have hlt : i.val < 1 := by
      simpa [occupied, leafNumber_setupPost, lt_def] using hi
    exact ext (Nat.lt_one_iff.mp hlt)
  · intro hi
    subst hi
    change (0 : Uint256) < leafNumber (setupPost s)
    simpa [leafNumber_setupPost, lt_def, val_zero, val_one]

private theorem leafValue_setupPost_zero (s : ContractState) :
    leafValue (setupPost s) 0 = 0 := by
  simp [leafValue, setupPost]

private theorem nextIndex_setupPost_zero (s : ContractState) :
    nextIndex (setupPost s) 0 = 0 := by
  simp [nextIndex, setupPost]

private theorem nextValue_setupPost_zero (s : ContractState) :
    nextValue (setupPost s) 0 = 0 := by
  simp [nextValue, setupPost]

private theorem valueToIndex_setupPost (s : ContractState)
    (hFresh : freshZeroStorage s) (v : Uint256) :
    valueToIndexOf (setupPost s) v = 0 := by
  have hz : s.storageMapUint 4 v = 0 := by
    simpa [valueToIndexOf] using hFresh.2.2 v
  simp [valueToIndexOf, setupPost, hz]

private theorem setup_run_of_fresh (s : ContractState)
    (hFresh : freshZeroStorage s) :
    IndexedMerkleTree.setup.run s = ContractResult.success () (setupPost s) := by
  have hln : s.storage 0 = 0 := by
    simpa [leafNumber] using hFresh.1
  unfold IndexedMerkleTree.setup
  simp [setupPost, Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, getStorage, setStorage, setMappingUint,
        IndexedMerkleTree.leafNumber, IndexedMerkleTree.leaves_value,
        IndexedMerkleTree.leaves_nextIndex, IndexedMerkleTree.leaves_nextValue,
        hln]

/-- `setup` on fresh-zero storage establishes `IMTOrder`. -/
theorem setup_establishes_order (s : ContractState)
    (hFresh : freshZeroStorage s) :
    IMTOrder (IndexedMerkleTree.setup.run s).snd := by
  have hrun := setup_run_of_fresh s hFresh
  rw [hrun]
  change IMTOrder (setupPost s)
  refine {
    sentinelValue := leafValue_setupPost_zero s
    covering := ?cov
  }
  refine ⟨[0], ?head, ?len, ?nodup, ?chain, ?mem, ?inc, ?tail⟩
  · rfl
  · simp [leafNumber_setupPost, val_one]
  · simp [noDuplicateIndices]
  · simp [isIndexChain]
  · intro i
    constructor
    · intro hi
      have : i = 0 := (occupied_setupPost s i).1 hi
      simp [this]
    · intro hi
      have : i = 0 := List.mem_singleton.mp hi
      exact (occupied_setupPost s i).2 this
  · simp [chainValuesIncrease]
  · intro t ht
    have hlast : some t = some (0 : Uint256) := by
      simpa using ht.symm
    injection hlast with ht0
    subst ht0
    exact ⟨nextIndex_setupPost_zero s, nextValue_setupPost_zero s⟩

theorem setup_establishes_IMTOrder (s s' : ContractState) :
    setup_establishes_spec s s' := by
  intro hFresh hEq
  simpa [hEq] using setup_establishes_order s hFresh


def insertLow (s : ContractState) (value lowHint : Uint256) : Uint256 :=
  walkLowLeafFuel (leafNumber s).val s lowHint value

def insertPost (s : ContractState) (value lowHint : Uint256) : ContractState :=
  { s with
    storageMapUint := fun sl k =>
      if sl == 4 && k == value then leafNumber s
      else if sl == 3 && k == leafNumber s then
        nextValue s (insertLow s value lowHint)
      else if sl == 2 && k == leafNumber s then
        nextIndex s (insertLow s value lowHint)
      else if sl == 1 && k == leafNumber s then value
      else if sl == 3 && k == insertLow s value lowHint then value
      else if sl == 2 && k == insertLow s value lowHint then leafNumber s
      else s.storageMapUint sl k
    «storage» := fun sl =>
      if sl == 0 then EVM.Uint256.add (leafNumber s) 1 else s.storage sl }

def walkResult (fuel : Nat) (s : ContractState) (idx value : Uint256) : Uint256 :=
  match fuel with
  | 0 => idx
  | fuel' + 1 =>
    if nextValue s idx ≠ 0 ∧ nextValue s idx < value then
      walkResult fuel' s (nextIndex s idx) value
    else
      idx

theorem walkLowLeaf_apply
    (fuel : Nat) (idx value : Uint256) (s : ContractState) :
    walkLowLeaf fuel idx value s =
      ContractResult.success (walkResult fuel s idx value) s := by
  induction fuel generalizing idx with
  | zero =>
      rw [walkLowLeaf.eq_def]
      rfl
  | succ fuel ih =>
      rw [walkLowLeaf.eq_def]
      have h3 :
          getMappingUint (⟨3⟩ : StorageSlot (Uint256 → Uint256)) idx s =
            ContractResult.success (s.storageMapUint 3 idx) s := rfl
      have h2 :
          getMappingUint (⟨2⟩ : StorageSlot (Uint256 → Uint256)) idx s =
            ContractResult.success (s.storageMapUint 2 idx) s := rfl
      simp [Verity.bind, h3, h2, walkResult, nextValue, nextIndex]
      split
      · exact ih (s.storageMapUint 2 idx)
      · rfl

private theorem walkLowLeafFuel_eq_walkResult
    (fuel : Nat) (s : ContractState) (idx value : Uint256) :
    walkLowLeafFuel fuel s idx value = walkResult fuel s idx value := by
  simp [walkLowLeafFuel, Contract.run, walkLowLeaf_apply]

private theorem require_apply (cond : Bool) (msg : String) (s : ContractState) :
    Verity.require cond msg s =
      if cond then ContractResult.success () s else ContractResult.revert msg s := rfl

private theorem get_leafNumber (s : ContractState) :
    getStorage IndexedMerkleTree.leafNumber s =
      ContractResult.success (s.storage 0) s := rfl

private theorem get_v2i (k : Uint256) (s : ContractState) :
    getMappingUint IndexedMerkleTree.valueToIndex k s =
      ContractResult.success (s.storageMapUint 4 k) s := rfl

private theorem get_val (k : Uint256) (s : ContractState) :
    getMappingUint IndexedMerkleTree.leaves_value k s =
      ContractResult.success (s.storageMapUint 1 k) s := rfl

private theorem get_ni (k : Uint256) (s : ContractState) :
    getMappingUint IndexedMerkleTree.leaves_nextIndex k s =
      ContractResult.success (s.storageMapUint 2 k) s := rfl

private theorem get_nv (k : Uint256) (s : ContractState) :
    getMappingUint IndexedMerkleTree.leaves_nextValue k s =
      ContractResult.success (s.storageMapUint 3 k) s := rfl

private theorem set_ni (k v : Uint256) (s : ContractState) :
    setMappingUint IndexedMerkleTree.leaves_nextIndex k v s =
      ContractResult.success () (s.writeMapUint 2 k v) := rfl

private theorem set_nv (k v : Uint256) (s : ContractState) :
    setMappingUint IndexedMerkleTree.leaves_nextValue k v s =
      ContractResult.success () (s.writeMapUint 3 k v) := rfl

private theorem set_val (k v : Uint256) (s : ContractState) :
    setMappingUint IndexedMerkleTree.leaves_value k v s =
      ContractResult.success () (s.writeMapUint 1 k v) := rfl

private theorem set_v2i (k v : Uint256) (s : ContractState) :
    setMappingUint IndexedMerkleTree.valueToIndex k v s =
      ContractResult.success () (s.writeMapUint 4 k v) := rfl

private theorem set_ln (v : Uint256) (s : ContractState) :
    setStorage IndexedMerkleTree.leafNumber v s =
      ContractResult.success () (s.writeSlot 0 v) := rfl

private theorem addPanic_apply (a b : Uint256) (s : ContractState) :
    addPanic a b s =
      match safeAdd a b with
      | some n => ContractResult.success n s
      | none => ContractResult.revert "Panic(0x11): arithmetic overflow" s := by
  unfold addPanic requireSomeUint
  cases h : safeAdd a b with
  | none =>
      simp [h, Bind.bind, Verity.bind, Verity.require, Verity.pure, Pure.pure]
  | some n =>
      simp [h, Bind.bind, Verity.bind, Verity.require, Verity.pure, Pure.pure]

private theorem insert_apply_revert_not_init
    (value lowHint : Uint256) (s : ContractState)
    (hln : (s.storage 0 != 0) = false) :
    IndexedMerkleTree.insert value lowHint s =
      ContractResult.revert "IMTNotInitialized" s := by
  unfold IndexedMerkleTree.insert
  simp [Bind.bind, Verity.bind, get_leafNumber, require_apply, hln]

private theorem insert_apply_revert_zero_value
    (value lowHint : Uint256) (s : ContractState)
    (hln : (s.storage 0 != 0) = true)
    (hv : (value != 0) = false) :
    IndexedMerkleTree.insert value lowHint s =
      ContractResult.revert "IMTValueZero" s := by
  unfold IndexedMerkleTree.insert
  simp [Bind.bind, Verity.bind, get_leafNumber, require_apply, hln, hv]

private theorem insert_apply_revert_exists
    (value lowHint : Uint256) (s : ContractState)
    (hln : (s.storage 0 != 0) = true)
    (hv : (value != 0) = true)
    (hex : (s.storageMapUint 4 value == 0) = false) :
    IndexedMerkleTree.insert value lowHint s =
      ContractResult.revert "IMTValueAlreadyExists" s := by
  unfold IndexedMerkleTree.insert
  simp [Bind.bind, Verity.bind, get_leafNumber, require_apply, get_v2i, hln, hv, hex]

private theorem insert_apply_revert_hint_oob
    (value lowHint : Uint256) (s : ContractState)
    (hln : (s.storage 0 != 0) = true)
    (hv : (value != 0) = true)
    (hex : (s.storageMapUint 4 value == 0) = true)
    (hhint : decide (lowHint.val < (s.storage 0).val) = false) :
    IndexedMerkleTree.insert value lowHint s =
      ContractResult.revert "IMTLowLeafIndexOutOfBounds" s := by
  have hhintN : ¬ (lowHint.val < (s.storage 0).val) := of_decide_eq_false hhint
  unfold IndexedMerkleTree.insert
  simp [Bind.bind, Verity.bind, get_leafNumber, require_apply, get_v2i,
    hln, hv, hex, hhintN]

private theorem insert_apply_revert_hint_too_large
    (value lowHint : Uint256) (s : ContractState)
    (hln : (s.storage 0 != 0) = true)
    (hv : (value != 0) = true)
    (hex : (s.storageMapUint 4 value == 0) = true)
    (hhint : decide (lowHint.val < (s.storage 0).val) = true)
    (hval : decide ((s.storageMapUint 1 lowHint).val < value.val) = false) :
    IndexedMerkleTree.insert value lowHint s =
      ContractResult.revert "IMTLowLeafValueTooLarge" s := by
  have hhintP : lowHint.val < (s.storage 0).val := of_decide_eq_true hhint
  have hvalN : ¬ ((s.storageMapUint 1 lowHint).val < value.val) :=
    of_decide_eq_false hval
  unfold IndexedMerkleTree.insert
  simp [Bind.bind, Verity.bind, get_leafNumber, require_apply, get_v2i, get_val,
    hln, hv, hex, hhintP, hvalN]

private theorem insert_apply_after_guards
    (value lowHint : Uint256) (s : ContractState)
    (hln : (s.storage 0 != 0) = true)
    (hv : (value != 0) = true)
    (hex : (s.storageMapUint 4 value == 0) = true)
    (hhint : decide (lowHint.val < (s.storage 0).val) = true)
    (hval : decide ((s.storageMapUint 1 lowHint).val < value.val) = true) :
    IndexedMerkleTree.insert value lowHint s =
      (let low := walkResult (s.storage 0).val s lowHint value
       let s1 := s.writeMapUint 2 low (s.storage 0)
       let s2 := s1.writeMapUint 3 low value
       let s3 := s2.writeMapUint 1 (s.storage 0) value
       let s4 := s3.writeMapUint 2 (s.storage 0) (s.storageMapUint 2 low)
       let s5 := s4.writeMapUint 3 (s.storage 0) (s.storageMapUint 3 low)
       let s6 := s5.writeMapUint 4 value (s.storage 0)
       match safeAdd (s.storage 0) 1 with
       | none => ContractResult.revert "Panic(0x11): arithmetic overflow" s6
       | some n => ContractResult.success (s.storage 0) (s6.writeSlot 0 n)) := by
  have hhintP : lowHint.val < (s.storage 0).val := of_decide_eq_true hhint
  have hvalP : (s.storageMapUint 1 lowHint).val < value.val :=
    of_decide_eq_true hval
  unfold IndexedMerkleTree.insert
  simp [Bind.bind, Verity.bind, get_leafNumber, require_apply, get_v2i, get_val,
    get_ni, get_nv, set_ni, set_nv, set_val, set_v2i, set_ln,
    walkLowLeaf_apply, addPanic_apply, Verity.pure, Pure.pure,
    hln, hv, hex, hhintP, hvalP]
  cases safeAdd (s.storage 0) 1 <;> simp

private theorem eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

/-- Characterization of a successful `insert` by unfolding the modeled
    require / walk / write / addPanic bind chain. Conclusion is the
    concrete `insertPost` record, not `IMTOrder`. -/
theorem insert_run_of_success
    (value lowHint : Uint256) (s : ContractState)
    (hOk : insert_succeeds value lowHint s) :
    (IndexedMerkleTree.insert value lowHint).run s =
      ContractResult.success (leafNumber s) (insertPost s value lowHint) := by
  unfold insert_succeeds at hOk
  by_cases hln : (s.storage 0 != 0) = true
  · by_cases hv : (value != 0) = true
    · by_cases hex : (s.storageMapUint 4 value == 0) = true
      · by_cases hhint : decide (lowHint.val < (s.storage 0).val) = true
        · by_cases hval : decide ((s.storageMapUint 1 lowHint).val < value.val) = true
          · have happly :=
              insert_apply_after_guards value lowHint s hln hv hex hhint hval
            cases hsa : safeAdd (s.storage 0) 1 with
            | none =>
                have hrev :
                    IndexedMerkleTree.insert value lowHint s =
                      ContractResult.revert
                        "Panic(0x11): arithmetic overflow"
                        (let low := walkResult (s.storage 0).val s lowHint value
                         let s1 := s.writeMapUint 2 low (s.storage 0)
                         let s2 := s1.writeMapUint 3 low value
                         let s3 := s2.writeMapUint 1 (s.storage 0) value
                         let s4 := s3.writeMapUint 2 (s.storage 0) (s.storageMapUint 2 low)
                         let s5 := s4.writeMapUint 3 (s.storage 0) (s.storageMapUint 3 low)
                         s5.writeMapUint 4 value (s.storage 0)) := by
                  simpa [hsa] using happly
                simp [Contract.run, hrev] at hOk
            | some n =>
                have hsucc :
                    IndexedMerkleTree.insert value lowHint s =
                      ContractResult.success (s.storage 0)
                        ((let low := walkResult (s.storage 0).val s lowHint value
                          let s1 := s.writeMapUint 2 low (s.storage 0)
                          let s2 := s1.writeMapUint 3 low value
                          let s3 := s2.writeMapUint 1 (s.storage 0) value
                          let s4 := s3.writeMapUint 2 (s.storage 0) (s.storageMapUint 2 low)
                          let s5 := s4.writeMapUint 3 (s.storage 0) (s.storageMapUint 3 low)
                          let s6 := s5.writeMapUint 4 value (s.storage 0)
                          s6.writeSlot 0 n)) := by
                  simpa [hsa] using happly
                have hle : (s.storage 0 : Nat) + (1 : Nat) ≤ MAX_UINT256 := by
                  have his : (safeAdd (s.storage 0) 1).isSome = true := by
                    simp [hsa]
                  exact
                    (Verity.Proofs.Stdlib.Math.CheckedArithmetic.safeAdd_isSome_iff_addNoOverflow
                      (s.storage 0) 1).mp (by simpa using his)
                have hnAdd : n = EVM.Uint256.add (s.storage 0) 1 := by
                  have : safeAdd (s.storage 0) 1 =
                      some (EVM.Uint256.add (s.storage 0) 1) := by
                    have h :=
                      Verity.Proofs.Stdlib.Math.safeAdd_some (s.storage 0) 1 hle
                    simpa [HAdd.hAdd, Add.add, EVM.Uint256.add] using h
                  rw [this] at hsa
                  injection hsa with hn'
                  exact hn'.symm
                simp [Contract.run, hsucc, insertPost, insertLow,
                  walkLowLeafFuel_eq_walkResult, leafNumber, nextValue, nextIndex,
                  hnAdd, ContractState.writeMapUint, ContractState.writeSlot]
          · have hrev :=
              insert_apply_revert_hint_too_large value lowHint s hln hv hex hhint
                (eq_false_of_ne_true hval)
            simp [Contract.run, hrev] at hOk
        · have hrev :=
            insert_apply_revert_hint_oob value lowHint s hln hv hex
              (eq_false_of_ne_true hhint)
          simp [Contract.run, hrev] at hOk
      · have hrev := insert_apply_revert_exists value lowHint s hln hv
          (eq_false_of_ne_true hex)
        simp [Contract.run, hrev] at hOk
    · have hrev := insert_apply_revert_zero_value value lowHint s hln
        (eq_false_of_ne_true hv)
      simp [Contract.run, hrev] at hOk
  · have hrev := insert_apply_revert_not_init value lowHint s
      (eq_false_of_ne_true hln)
    simp [Contract.run, hrev] at hOk

private theorem insert_success_guards
    (value lowHint : Uint256) (s : ContractState)
    (hOk : insert_succeeds value lowHint s) :
    (s.storage 0 != 0) = true ∧
    (value != 0) = true ∧
    (s.storageMapUint 4 value == 0) = true ∧
    decide (lowHint.val < (s.storage 0).val) = true ∧
    decide ((s.storageMapUint 1 lowHint).val < value.val) = true ∧
    (safeAdd (s.storage 0) 1).isSome = true := by
  unfold insert_succeeds at hOk
  by_cases hln : (s.storage 0 != 0) = true
  · by_cases hv : (value != 0) = true
    · by_cases hex : (s.storageMapUint 4 value == 0) = true
      · by_cases hhint : decide (lowHint.val < (s.storage 0).val) = true
        · by_cases hval : decide ((s.storageMapUint 1 lowHint).val < value.val) = true
          · have happly :=
              insert_apply_after_guards value lowHint s hln hv hex hhint hval
            cases hsa : safeAdd (s.storage 0) 1 with
            | none =>
                have hrev :
                    IndexedMerkleTree.insert value lowHint s =
                      ContractResult.revert
                        "Panic(0x11): arithmetic overflow"
                        (let low := walkResult (s.storage 0).val s lowHint value
                         let s1 := s.writeMapUint 2 low (s.storage 0)
                         let s2 := s1.writeMapUint 3 low value
                         let s3 := s2.writeMapUint 1 (s.storage 0) value
                         let s4 := s3.writeMapUint 2 (s.storage 0) (s.storageMapUint 2 low)
                         let s5 := s4.writeMapUint 3 (s.storage 0) (s.storageMapUint 3 low)
                         s5.writeMapUint 4 value (s.storage 0)) := by
                  simpa [hsa] using happly
                simp [Contract.run, hrev] at hOk
            | some _ =>
                exact ⟨hln, hv, hex, hhint, hval, by simp [hsa]⟩
          · have hrev :=
              insert_apply_revert_hint_too_large value lowHint s hln hv hex hhint
                (eq_false_of_ne_true hval)
            simp [Contract.run, hrev] at hOk
        · have hrev :=
            insert_apply_revert_hint_oob value lowHint s hln hv hex
              (eq_false_of_ne_true hhint)
          simp [Contract.run, hrev] at hOk
      · have hrev := insert_apply_revert_exists value lowHint s hln hv
          (eq_false_of_ne_true hex)
        simp [Contract.run, hrev] at hOk
    · have hrev := insert_apply_revert_zero_value value lowHint s hln
        (eq_false_of_ne_true hv)
      simp [Contract.run, hrev] at hOk
  · have hrev := insert_apply_revert_not_init value lowHint s
      (eq_false_of_ne_true hln)
    simp [Contract.run, hrev] at hOk

private theorem chain_index_cons
    (s : ContractState) (a b : Uint256) (rest : List Uint256)
    (h : isIndexChain s (a :: b :: rest)) :
    nextIndex s a = b ∧
    nextValue s a = leafValue s b ∧
    isIndexChain s (b :: rest) := h

private theorem eq_cons_of_head?
    {α : Type} {x : α} {l : List α} (h : l.head? = some x) :
    ∃ rest, l = x :: rest := by
  cases l with
  | nil => cases h
  | cons a rest =>
      have : a = x := by simpa using h
      subst this
      exact ⟨rest, rfl⟩

private theorem walkResult_zero (s : ContractState) (idx value : Uint256) :
    walkResult 0 s idx value = idx := rfl

private theorem walkResult_succ_go
    (fuel : Nat) (s : ContractState) (idx value : Uint256)
    (h : nextValue s idx ≠ 0 ∧ nextValue s idx < value) :
    walkResult (fuel + 1) s idx value =
      walkResult fuel s (nextIndex s idx) value := by
  simp [walkResult, h]

private theorem walkResult_succ_stop
    (fuel : Nat) (s : ContractState) (idx value : Uint256)
    (h : ¬ (nextValue s idx ≠ 0 ∧ nextValue s idx < value)) :
    walkResult (fuel + 1) s idx value = idx := by
  unfold walkResult
  split
  · next hgo => exact False.elim (h hgo)
  · rfl

private theorem walk_on_suffix
    (s : ContractState) (value : Uint256) :
    ∀ fuel idx rest,
      isIndexChain s rest →
      (∀ t : Uint256, rest.getLast? = some t → nextValue s t = 0) →
      rest.head? = some idx →
      rest.length ≤ fuel + 1 →
      leafValue s idx < value →
      walkResult fuel s idx value ∈ rest ∧
      leafValue s (walkResult fuel s idx value) < value ∧
      (nextValue s (walkResult fuel s idx value) = 0 ∨
        ¬ nextValue s (walkResult fuel s idx value) < value)
  | 0, idx, rest, _hCh, hLast, hHead, hLen, hLt => by
      obtain ⟨tail, hrest⟩ := eq_cons_of_head? hHead
      subst hrest
      cases tail with
      | nil =>
          have hnv : nextValue s idx = 0 := hLast idx (by simp)
          rw [walkResult_zero]
          exact ⟨List.mem_singleton.mpr rfl, hLt, Or.inl hnv⟩
      | cons _ _ =>
          have : (idx :: _ :: _).length ≤ 1 := hLen
          simp at this
  | fuel + 1, idx, rest, hCh, hLast, hHead, hLen, hLt => by
      obtain ⟨tail, hrest⟩ := eq_cons_of_head? hHead
      subst hrest
      by_cases h : nextValue s idx ≠ 0 ∧ nextValue s idx < value
      · rw [walkResult_succ_go (h := h)]
        cases tail with
        | nil =>
            have hnv0 : nextValue s idx = 0 := hLast idx (by simp)
            exact absurd h.1 (by simp [hnv0])
        | cons z zs =>
            have ⟨hni, hnv, hCh'⟩ := chain_index_cons s idx z zs hCh
            have hLast' :
                ∀ t, (z :: zs).getLast? = some t → nextValue s t = 0 := by
              intro t ht
              exact hLast t (by simpa using ht)
            have hHead' : (z :: zs).head? = some (nextIndex s idx) := by
              simp [hni]
            have hLen' : (z :: zs).length ≤ fuel + 1 := by
              have hlen : (idx :: z :: zs).length ≤ fuel + 2 := by
                simpa using hLen
              have : zs.length + 2 ≤ fuel + 2 := by
                simpa [List.length_cons] using hlen
              have : zs.length ≤ fuel := Nat.le_of_add_le_add_right this
              simpa [List.length_cons] using Nat.succ_le_succ this
            have hLt' : leafValue s (nextIndex s idx) < value := by
              have : leafValue s (nextIndex s idx) = nextValue s idx := by
                simpa [hni] using hnv.symm
              simpa [this] using h.2
            have ih :=
              walk_on_suffix s value fuel (nextIndex s idx) (z :: zs)
                hCh' hLast' hHead' hLen' hLt'
            refine ⟨List.mem_cons.mpr (Or.inr ih.1), ih.2.1, ih.2.2⟩
      · rw [walkResult_succ_stop (h := h)]
        refine ⟨List.mem_cons_self, hLt, ?_⟩
        by_cases hz : nextValue s idx = 0
        · exact Or.inl hz
        · exact Or.inr (fun hlt => h ⟨hz, hlt⟩)

private theorem mem_tail_of_ne
    {a idx : Uint256} {rest : List Uint256}
    (hmem : idx ∈ a :: rest) (ha : a ≠ idx) : idx ∈ rest := by
  cases List.mem_cons.mp hmem with
  | inl heq => exact False.elim (ha heq.symm)
  | inr h => exact h

private theorem dropWhile_ne_head
    (chain : List Uint256) (idx : Uint256) (hmem : idx ∈ chain) :
    (chain.dropWhile (· ≠ idx)).head? = some idx := by
  induction chain with
  | nil => cases hmem
  | cons a rest ih =>
      by_cases ha : a = idx
      · subst ha
        simp [List.dropWhile]
      · have hrest : idx ∈ rest := mem_tail_of_ne hmem ha
        unfold List.dropWhile
        split
        · next hpos =>
            have hdw : rest.dropWhile (· ≠ idx) = rest.dropWhile (· ≠ idx) := rfl
            exact ih hrest
        · next hneg =>
            have : decide (a ≠ idx) = true := by simp [ha]
            simp [this] at hneg

private theorem dropWhile_subset
    (chain : List Uint256) (idx : Uint256) :
    ∀ x, x ∈ chain.dropWhile (· ≠ idx) → x ∈ chain := by
  induction chain with
  | nil => intro x hx; cases hx
  | cons a rest ih =>
      intro x hx
      unfold List.dropWhile at hx
      split at hx
      · next hpos =>
          exact List.mem_cons.mpr (Or.inr (ih x hx))
      · next hneg =>
          exact hx

private theorem dropWhile_ne_last
    (chain : List Uint256) (idx : Uint256) (hmem : idx ∈ chain) :
    (chain.dropWhile (· ≠ idx)).getLast? = chain.getLast? := by
  induction chain with
  | nil => cases hmem
  | cons a rest ih =>
      by_cases ha : a = idx
      · subst ha
        simp [List.dropWhile]
      · have hrest : idx ∈ rest := mem_tail_of_ne hmem ha
        unfold List.dropWhile
        split
        · next hpos =>
            have hne : rest ≠ [] := List.ne_nil_of_mem hrest
            have hlast : (a :: rest).getLast? = rest.getLast? :=
              List.getLast?_cons_of_ne_nil hne
            rw [hlast]
            exact ih hrest
        · next hneg =>
            have : decide (a ≠ idx) = true := by simp [ha]
            simp [this] at hneg

private theorem dropWhile_length_le
    (chain : List Uint256) (idx : Uint256) :
    (chain.dropWhile (· ≠ idx)).length ≤ chain.length := by
  induction chain with
  | nil => simp
  | cons a rest ih =>
      by_cases ha : a = idx
      · subst ha
        simp [List.dropWhile]
      · unfold List.dropWhile
        split
        · next hpos =>
            exact Nat.le_trans ih (Nat.le_succ _)
        · next hneg =>
            simp

private theorem index_of_dropWhile
    (s : ContractState) (chain : List Uint256) (idx : Uint256)
    (hCh : isIndexChain s chain) (hmem : idx ∈ chain) :
    isIndexChain s (chain.dropWhile (· ≠ idx)) := by
  induction chain with
  | nil => cases hmem
  | cons a rest ih =>
      by_cases ha : a = idx
      · subst ha
        simp [List.dropWhile]
        exact hCh
      · have hrest : idx ∈ rest := mem_tail_of_ne hmem ha
        unfold List.dropWhile
        split
        · next hpos =>
            cases rest with
            | nil => cases hrest
            | cons b bs =>
                have ⟨_, _, hCh'⟩ := chain_index_cons s a b bs hCh
                exact ih hCh' hrest
        · next hneg =>
            have : decide (a ≠ idx) = true := by simp [ha]
            simp [this] at hneg

private theorem covering_walk
    (s : ContractState) (value lowHint : Uint256) (old : List Uint256)
    (hCov : isCoveringOrderedChain s old)
    (hHint : occupied s lowHint)
    (hLt : leafValue s lowHint < value) :
    occupied s (walkResult (leafNumber s).val s lowHint value) ∧
    leafValue s (walkResult (leafNumber s).val s lowHint value) < value ∧
    (nextValue s (walkResult (leafNumber s).val s lowHint value) = 0 ∨
      ¬ nextValue s (walkResult (leafNumber s).val s lowHint value) < value) := by
  rcases hCov with ⟨hHead, hLen, _hNodup, hCh, hMem, _hInc, hTail⟩
  have hmem : lowHint ∈ old := (hMem lowHint).mp hHint
  let rest := old.dropWhile (· ≠ lowHint)
  have hHeadR : rest.head? = some lowHint := dropWhile_ne_head old lowHint hmem
  have hChR : isIndexChain s rest := index_of_dropWhile s old lowHint hCh hmem
  have hLastR : ∀ t, rest.getLast? = some t → nextValue s t = 0 := by
    intro t ht
    have hlast : rest.getLast? = old.getLast? :=
      dropWhile_ne_last old lowHint hmem
    have : old.getLast? = some t := by
      simpa [hlast] using ht
    exact (hTail t this).2
  have hLenR : rest.length ≤ (leafNumber s).val + 1 := by
    have : rest.length ≤ old.length := dropWhile_length_le old lowHint
    have : rest.length ≤ (leafNumber s).val := by simpa [hLen] using this
    exact Nat.le_succ_of_le this
  have hWalk :=
    walk_on_suffix s value (leafNumber s).val lowHint rest
      hChR hLastR hHeadR hLenR hLt
  have hOcc : occupied s (walkResult (leafNumber s).val s lowHint value) :=
    (hMem _).mpr (dropWhile_subset old lowHint _ hWalk.1)
  exact ⟨hOcc, hWalk.2.1, hWalk.2.2⟩


/-- Localized pre-state walk-stop fact.

    Premise: modeled success and `IMTOrder`.
    Conclusion: `insertLow` is occupied, its stored value is `< value`,
    and the walk has stopped (`nextValue = 0` or `¬ nextValue < value`).
    Combined with `valueNotStored`, that predecessor is the splice point. -/
theorem insert_walk_brackets
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    occupied s (insertLow s value lowHint) ∧
    leafValue s (insertLow s value lowHint) < value ∧
    (nextValue s (insertLow s value lowHint) = 0 ∨
      ¬ nextValue s (insertLow s value lowHint) < value) ∧
    value ≠ 0 ∧
    (leafNumber s).val + 1 ≤ MAX_UINT256 := by
  have hG := insert_success_guards value lowHint s hOk
  rcases hG with ⟨hln, hv, _hex, hhint, hval, hAdd⟩
  have hvNe : value ≠ 0 := by
    intro h
    have : (value != 0) = false := by simp [h]
    simp [this] at hv
  have hhintLt : lowHint < leafNumber s := by
    have : lowHint.val < (s.storage 0).val := of_decide_eq_true hhint
    simpa [lt_def, leafNumber] using this
  have hvalLt : leafValue s lowHint < value := by
    have : (s.storageMapUint 1 lowHint).val < value.val := of_decide_eq_true hval
    simpa [lt_def, leafValue] using this
  have hAddLe : (leafNumber s).val + 1 ≤ MAX_UINT256 :=
    (Verity.Proofs.Stdlib.Math.CheckedArithmetic.safeAdd_isSome_iff_addNoOverflow
      (s.storage 0) 1).mp (by simpa [leafNumber] using hAdd)
  have hLowEq : insertLow s value lowHint =
      walkResult (leafNumber s).val s lowHint value := by
    simp [insertLow, walkLowLeafFuel_eq_walkResult, leafNumber]
  rcases hInv.covering with ⟨old, hOld⟩
  have hWalk := covering_walk s value lowHint old hOld hhintLt hvalLt
  simpa [hLowEq] using And.intro hWalk.1
    (And.intro hWalk.2.1 (And.intro hWalk.2.2 (And.intro hvNe hAddLe)))


private theorem ne_of_lt_uint {a b : Uint256} (h : a < b) : a ≠ b := by
  intro heq
  subst heq
  exact Nat.lt_irrefl a.val (by simpa [lt_def] using h)

/-- Successful `insert` mutates only the predecessor hop, the fresh leaf,
    `valueToIndex[value]`, and `leafNumber`. Derived from
    `insert_run_of_success` by unfolding `insertPost`. -/
theorem insert_leaf_frame
    (value lowHint : Uint256) (s s' : ContractState) :
    insert_leaf_frame_spec value lowHint s s' := by
  unfold insert_leaf_frame_spec
  cases hrun : (IndexedMerkleTree.insert value lowHint).run s with
  | «revert» _ _ => simp [hrun]
  | success newIndex sPost =>
      simp [hrun]
      intro hs'
      subst hs'
      have hOk : insert_succeeds value lowHint s := by
        simp [insert_succeeds, hrun]
      have hchar := insert_run_of_success value lowHint s hOk
      have hEq : ContractResult.success newIndex sPost =
          ContractResult.success (leafNumber s) (insertPost s value lowHint) := by
        simpa [hrun] using hchar
      injection hEq with hNew hState
      subst hNew
      subst hState
      refine ⟨?vals, ?links, ?newVal, ?newIdx, ?ln, ?mapNew, ?mapOld⟩
      · intro i hi
        have hneNew : i ≠ leafNumber s := ne_of_lt_uint hi
        unfold insertPost leafValue
        simp [hneNew]
      · intro i hi hne
        have hneNew : i ≠ leafNumber s := ne_of_lt_uint hi
        have hneLow : i ≠ insertLow s value lowHint := by
          simpa [insertLow] using hne
        constructor
        · unfold insertPost nextIndex
          simp [hneNew, hneLow]
        · unfold insertPost nextValue
          simp [hneNew, hneLow]
      · unfold insertPost leafValue; simp
      · rfl
      · unfold insertPost leafNumber; simp
      · unfold insertPost valueToIndexOf; simp
      · intro v hv
        unfold insertPost valueToIndexOf
        simp [hv]

private def pNe (pred : Uint256) : Uint256 → Bool := fun x => decide (x ≠ pred)

private def spliceChain (chain : List Uint256) (pred newIndex : Uint256) :
    List Uint256 :=
  chain.takeWhile (pNe pred) ++ [pred, newIndex] ++
    (chain.dropWhile (pNe pred)).drop 1

private theorem takeWhile_ne_not_mem
    (chain : List Uint256) (pred : Uint256) :
    pred ∉ chain.takeWhile (pNe pred) := by
  induction chain with
  | nil => simp [List.takeWhile, pNe]
  | cons a rest ih =>
      unfold List.takeWhile
      split
      · next hpos =>
          have ha : a ≠ pred := of_decide_eq_true (by simpa [pNe] using hpos)
          intro hmem
          cases List.mem_cons.mp hmem with
          | inl heq =>
              have : a = pred := heq.symm
              exact ha this
          | inr h => exact ih h
      · next hneg => simp

private theorem dropWhile_ne_eq_cons
    (chain : List Uint256) (pred : Uint256) (hmem : pred ∈ chain) :
    ∃ rest, chain.dropWhile (pNe pred) = pred :: rest := by
  induction chain with
  | nil => cases hmem
  | cons a rest ih =>
      unfold List.dropWhile
      split
      · next hpos =>
          have ha : a ≠ pred := of_decide_eq_true (by simpa [pNe] using hpos)
          exact ih (mem_tail_of_ne hmem ha)
      · next hneg =>
          have : a = pred := by
            have : ¬ (a ≠ pred) := of_decide_eq_false (by simpa [pNe] using hneg)
            exact Classical.not_not.mp this
          refine ⟨rest, ?_⟩
          simp [this]

private theorem take_drop_split
    (chain : List Uint256) (pred : Uint256) :
    chain = chain.takeWhile (pNe pred) ++ chain.dropWhile (pNe pred) := by
  induction chain with
  | nil => simp [List.takeWhile, List.dropWhile, pNe]
  | cons a rest ih =>
      unfold List.takeWhile List.dropWhile
      split
      · next hpos =>
          simpa [List.cons_append] using congrArg (fun l => a :: l) ih
      · next hneg =>
          simp

private theorem splice_eq
    (chain : List Uint256) (pred newIndex : Uint256) (hmem : pred ∈ chain) :
    ∃ pref suff,
      chain = pref ++ pred :: suff ∧
      spliceChain chain pred newIndex = pref ++ pred :: newIndex :: suff ∧
      pred ∉ pref := by
  obtain ⟨suff, hdw⟩ := dropWhile_ne_eq_cons chain pred hmem
  let pref := chain.takeWhile (pNe pred)
  refine ⟨pref, suff, ?_⟩
  have hsplit := take_drop_split chain pred
  have hchain : chain = pref ++ pred :: suff := by
    calc
      chain = pref ++ chain.dropWhile (pNe pred) := hsplit
      _ = pref ++ pred :: suff := by rw [hdw]
  have hspl : spliceChain chain pred newIndex = pref ++ pred :: newIndex :: suff := by
    unfold spliceChain
    have hdrop : (chain.dropWhile (pNe pred)).drop 1 = suff := by
      rw [hdw]; simp
    simp [pref, hdrop, hdw]
  exact ⟨hchain, hspl, takeWhile_ne_not_mem chain pred⟩

private theorem splice_length
    (chain : List Uint256) (pred newIndex : Uint256) (hmem : pred ∈ chain) :
    (spliceChain chain pred newIndex).length = chain.length + 1 := by
  obtain ⟨pref, suff, hchain, hspl, _⟩ := splice_eq chain pred newIndex hmem
  rw [hspl, hchain]
  simp [List.length_append, List.length_cons]
  omega

private theorem splice_head_zero
    (chain : List Uint256) (pred newIndex : Uint256)
    (hmem : pred ∈ chain) (hHead : chain.head? = some (0 : Uint256)) :
    (spliceChain chain pred newIndex).head? = some 0 := by
  obtain ⟨pref, suff, hchain, hspl, _hpref⟩ := splice_eq chain pred newIndex hmem
  rw [hspl]
  cases pref with
  | nil =>
      have : (pred :: suff).head? = some 0 := by simpa [hchain] using hHead
      have : pred = 0 := by simpa using this
      simp [this]
  | cons a rest =>
      have : (a :: (rest ++ pred :: suff)).head? = some 0 := by
        simpa [hchain] using hHead
      have : a = 0 := by simpa using this
      simp [this]

private theorem noDup_cons
    (a : Uint256) (rest : List Uint256)
    (h : noDuplicateIndices (a :: rest)) :
    a ∉ rest ∧ noDuplicateIndices rest := h

private theorem noDup_of_append_left
    (pref rest : List Uint256) :
    noDuplicateIndices (pref ++ rest) → noDuplicateIndices pref := by
  induction pref with
  | nil => intro; trivial
  | cons a as ih =>
      intro h
      have ⟨ha, htail⟩ := noDup_cons a (as ++ rest) (by simpa [List.cons_append] using h)
      refine ⟨?_, ih htail⟩
      intro hmem
      exact ha (List.mem_append.mpr (Or.inl hmem))

private theorem noDup_of_append_right
    (pref rest : List Uint256) :
    noDuplicateIndices (pref ++ rest) → noDuplicateIndices rest := by
  induction pref with
  | nil => intro h; exact h
  | cons a as ih =>
      intro h
      have ⟨_, htail⟩ := noDup_cons a (as ++ rest) (by simpa [List.cons_append] using h)
      exact ih htail

private theorem not_mem_of_noDup_append
    (pref : List Uint256) (x : Uint256) (suff : List Uint256)
    (h : noDuplicateIndices (pref ++ x :: suff)) :
    x ∉ pref ∧ x ∉ suff := by
  induction pref with
  | nil =>
      have ⟨hx, _⟩ := noDup_cons x suff (by simpa using h)
      exact ⟨List.not_mem_nil, hx⟩
  | cons a as ih =>
      have ⟨ha, htail⟩ := noDup_cons a (as ++ x :: suff) (by simpa [List.cons_append] using h)
      have ⟨hxpref, hxsuff⟩ := ih htail
      refine ⟨?_, hxsuff⟩
      intro hmem
      cases List.mem_cons.mp hmem with
      | inl heq =>
          have : a = x := heq.symm
          have hxcons : x ∈ x :: suff := List.mem_cons_self
          have : a ∈ as ++ x :: suff := by
            simpa [this] using List.mem_append.mpr (Or.inr hxcons)
          exact ha this
      | inr hrest => exact hxpref hrest

private theorem noDup_append
    (pref rest : List Uint256)
    (hp : noDuplicateIndices pref)
    (hr : noDuplicateIndices rest)
    (hdisj : ∀ x, x ∈ pref → x ∉ rest) :
    noDuplicateIndices (pref ++ rest) := by
  induction pref with
  | nil => simpa using hr
  | cons a as ih =>
      have ⟨ha, has⟩ := noDup_cons a as hp
      have hdisj' : ∀ x, x ∈ as → x ∉ rest := by
        intro x hx
        exact hdisj x (List.mem_cons.mpr (Or.inr hx))
      have ih' := ih has hdisj'
      refine ⟨?_, ih'⟩
      intro hmem
      cases List.mem_append.mp hmem with
      | inl hin => exact ha hin
      | inr hin => exact hdisj a List.mem_cons_self hin

private theorem disjoint_of_noDup_append
    (pref rest : List Uint256)
    (h : noDuplicateIndices (pref ++ rest)) :
    ∀ x, x ∈ pref → x ∉ rest := by
  induction pref with
  | nil => intro x hx; cases hx
  | cons a as ih =>
      have ⟨ha, htail⟩ := noDup_cons a (as ++ rest) (by simpa [List.cons_append] using h)
      intro x hx
      cases List.mem_cons.mp hx with
      | inl heq =>
          have : a = x := heq.symm
          intro hin
          exact ha (by simpa [this] using List.mem_append.mpr (Or.inr hin))
      | inr hrest => exact ih htail x hrest

private theorem noDup_splice
    (chain : List Uint256) (pred newIndex : Uint256)
    (hmem : pred ∈ chain)
    (hNodup : noDuplicateIndices chain)
    (hne : newIndex ∉ chain) :
    noDuplicateIndices (spliceChain chain pred newIndex) := by
  obtain ⟨pref, suff, hchain, hspl, hprefNe⟩ := splice_eq chain pred newIndex hmem
  have hN : noDuplicateIndices (pref ++ pred :: suff) := by simpa [hchain] using hNodup
  have hprefN := noDup_of_append_left pref (pred :: suff) hN
  have hxs := noDup_of_append_right pref (pred :: suff) hN
  have ⟨_hxpref, hxsuff⟩ := not_mem_of_noDup_append pref pred suff hN
  have ⟨_, hsuffN⟩ := noDup_cons pred suff hxs
  have hnewPref : newIndex ∉ pref := by
    intro hx
    have : newIndex ∈ pref ++ pred :: suff := List.mem_append.mpr (Or.inl hx)
    exact hne (by simpa [hchain] using this)
  have hnewSuff : newIndex ∉ suff := by
    intro hx
    have : newIndex ∈ pref ++ pred :: suff :=
      List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hx)))
    exact hne (by simpa [hchain] using this)
  have hnewPred : newIndex ≠ pred := by
    intro heq
    exact hne (by simpa [heq] using hmem)
  have hmid : noDuplicateIndices (pred :: newIndex :: suff) := by
    refine ⟨?_, ⟨hnewSuff, hsuffN⟩⟩
    intro hmem'
    cases List.mem_cons.mp hmem' with
    | inl heq => exact hnewPred heq.symm
    | inr hs => exact hxsuff hs
  have hdisjOld := disjoint_of_noDup_append pref (pred :: suff) hN
  have hdisj : ∀ x, x ∈ pref → x ∉ pred :: newIndex :: suff := by
    intro x hx hmem'
    cases List.mem_cons.mp hmem' with
    | inl heq =>
        have : x = pred := heq
        exact hprefNe (by simpa [this] using hx)
    | inr hrest =>
        cases List.mem_cons.mp hrest with
        | inl heq =>
            have : x = newIndex := heq
            exact hnewPref (by simpa [this] using hx)
        | inr hs =>
            exact hdisjOld x hx (List.mem_cons.mpr (Or.inr hs))
  rw [hspl]
  exact noDup_append pref (pred :: newIndex :: suff) hprefN hmid hdisj

private theorem insertPost_leafNumber
    (s : ContractState) (value lowHint : Uint256) :
    leafNumber (insertPost s value lowHint) =
      EVM.Uint256.add (leafNumber s) 1 := by
  simp [insertPost, leafNumber]

private theorem insertPost_leafValue_old
    (s : ContractState) (value lowHint i : Uint256)
    (hi : i ≠ leafNumber s) :
    leafValue (insertPost s value lowHint) i = leafValue s i := by
  unfold insertPost leafValue
  simp [hi]

private theorem insertPost_leafValue_new
    (s : ContractState) (value lowHint : Uint256) :
    leafValue (insertPost s value lowHint) (leafNumber s) = value := by
  unfold insertPost leafValue
  simp

private theorem insertPost_next_pred
    (s : ContractState) (value lowHint : Uint256)
    (hPred : insertLow s value lowHint ≠ leafNumber s) :
    nextIndex (insertPost s value lowHint) (insertLow s value lowHint) =
      leafNumber s ∧
    nextValue (insertPost s value lowHint) (insertLow s value lowHint) =
      value := by
  unfold insertPost nextIndex nextValue
  simp [hPred]

private theorem insertPost_next_new
    (s : ContractState) (value lowHint : Uint256) :
    nextIndex (insertPost s value lowHint) (leafNumber s) =
      nextIndex s (insertLow s value lowHint) ∧
    nextValue (insertPost s value lowHint) (leafNumber s) =
      nextValue s (insertLow s value lowHint) := by
  unfold insertPost nextIndex nextValue
  simp

private theorem insertPost_next_old
    (s : ContractState) (value lowHint i : Uint256)
    (hi : i ≠ insertLow s value lowHint) (hinew : i ≠ leafNumber s) :
    nextIndex (insertPost s value lowHint) i = nextIndex s i ∧
    nextValue (insertPost s value lowHint) i = nextValue s i := by
  unfold insertPost nextIndex nextValue
  simp [hi, hinew]

private theorem insertPost_valueToIndex_new
    (s : ContractState) (value lowHint : Uint256) :
    valueToIndexOf (insertPost s value lowHint) value = leafNumber s := by
  unfold insertPost valueToIndexOf
  simp

private theorem insertPost_valueToIndex_old
    (s : ContractState) (value lowHint v : Uint256) (hv : v ≠ value) :
    valueToIndexOf (insertPost s value lowHint) v = valueToIndexOf s v := by
  unfold insertPost valueToIndexOf
  simp [hv]

private theorem insertPost_occupied
    (s : ContractState) (value lowHint i : Uint256)
    (hAdd : (leafNumber s).val + 1 ≤ MAX_UINT256) :
    occupied (insertPost s value lowHint) i ↔
      occupied s i ∨ i = leafNumber s := by
  have hln :
      (leafNumber (insertPost s value lowHint)).val =
        (leafNumber s).val + 1 := by
    have hEq := insertPost_leafNumber s value lowHint
    have : ((EVM.Uint256.add (leafNumber s) 1 : Uint256) : Nat) =
        (leafNumber s).val + 1 :=
      EVM.Uint256.add_eq_of_lt (by
        have : (leafNumber s).val + 1 < 2 ^ 256 :=
          Nat.lt_of_le_of_lt hAdd (by decide)
        simpa [Nat.cast_ofNat] using this)
    simpa [hEq] using this
  constructor
  · intro hi
    have : i.val < (leafNumber s).val + 1 := by
      simpa [occupied, hln, lt_def] using hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp this with hlt | heq
    · left; simpa [occupied, lt_def] using hlt
    · right
      exact ext heq
  · intro h
    rcases h with hOld | hNew
    · have : i.val < (leafNumber s).val := by simpa [occupied, lt_def] using hOld
      have : i.val < (leafNumber s).val + 1 := Nat.lt_succ_of_lt this
      simpa [occupied, hln, lt_def] using this
    · subst hNew
      have : (leafNumber s).val < (leafNumber s).val + 1 := Nat.lt_succ_self _
      simpa [occupied, hln, lt_def] using this

/-- Sentinel leaf value is unchanged: index 0 is never the fresh index. -/
private theorem insertPost_sentinelValue
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    sentinelValueOk (insertPost s value lowHint) := by
  have hv0 : leafValue s 0 = 0 := hInv.sentinelValue
  have hln0 : (0 : Uint256) ≠ leafNumber s := by
    intro h
    have hval := congrArg Verity.Core.Uint256.val h.symm
    have : (leafNumber s).val = 0 := by simpa [val_zero] using hval
    rcases hInv.covering with ⟨old, hHead, hLen, _hNodup, _hChain, _hMem, _hInc, _hTail⟩
    have hlen0 : old.length = 0 := by simpa [this] using hLen
    have : old = [] := List.length_eq_zero_iff.mp hlen0
    subst this
    cases hHead
  unfold sentinelValueOk
  rw [insertPost_leafValue_old s value lowHint 0 hln0]
  exact hv0

private theorem covering_head
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    old.head? = some 0 := by
  rcases hOld with ⟨hHead, _⟩
  exact hHead

private theorem covering_len
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    old.length = (leafNumber s).val := by
  rcases hOld with ⟨_, hLen, _⟩
  exact hLen

private theorem covering_nodup
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    noDuplicateIndices old := by
  rcases hOld with ⟨_, _, hNodup, _⟩
  exact hNodup

private theorem covering_chain
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    isIndexChain s old := by
  rcases hOld with ⟨_, _, _, hChain, _⟩
  exact hChain

private theorem covering_mem
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) (i : Uint256) :
    occupied s i ↔ i ∈ old := by
  rcases hOld with ⟨_, _, _, _, hMem, _⟩
  exact hMem i

private theorem covering_inc
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    chainValuesIncrease s old := by
  rcases hOld with ⟨_, _, _, _, _, hInc, _⟩
  exact hInc

private theorem covering_tail
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    ∀ t, old.getLast? = some t → nextIndex s t = 0 ∧ nextValue s t = 0 := by
  rcases hOld with ⟨_, _, _, _, _, _, hTail⟩
  exact hTail

private theorem fresh_not_mem_old
    (s : ContractState) (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    leafNumber s ∉ old := by
  intro hmem
  have hocc : occupied s (leafNumber s) := (covering_mem s old hOld _).mpr hmem
  have : (leafNumber s).val < (leafNumber s).val := by
    simpa [occupied, lt_def] using hocc
  exact Nat.lt_irrefl _ this

private theorem pred_ne_new
    (s : ContractState) (value lowHint : Uint256)
    (hOcc : occupied s (insertLow s value lowHint)) :
    insertLow s value lowHint ≠ leafNumber s := by
  intro heq
  have : (leafNumber s).val < (leafNumber s).val := by
    simpa [occupied, lt_def, heq] using hOcc
  exact Nat.lt_irrefl _ this

private theorem isIndexChain_append
    (s : ContractState) (pref : List Uint256) (x : Uint256) (suff : List Uint256)
    (h : isIndexChain s (pref ++ x :: suff)) :
    isIndexChain s (x :: suff) := by
  induction pref with
  | nil => simpa using h
  | cons a as ih =>
      have hcons : isIndexChain s (a :: (as ++ x :: suff)) := by
        simpa [List.cons_append] using h
      cases htl : as ++ x :: suff with
      | nil =>
          have : x ∈ as ++ x :: suff :=
            List.mem_append.mpr (Or.inr List.mem_cons_self)
          simp [htl] at this
      | cons b rest =>
          have hcons' : isIndexChain s (a :: b :: rest) := by simpa [htl] using hcons
          have ⟨_, _, hrest⟩ := chain_index_cons s a b rest hcons'
          exact ih (by simpa [htl] using hrest)

private theorem chain_last_eq
    (pref : List Uint256) (x : Uint256) (suff : List Uint256) :
    (pref ++ x :: suff).getLast? = (x :: suff).getLast? := by
  induction pref with
  | nil => simp
  | cons a as ih =>
      have hne : as ++ x :: suff ≠ [] := by
        intro h
        have : x ∈ as ++ x :: suff :=
          List.mem_append.mpr (Or.inr List.mem_cons_self)
        simp [h] at this
      simpa [List.cons_append, List.getLast?_cons_of_ne_nil hne] using ih

private theorem lt_of_not_lt_of_ne
    {a b : Uint256} (hnlt : ¬ b < a) (hne : a ≠ b) : a < b := by
  have hneval : a.val ≠ b.val := by
    intro h
    exact hne (ext h)
  have hle : a.val ≤ b.val := Nat.le_of_not_gt (by
    intro hlt
    have : b < a := by simpa [lt_def] using hlt
    exact hnlt this)
  have : a.val < b.val := Nat.lt_of_le_of_ne hle hneval
  simpa [lt_def] using this

private theorem isIndexChain_preserved
    (s s' : ContractState) :
    ∀ chain,
      (∀ a ∈ chain,
        nextIndex s' a = nextIndex s a ∧
        nextValue s' a = nextValue s a ∧
        leafValue s' a = leafValue s a) →
      isIndexChain s chain → isIndexChain s' chain
  | [], _, h => h
  | [_], _, h => h
  | a :: b :: rest, hmem, h => by
      have ⟨hni, hnv, hrest⟩ := chain_index_cons s a b rest h
      have ha := hmem a List.mem_cons_self
      have hb := hmem b (List.mem_cons.mpr (Or.inr List.mem_cons_self))
      refine ⟨?_, ?_,
        isIndexChain_preserved s s' (b :: rest)
          (fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))) hrest⟩
      · rw [ha.1, hni]
      · rw [ha.2.1, hb.2.2, hnv]

private theorem chainValuesIncrease_preserved
    (s s' : ContractState) :
    ∀ chain,
      (∀ a ∈ chain, leafValue s' a = leafValue s a) →
      chainValuesIncrease s chain → chainValuesIncrease s' chain
  | [], _, h => h
  | [_], _, h => h
  | a :: b :: rest, hmem, h => by
      have ⟨hlt, hrest⟩ : leafValue s a < leafValue s b ∧
          chainValuesIncrease s (b :: rest) := h
      refine ⟨?_,
        chainValuesIncrease_preserved s s' (b :: rest)
          (fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))) hrest⟩
      simpa [hmem a List.mem_cons_self,
        hmem b (List.mem_cons.mpr (Or.inr List.mem_cons_self))] using hlt

private theorem chainValuesIncrease_suffix
    (s : ContractState) :
    ∀ pref x suff,
      chainValuesIncrease s (pref ++ x :: suff) →
      chainValuesIncrease s (x :: suff)
  | [], _, _, h => h
  | a :: as, x, suff, h => by
      have hcons : chainValuesIncrease s (a :: (as ++ x :: suff)) := by
        simpa [List.cons_append] using h
      cases htl : as ++ x :: suff with
      | nil =>
          have : x ∈ as ++ x :: suff :=
            List.mem_append.mpr (Or.inr List.mem_cons_self)
          simp [htl] at this
      | cons b rest =>
          have hcons' : chainValuesIncrease s (a :: b :: rest) := by simpa [htl] using hcons
          have hrest : chainValuesIncrease s (as ++ x :: suff) := by
            have : b :: rest = as ++ x :: suff := htl.symm
            simpa [this] using hcons'.2
          exact chainValuesIncrease_suffix s as x suff hrest


private theorem isIndexChain_splice
    (s s' : ContractState) (pred newIndex : Uint256) (pref suff : List Uint256)
    (hNe : pred ≠ newIndex)
    (hOld : isIndexChain s (pref ++ pred :: suff))
    (hpred : nextIndex s' pred = newIndex ∧
      nextValue s' pred = leafValue s' newIndex)
    (hnew : nextIndex s' newIndex = nextIndex s pred ∧
      nextValue s' newIndex = nextValue s pred)
    (hold : ∀ i, i ≠ pred → i ≠ newIndex →
      nextIndex s' i = nextIndex s i ∧
      nextValue s' i = nextValue s i ∧
      leafValue s' i = leafValue s i)
    (hpredLeaf : leafValue s' pred = leafValue s pred)
    (hSuffFresh : ∀ x ∈ suff, x ≠ pred ∧ x ≠ newIndex)
    (hPrefFresh : ∀ x ∈ pref, x ≠ pred ∧ x ≠ newIndex) :
    isIndexChain s' (pref ++ pred :: newIndex :: suff) := by
  induction pref with
  | nil =>
      refine ⟨hpred.1, hpred.2, ?_⟩
      cases suff with
      | nil => trivial
      | cons z zs =>
          have hOld' : isIndexChain s (pred :: z :: zs) := by simpa using hOld
          have ⟨hni, hnv, hrest⟩ := chain_index_cons s pred z zs hOld'
          have hz := hSuffFresh z List.mem_cons_self
          have hzleaf := (hold z hz.1 hz.2).2.2
          refine ⟨?_, ?_,
            isIndexChain_preserved s s' (z :: zs)
              (fun i hi =>
                hold i (hSuffFresh i hi).1 (hSuffFresh i hi).2)
              hrest⟩
          · rw [hnew.1, hni]
          · rw [hnew.2, hnv, hzleaf]
  | cons a as ih =>
      have hcons : isIndexChain s (a :: (as ++ pred :: suff)) := by
        simpa [List.cons_append] using hOld
      have ha := hPrefFresh a List.mem_cons_self
      have hOldAs : isIndexChain s (as ++ pred :: suff) := by
        cases htl : as ++ pred :: suff with
        | nil =>
            have : pred ∈ as ++ pred :: suff :=
              List.mem_append.mpr (Or.inr List.mem_cons_self)
            simp [htl] at this
        | cons b rest =>
            have hcons' : isIndexChain s (a :: b :: rest) := by simpa [htl] using hcons
            have ⟨_, _, hrest⟩ := chain_index_cons s a b rest hcons'
            simpa [htl] using hrest
      have ih' := ih hOldAs (fun x hx => hPrefFresh x (List.mem_cons.mpr (Or.inr hx)))
      cases as with
      | nil =>
          have hOld' : isIndexChain s (a :: pred :: suff) := by simpa using hcons
          have hni' : nextIndex s a = pred := by
            cases suff with
            | nil =>
                have h2 : isIndexChain s [a, pred] := by simpa using hOld'
                simpa [isIndexChain] using h2.1
            | cons z zs =>
                exact (chain_index_cons s a pred (z :: zs) (by simpa using hOld')).1
          have hnv' : nextValue s a = leafValue s pred := by
            cases suff with
            | nil =>
                have h2 : isIndexChain s [a, pred] := by simpa using hOld'
                simpa [isIndexChain] using h2.2.1
            | cons z zs =>
                exact (chain_index_cons s a pred (z :: zs) (by simpa using hOld')).2.1
          refine ⟨?_, ?_, ih'⟩
          · have := (hold a ha.1 ha.2).1
            rw [this, hni']
          · have := (hold a ha.1 ha.2).2.1
            have hpredLeaf' : leafValue s' pred = leafValue s pred := hpredLeaf
            rw [this, hnv', hpredLeaf']
      | cons c cs =>
          have hOld' : isIndexChain s (a :: c :: (cs ++ pred :: suff)) := by
            simpa [List.cons_append] using hcons
          have ⟨hni, hnv, _⟩ := chain_index_cons s a c (cs ++ pred :: suff) hOld'
          have hc := hPrefFresh c (List.mem_cons.mpr (Or.inr List.mem_cons_self))
          refine ⟨?_, ?_, ih'⟩
          · have := (hold a ha.1 ha.2).1
            rw [this, hni]
          · have := (hold a ha.1 ha.2).2.1
            have hcleaf := (hold c hc.1 hc.2).2.2
            rw [this, hnv, hcleaf]

private theorem chainValuesIncrease_splice
    (s s' : ContractState) (pred newIndex : Uint256) (pref suff : List Uint256)
    (hIncOld : chainValuesIncrease s (pref ++ pred :: suff))
    (hIncMid : chainValuesIncrease s' (pred :: newIndex :: suff))
    (hleafOld : ∀ i, i ≠ newIndex → leafValue s' i = leafValue s i)
    (hPrefFresh : ∀ x ∈ pref, x ≠ pred ∧ x ≠ newIndex)
    (hpredNeNew : pred ≠ newIndex) :
    chainValuesIncrease s' (pref ++ pred :: newIndex :: suff) := by
  induction pref with
  | nil => simpa using hIncMid
  | cons a as ih =>
      have hcons : chainValuesIncrease s (a :: (as ++ pred :: suff)) := by
        simpa [List.cons_append] using hIncOld
      have ha := hPrefFresh a List.mem_cons_self
      have hleafA : leafValue s' a = leafValue s a := hleafOld a ha.2
      have hIncAs : chainValuesIncrease s (as ++ pred :: suff) := by
        cases htl : as ++ pred :: suff with
        | nil =>
            have : pred ∈ as ++ pred :: suff :=
              List.mem_append.mpr (Or.inr List.mem_cons_self)
            simp [htl] at this
        | cons b rest =>
            have hcons' : chainValuesIncrease s (a :: b :: rest) := by
              simpa [htl] using hcons
            have : b :: rest = as ++ pred :: suff := htl.symm
            simpa [this] using hcons'.2
      have ih' := ih hIncAs (fun x hx => hPrefFresh x (List.mem_cons.mpr (Or.inr hx)))
      cases as with
      | nil =>
          have hIncOld' : chainValuesIncrease s (a :: pred :: suff) := by
            simpa using hcons
          have hlt : leafValue s a < leafValue s pred := hIncOld'.1
          have hleafPred : leafValue s' pred = leafValue s pred :=
            hleafOld pred (by intro h; exact hpredNeNew h)
          refine ⟨?_, ih'⟩
          simpa [hleafA, hleafPred] using hlt
      | cons c cs =>
          have hIncOld' : chainValuesIncrease s (a :: c :: (cs ++ pred :: suff)) := by
            simpa [List.cons_append] using hcons
          have hlt : leafValue s a < leafValue s c := hIncOld'.1
          have hc := hPrefFresh c (List.mem_cons.mpr (Or.inr List.mem_cons_self))
          have hleafC : leafValue s' c = leafValue s c := hleafOld c hc.2
          refine ⟨?_, ih'⟩
          simpa [hleafA, hleafC] using hlt

/-- Successful insert splices the fresh index after the walk predecessor. -/
theorem insert_spliced_chain
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s)
    (hAbs : valueNotStored s value)
    (hWalk : occupied s (insertLow s value lowHint) ∧
      leafValue s (insertLow s value lowHint) < value ∧
      (nextValue s (insertLow s value lowHint) = 0 ∨
        ¬ nextValue s (insertLow s value lowHint) < value) ∧
      value ≠ 0 ∧
      (leafNumber s).val + 1 ≤ MAX_UINT256)
    (old : List Uint256)
    (hOld : isCoveringOrderedChain s old) :
    let pred := insertLow s value lowHint
    let newIndex := leafNumber s
    let chain := spliceChain old pred newIndex
    let s' := insertPost s value lowHint
    isCoveringOrderedChain s' chain := by
  let pred := insertLow s value lowHint
  let newIndex := leafNumber s
  let chain := spliceChain old pred newIndex
  let s' := insertPost s value lowHint
  have hpredOcc := hWalk.1
  have hLt := hWalk.2.1
  have hStop := hWalk.2.2.1
  have hAdd := hWalk.2.2.2.2
  have hpredMem : pred ∈ old := (covering_mem s old hOld pred).mp hpredOcc
  obtain ⟨pref, suff, hchain, hspl, _hprefNe⟩ := splice_eq old pred newIndex hpredMem
  have hs' : s' = insertPost s value lowHint := rfl
  have hpredNeNew := pred_ne_new s value lowHint hpredOcc
  have hnewNmem := fresh_not_mem_old s old hOld
  -- head
  have hHead' : chain.head? = some 0 := by
    simpa [chain] using splice_head_zero old pred newIndex hpredMem (covering_head s old hOld)
  -- length
  have hLen' : chain.length = (leafNumber s').val := by
    have hlen := splice_length old pred newIndex hpredMem
    have hln :
        (leafNumber s').val = (leafNumber s).val + 1 := by
      have hEq := insertPost_leafNumber s value lowHint
      have : ((EVM.Uint256.add (leafNumber s) 1 : Uint256) : Nat) =
          (leafNumber s).val + 1 :=
        EVM.Uint256.add_eq_of_lt (by
          have : (leafNumber s).val + 1 < 2 ^ 256 :=
            Nat.lt_of_le_of_lt hAdd (by decide)
          simpa [Nat.cast_ofNat] using this)
      simpa [hs', hEq] using this
    have hlenEq : chain.length = old.length + 1 := by simpa [chain] using hlen
    have holdLen : old.length = (leafNumber s).val := covering_len s old hOld
    simpa [hlenEq, holdLen, hln]
  -- uniqueness
  have hNodup' : noDuplicateIndices chain := by
    simpa [chain] using noDup_splice old pred newIndex hpredMem
      (covering_nodup s old hOld) hnewNmem
  -- membership / occupancy
  have hMem' : ∀ i, occupied s' i ↔ i ∈ chain := by
    intro i
    have hocc := insertPost_occupied s value lowHint i hAdd
    constructor
    · intro hi
      have : occupied s i ∨ i = newIndex := by
        simpa [hs', occupied, newIndex] using (hocc.mp (by simpa [hs'] using hi))
      rcases this with hOldi | hNew
      · have : i ∈ old := (covering_mem s old hOld i).mp hOldi
        -- old = pref ++ pred :: suff, chain = pref ++ pred :: newIndex :: suff
        have : i ∈ pref ++ pred :: suff := by simpa [hchain] using this
        have : i ∈ pref ++ pred :: newIndex :: suff := by
          cases List.mem_append.mp this with
          | inl hp => exact List.mem_append.mpr (Or.inl hp)
          | inr hr =>
              cases List.mem_cons.mp hr with
              | inl heq =>
                  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq)))
              | inr hs =>
                  exact List.mem_append.mpr
                    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hs)))))
        simpa [chain, hspl] using this
      · subst hNew
        have : newIndex ∈ pref ++ pred :: newIndex :: suff :=
          List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr List.mem_cons_self)))
        simpa [chain, hspl] using this
    · intro hi
      have : i ∈ pref ++ pred :: newIndex :: suff := by simpa [chain, hspl] using hi
      cases List.mem_append.mp this with
      | inl hp =>
          have holdMem : i ∈ old := by
            have : i ∈ pref ++ pred :: suff := List.mem_append.mpr (Or.inl hp)
            simpa [hchain] using this
          have hoccOld : occupied s i := (covering_mem s old hOld i).mpr holdMem
          exact hocc.mpr (Or.inl hoccOld)
      | inr hr =>
          cases List.mem_cons.mp hr with
          | inl heq =>
              have hiPred : i = pred := heq
              exact hocc.mpr (Or.inl (by simpa [hiPred] using hpredOcc))
          | inr hrest =>
              cases List.mem_cons.mp hrest with
              | inl heq =>
                  have : i = newIndex := heq
                  exact hocc.mpr (Or.inr (by simpa [hs', this, newIndex]))
              | inr hs =>
                  have holdMem : i ∈ old := by
                    have : i ∈ pref ++ pred :: suff :=
                      List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hs)))
                    simpa [hchain] using this
                  have hoccOld : occupied s i := (covering_mem s old hOld i).mpr holdMem
                  exact hocc.mpr (Or.inl hoccOld)
  -- remaining fields: chain, increase, tail. Prove from splice split.
  have hChOld := covering_chain s old hOld
  have hIncOld := covering_inc s old hOld
  have hTailOld := covering_tail s old hOld
  have hChSuff : isIndexChain s (pred :: suff) :=
    isIndexChain_append s pref pred suff (by simpa [hchain] using hChOld)
  have hSuffFresh : ∀ x ∈ suff, x ≠ pred ∧ x ≠ newIndex := by
    intro x hx
    have hxold : x ∈ old := by
      simpa [hchain] using List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hx)))
    refine ⟨?_, ?_⟩
    · intro heq
      have ⟨_, hpredNotSuff⟩ := not_mem_of_noDup_append pref pred suff
        (by simpa [hchain] using covering_nodup s old hOld)
      exact hpredNotSuff (by simpa [heq] using hx)
    · intro heq
      exact hnewNmem (by simpa [heq] using hxold)
  have hPrefFresh : ∀ x ∈ pref, x ≠ pred ∧ x ≠ newIndex := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro heq
      have ⟨hpredNotPref, _⟩ := not_mem_of_noDup_append pref pred suff
        (by simpa [hchain] using covering_nodup s old hOld)
      exact hpredNotPref (by simpa [heq] using hx)
    · intro heq
      have hxold : newIndex ∈ old := by
        have hx' : x ∈ pref ++ pred :: suff := List.mem_append.mpr (Or.inl hx)
        have : newIndex ∈ pref ++ pred :: suff := by simpa [heq] using hx'
        simpa [hchain] using this
      exact hnewNmem hxold
  have hCh' : isIndexChain s' chain := by
    have hpred' := insertPost_next_pred s value lowHint hpredNeNew
    have hnew' := insertPost_next_new s value lowHint
    have hleafNew : leafValue s' newIndex = value := by
      simpa [hs', newIndex] using insertPost_leafValue_new s value lowHint
    rw [show chain = pref ++ pred :: newIndex :: suff from hspl]
    refine isIndexChain_splice s s' pred newIndex pref suff hpredNeNew
      (by simpa [hchain] using hChOld)
      ⟨by simpa [hs', pred, newIndex] using hpred'.1,
        by
          have : nextValue s' pred = value := by
            simpa [hs', pred] using hpred'.2
          simpa [this, hleafNew]⟩
      ⟨by simpa [hs', pred, newIndex] using hnew'.1,
        by simpa [hs', pred, newIndex] using hnew'.2⟩
      (fun i hi hinew => by
        have hnext := insertPost_next_old s value lowHint i
          (by simpa [pred] using hi) (by simpa [newIndex] using hinew)
        have hleaf := insertPost_leafValue_old s value lowHint i
          (by simpa [newIndex] using hinew)
        exact ⟨by simpa [hs'] using hnext.1,
          by simpa [hs'] using hnext.2,
          by simpa [hs'] using hleaf⟩)
      (insertPost_leafValue_old s value lowHint pred (by simpa [newIndex] using hpredNeNew)
        ▸ (by rfl))
      hSuffFresh hPrefFresh
  have hInc' : chainValuesIncrease s' chain := by
    have hleafOld : ∀ i, i ≠ newIndex → leafValue s' i = leafValue s i := by
      intro i hi
      simpa [hs'] using insertPost_leafValue_old s value lowHint i (by simpa [newIndex] using hi)
    have hleafNew : leafValue s' newIndex = value := by
      simpa [hs', newIndex] using insertPost_leafValue_new s value lowHint
    -- increase along pref ++ pred, then pred < new, then new < first suff, then rest
    have hIncSplit : chainValuesIncrease s (pref ++ pred :: suff) := by
      simpa [hchain] using hIncOld
    rw [show chain = pref ++ pred :: newIndex :: suff from hspl]
    -- prove by induction on pref, reusing preserved increase on unchanged hops
    have hIncSuff : chainValuesIncrease s (pred :: suff) :=
      chainValuesIncrease_suffix s pref pred suff hIncSplit
    have hIncSuff' : chainValuesIncrease s' (newIndex :: suff) := by
      cases suff with
      | nil => trivial
      | cons z zs =>
          have hIncOldSuff : chainValuesIncrease s (pred :: z :: zs) := by
            simpa using hIncSuff
          have ⟨hltPredZ, hIncZ⟩ :=
            (hIncOldSuff : leafValue s pred < leafValue s z ∧
              chainValuesIncrease s (z :: zs))
          have hzNe := hSuffFresh z List.mem_cons_self
          have hleafZ : leafValue s' z = leafValue s z := hleafOld z hzNe.2
          have hnv : nextValue s pred = leafValue s z :=
            (chain_index_cons s pred z zs (by simpa using hChSuff)).2.1
          have hstrict : value < leafValue s z := by
            rcases hStop with hnv0 | hnlt
            · have hz0 : leafValue s z = 0 := by
                have hnv0' : nextValue s pred = 0 := by simpa [pred] using hnv0
                have : leafValue s z = nextValue s pred := hnv.symm
                exact this.trans hnv0'
              have hlt0 : leafValue s pred < 0 := by simpa [hz0] using hltPredZ
              have : False := by
                have : (leafValue s pred).val < 0 := by simpa [lt_def] using hlt0
                exact Nat.not_lt_zero _ this
              exact this.elim
            · have hneVal : value ≠ leafValue s z := by
                have hzold : z ∈ old := by
                  have : z ∈ pref ++ pred :: z :: zs :=
                    List.mem_append.mpr (Or.inr (List.mem_cons.mpr
                      (Or.inr List.mem_cons_self)))
                  simpa [hchain] using this
                have hoccZ : occupied s z := (covering_mem s old hOld z).mpr hzold
                exact (hAbs z hoccZ).symm
              have hnlt' : ¬ leafValue s z < value := by
                have hnv' : nextValue s pred = leafValue s z := hnv
                have : ¬ nextValue s pred < value := by simpa [pred] using hnlt
                simpa [hnv'] using this
              exact lt_of_not_lt_of_ne hnlt' hneVal
          refine ⟨?_,
            chainValuesIncrease_preserved s s' (z :: zs)
              (fun i hi => hleafOld i (hSuffFresh i hi).2)
              hIncZ⟩
          simpa [hleafNew, hleafZ] using hstrict
    -- glue pref ++ pred with newIndex :: suff
    have hIncMid : chainValuesIncrease s' (pred :: newIndex :: suff) := by
      have hleafPred : leafValue s' pred = leafValue s pred :=
        hleafOld pred (by intro h; exact hpredNeNew h)
      refine ⟨?_, hIncSuff'⟩
      simpa [hleafPred, hleafNew] using hLt
    exact chainValuesIncrease_splice s s' pred newIndex pref suff
      hIncSplit hIncMid hleafOld hPrefFresh hpredNeNew
  have hTail' : ∀ t, chain.getLast? = some t →
      nextIndex s' t = 0 ∧ nextValue s' t = 0 := by
    intro t ht
    have ht' : (pred :: newIndex :: suff).getLast? = some t := by
      have : chain.getLast? = (pred :: newIndex :: suff).getLast? := by
        simpa [chain, hspl] using chain_last_eq pref pred (newIndex :: suff)
      simpa [this] using ht
    have htOld : old.getLast? = (pred :: suff).getLast? := by
      simpa [hchain] using chain_last_eq pref pred suff
    cases suff with
    | nil =>
        have htEq : t = newIndex := by
          have hlast : (pred :: newIndex :: ([] : List Uint256)).getLast? =
              some t := ht'
          simp at hlast
          exact hlast.symm
        subst htEq
        have hLastPred : old.getLast? = some pred := by simpa [htOld]
        have ⟨hni0, hnv0⟩ := hTailOld pred hLastPred
        have hnew' := insertPost_next_new s value lowHint
        exact ⟨by simpa [hs', pred, newIndex, hni0] using hnew'.1,
          by simpa [hs', pred, newIndex, hnv0] using hnew'.2⟩
    | cons z zs =>
        have : (pred :: newIndex :: z :: zs).getLast? = (z :: zs).getLast? := by
          simp
        have htSuff : (z :: zs).getLast? = some t := by simpa [this] using ht'
        have hLastOld : old.getLast? = some t := by
          have : (pred :: z :: zs).getLast? = (z :: zs).getLast? := by simp
          simpa [htOld, this] using htSuff
        have ⟨hni0, hnv0⟩ := hTailOld t hLastOld
        have htNePred : t ≠ pred := by
          intro heq
          have ⟨_, hpredNotSuff⟩ := not_mem_of_noDup_append pref pred (z :: zs)
            (by simpa [hchain] using covering_nodup s old hOld)
          have : t ∈ z :: zs := List.mem_of_mem_getLast? htSuff
          exact hpredNotSuff (by simpa [heq] using this)
        have htNeNew : t ≠ newIndex := by
          intro heq
          have : t ∈ old := List.mem_of_mem_getLast? hLastOld
          exact hnewNmem (by simpa [heq] using this)
        have hnext := insertPost_next_old s value lowHint t
          (by simpa [pred] using htNePred) (by simpa [newIndex] using htNeNew)
        exact ⟨by simpa [hs', hni0] using hnext.1,
          by simpa [hs', hnv0] using hnext.2⟩
  exact ⟨hHead', hLen', hNodup', hCh', hMem', hInc', hTail'⟩

private theorem insertPost_covers
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s)
    (hAbs : valueNotStored s value) :
    coveringOrderedChain (insertPost s value lowHint) := by
  have hWalk := insert_walk_brackets value lowHint s hInv hOk
  rcases hInv.covering with ⟨old, hOld⟩
  have hSplice := insert_spliced_chain value lowHint s hInv hOk hAbs hWalk old hOld
  exact ⟨_, hSplice⟩

theorem insert_preserves_order_of_frame
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s)
    (hAbs : valueNotStored s value) :
    IMTOrder (insertPost s value lowHint) := by
  exact {
    sentinelValue := insertPost_sentinelValue value lowHint s hInv hOk
    covering := insertPost_covers value lowHint s hInv hOk hAbs
  }

/-- A successful `insert` preserves `IMTOrder`. -/
theorem insert_preserves_order
    (value lowHint : Uint256) (s : ContractState) :
    insert_preserves_spec value lowHint s := by
  intro hInv hOk hAbs
  have hchar := insert_run_of_success value lowHint s hOk
  have _hFrame := insert_leaf_frame value lowHint s
      ((IndexedMerkleTree.insert value lowHint).run s).snd
  rw [hchar]
  exact insert_preserves_order_of_frame value lowHint s hInv hOk hAbs

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
