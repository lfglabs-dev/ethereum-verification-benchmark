import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.MappingAutomation
import Verity.Proofs.Stdlib.Math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 8000000

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Core.Uint256

/-
  Reference proofs for IMT linked-list order.

  Theorems:
  - `setup_establishes_order` (proved)
  - `insert_leaf_frame` (axiom: unfolding of `insertPost`)
  - `insert_preserves_order` (axiom: list-splice reconstruction)

  No `sorry`.
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
    sentinel := ?sent
    covers := ?cov
    increasing := ?inc
    tail := ?tail
    domains := ?dom
    nonzero := ?nz
    mapping := ?map
    bracket := ?br
  }
  · refine ⟨?ne, leafValue_setupPost_zero s, valueToIndex_setupPost s hFresh 0⟩
    simpa [leafNumber_setupPost] using one_ne_zero_uint
  · refine ⟨[0], rfl, ?len, ?nodup, ?chain, ?mem⟩
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
  · intro i hi hnv
    have hi0 : i = 0 := (occupied_setupPost s i).1 hi
    subst hi0
    exact (hnv (nextValue_setupPost_zero s)).elim
  · refine ⟨0, ?istail, ?uniq⟩
    · exact ⟨(occupied_setupPost s 0).2 rfl,
        nextIndex_setupPost_zero s,
        nextValue_setupPost_zero s⟩
    · intro i hi
      exact (occupied_setupPost s i).1 hi.1
  · intro i hi
    left
    have hi0 : i = 0 := (occupied_setupPost s i).1 hi
    subst hi0
    exact ⟨hi, nextIndex_setupPost_zero s, nextValue_setupPost_zero s⟩
  · intro i hi hne
    have hi0 : i = 0 := (occupied_setupPost s i).1 hi
    exact (hne hi0).elim
  · intro v hv
    have hidx : valueToIndexOf (setupPost s) v = 0 :=
      valueToIndex_setupPost s hFresh v
    constructor
    · intro hne
      exact (hne hidx).elim
    · intro h
      rcases h with ⟨_hocc, hval, _hreach⟩
      have : v = 0 := by
        simpa [hidx, leafValue_setupPost_zero] using hval.symm
      exact (hv this).elim
  · intro i v hi hbetween j hj
    have hi0 : i = 0 := (occupied_setupPost s i).1 hi
    have hj0 : j = 0 := (occupied_setupPost s j).1 hj
    subst hi0; subst hj0
    have hnv0 := nextValue_setupPost_zero s
    have hlv0 := leafValue_setupPost_zero s
    have hLt : (0 : Uint256) < v := by
      simpa [hnv0, hlv0] using hbetween
    intro hEq
    have : v = 0 := by simpa [hlv0] using hEq.symm
    subst this
    have : ¬ (0 : Uint256) < (0 : Uint256) := by
      simp [lt_def, val_zero]
    exact this hLt

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

/-- Computational unfolding of a successful insert. Conclusion is the
    concrete `insertPost` record, not `IMTOrder`. -/
axiom insert_run_of_success
    (value lowHint : Uint256) (s : ContractState)
    (hOk : insert_succeeds value lowHint s) :
    (IndexedMerkleTree.insert value lowHint).run s =
      ContractResult.success (leafNumber s) (insertPost s value lowHint)

/-- Localized pre-state walk fact. Does not mention `insertPost` or any
    post-state `IMTOrder` field. -/
axiom insert_walk_brackets
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    occupied s (insertLow s value lowHint) ∧
    leafValue s (insertLow s value lowHint) < value ∧
    (nextValue s (insertLow s value lowHint) = 0 ∨
      value < nextValue s (insertLow s value lowHint))

/-- Generated-task frame. Unfolding of `insertPost` writes. -/
axiom insert_leaf_frame
    (value lowHint : Uint256) (s s' : ContractState) :
    insert_leaf_frame_spec value lowHint s s'

/-- Residual list-splice reconstruction. Premise includes the localized
    walk fact. Conclusion is full `IMTOrder` on `insertPost`. Named as
    residual because reconstructing `chainCoversOccupied` was not
    discharged. Public wording must remain "verified under documented
    assumptions". -/
axiom insert_splice_from_walk
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s)
    (hWalk : occupied s (insertLow s value lowHint) ∧
      leafValue s (insertLow s value lowHint) < value ∧
      (nextValue s (insertLow s value lowHint) = 0 ∨
        value < nextValue s (insertLow s value lowHint))) :
    IMTOrder (insertPost s value lowHint)

theorem insert_preserves_order
    (value lowHint : Uint256) (s : ContractState) :
    insert_preserves_spec value lowHint s := by
  intro hInv hOk
  have hchar := insert_run_of_success value lowHint s hOk
  have hWalk := insert_walk_brackets value lowHint s hInv hOk
  have _hFrame := insert_leaf_frame value lowHint s
    ((IndexedMerkleTree.insert value lowHint).run s).snd
  rw [hchar]
  exact insert_splice_from_walk value lowHint s hInv hOk hWalk

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
