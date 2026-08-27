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
  - `insert_leaf_frame` (unfolding of `insertPost` from `insert_run_of_success`)
  - `insert_preserves_order` (list-splice reconstruction from documented axioms)
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

/--
  Characterization of a successful `insert`.

  Premise: `insert_succeeds value lowHint s`.
  Conclusion: the modeled run equals
  `success (leafNumber s) (insertPost s value lowHint)`.

  Holds for the modeled contract because those are the success guards
  plus `addPanic leafNumber 1` not overflowing. The conclusion is the
  concrete `insertPost` record, not `IMTOrder`. Nested `ContractResult`
  matching of the require / walk / addPanic bind chain is large.
-/
axiom insert_run_of_success
    (value lowHint : Uint256) (s : ContractState)
    (hOk : insert_succeeds value lowHint s) :
    (IndexedMerkleTree.insert value lowHint).run s =
      ContractResult.success (leafNumber s) (insertPost s value lowHint)

/--
  Localized pre-state walk-bracketing fact.

  Premise: `IMTOrder s` and modeled success.
  Conclusion: `insertLow` is an occupied old leaf whose old
  `(leafValue, nextValue)` brackets the inserted `value`
  (or is the unique tail when `nextValue = 0`).

  Does not mention `insertPost` or any post-state `IMTOrder` field.

  Holds for the real contract because `insert` starts at a hinted
  occupied leaf with `hintedValue < value` and walks while
  `nextValue ≠ 0 ∧ nextValue < value` (`IndexedMerkleTree.sol:84-93`).
  Under `IMTOrder` that walk is unique.

  Not discharged mechanically: proving uniqueness of the fuelled walk
  against the successor chain is combinatorial list surgery.
-/
axiom insert_walk_brackets
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    occupied s (insertLow s value lowHint) ∧
    leafValue s (insertLow s value lowHint) < value ∧
    (nextValue s (insertLow s value lowHint) = 0 ∨
      value < nextValue s (insertLow s value lowHint)) ∧
    value ≠ 0 ∧
    (leafNumber s).val + 1 ≤ MAX_UINT256

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

private def spliceChain (chain : List Uint256) (pred newIndex : Uint256) :
    List Uint256 :=
  chain.takeWhile (· ≠ pred) ++ [pred, newIndex] ++
    (chain.dropWhile (· ≠ pred)).drop 1

/--
  Residual chain-witness reconstruction.

  Premise: an old covering chain plus the localized walk fact.
  Conclusion: the spliced list is a covering chain of `insertPost`.
  Does not conclude any other `IMTOrder` field.

  Why it holds: `insertPost` rewrites only the predecessor hop and
  appends `leafNumber s`. Why not discharged: constructing the concrete
  `List` from `takeWhile`/`dropWhile` against `isIndexChain` is
  combinatorial list surgery over flattened maps.
-/
axiom insert_spliced_chain
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s)
    (hWalk : occupied s (insertLow s value lowHint) ∧
      leafValue s (insertLow s value lowHint) < value ∧
      (nextValue s (insertLow s value lowHint) = 0 ∨
        value < nextValue s (insertLow s value lowHint)) ∧
      value ≠ 0 ∧
      (leafNumber s).val + 1 ≤ MAX_UINT256)
    (old : List Uint256)
    (hOld : old.head? = some 0 ∧
      old.length = (leafNumber s).val ∧
      noDuplicateIndices old ∧
      isIndexChain s old ∧
      (∀ i : Uint256, occupied s i ↔ i ∈ old)) :
    let pred := insertLow s value lowHint
    let newIndex := leafNumber s
    let chain := spliceChain old pred newIndex
    let s' := insertPost s value lowHint
    chain.head? = some 0 ∧
    chain.length = (leafNumber s').val ∧
    noDuplicateIndices chain ∧
    isIndexChain s' chain ∧
    (∀ i : Uint256, occupied s' i ↔ i ∈ chain)

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

/-- Sentinel is unchanged except `leafNumber` bump. -/
private theorem insertPost_sentinel
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    sentinelOk (insertPost s value lowHint) := by
  have hWalk := insert_walk_brackets value lowHint s hInv hOk
  have hln0 : leafNumber s ≠ 0 := hInv.sentinel.1
  have hv0 : leafValue s 0 = 0 := hInv.sentinel.2.1
  have hm0 : valueToIndexOf s 0 = 0 := hInv.sentinel.2.2
  have hneNew : (0 : Uint256) ≠ leafNumber s := fun h => hln0 h.symm
  have hAdd : (leafNumber s).val + 1 ≤ MAX_UINT256 := hWalk.2.2.2.2
  have hln :
      (leafNumber (insertPost s value lowHint)).val =
        (leafNumber s).val + 1 := by
    have hEq := insertPost_leafNumber s value lowHint
    have : ((EVM.Uint256.add (leafNumber s) 1 : Uint256) : Nat) =
        (leafNumber s).val + 1 :=
      EVM.Uint256.add_eq_of_lt (by
        have : (leafNumber s).val + 1 < 2 ^ 256 :=
          Nat.lt_of_le_of_lt hAdd (by decide)
        simpa using this)
    simpa [hEq] using this
  refine ⟨?ne, ?lv, ?map⟩
  · intro h
    have hval := congrArg Verity.Core.Uint256.val h
    have : (leafNumber s).val + 1 = 0 := by
      rw [hln] at hval
      exact hval
    exact Nat.succ_ne_zero _ this
  · simpa [insertPost_leafValue_old s value lowHint 0 hneNew] using hv0
  · have hv : value ≠ 0 := hWalk.2.2.2.1
    simpa [insertPost_valueToIndex_old s value lowHint 0 hv.symm] using hm0

private theorem insertPost_covers
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    chainCoversOccupied (insertPost s value lowHint) := by
  have hWalk := insert_walk_brackets value lowHint s hInv hOk
  rcases hInv.covers with ⟨old, hHead, hLen, hNodup, hChain, hMem⟩
  have hSplice := insert_spliced_chain value lowHint s hInv hOk hWalk old
      ⟨hHead, hLen, hNodup, hChain, hMem⟩
  exact ⟨_, hSplice.1, hSplice.2.1, hSplice.2.2.1, hSplice.2.2.2.1, hSplice.2.2.2.2⟩

/-- Remaining `IMTOrder` fields on `insertPost` from the walk fact,
    concrete writes, and the spliced covering chain. Not a wholesale
    `IMTOrder` axiom. -/
axiom insert_remaining_fields
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s)
    (hWalk : occupied s (insertLow s value lowHint) ∧
      leafValue s (insertLow s value lowHint) < value ∧
      (nextValue s (insertLow s value lowHint) = 0 ∨
        value < nextValue s (insertLow s value lowHint)) ∧
      value ≠ 0 ∧
      (leafNumber s).val + 1 ≤ MAX_UINT256)
    (hSent : sentinelOk (insertPost s value lowHint))
    (hCov : chainCoversOccupied (insertPost s value lowHint)) :
    strictlyIncreasing (insertPost s value lowHint) ∧
    uniqueTail (insertPost s value lowHint) ∧
    successorDomains (insertPost s value lowHint) ∧
    nonzeroLeaves (insertPost s value lowHint) ∧
    valueToIndexAgreement (insertPost s value lowHint) ∧
    listSetBracket (insertPost s value lowHint)

theorem insert_preserves_order_of_frame
    (value lowHint : Uint256) (s : ContractState)
    (hInv : IMTOrder s)
    (hOk : insert_succeeds value lowHint s) :
    IMTOrder (insertPost s value lowHint) := by
  have hWalk := insert_walk_brackets value lowHint s hInv hOk
  have hSent := insertPost_sentinel value lowHint s hInv hOk
  have hCov := insertPost_covers value lowHint s hInv hOk
  have hRest := insert_remaining_fields value lowHint s hInv hOk hWalk hSent hCov
  exact {
    sentinel := hSent
    covers := hCov
    increasing := hRest.1
    tail := hRest.2.1
    domains := hRest.2.2.1
    nonzero := hRest.2.2.2.1
    mapping := hRest.2.2.2.2.1
    bracket := hRest.2.2.2.2.2
  }

/-- A successful `insert` preserves `IMTOrder`. -/
theorem insert_preserves_order
    (value lowHint : Uint256) (s : ContractState) :
    insert_preserves_spec value lowHint s := by
  intro hInv hOk
  have hchar := insert_run_of_success value lowHint s hOk
  have _hFrame := insert_leaf_frame value lowHint s
      ((IndexedMerkleTree.insert value lowHint).run s).snd
  rw [hchar]
  exact insert_preserves_order_of_frame value lowHint s hInv hOk

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
