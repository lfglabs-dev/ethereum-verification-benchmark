import Verity.Specs.Common
import Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder.Contract

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity
open Verity.EVM.Uint256

/-
  Specifications for the zkSync Era IMT linked-list order invariant.

  Physical array indices are append order, not sorted order. Ordering is
  the linked-list relation: following `nextIndex` from sentinel 0 visits
  strictly increasing `value`s. See IndexedMerkleTree.t.sol:116-135
  (insert 10, 20, 15 at indices 1, 2, 3; traversal 0 -> 10 -> 15 -> 20).

  The public invariant is one concrete chain witness. It is not a bundle
  of independent post-state fields. Unique tail, successor domain,
  absence bracketing, and nonzero non-sentinel leaves are intended
  corollaries of that witness plus `leafValue 0 = 0`. `valueToIndex`
  agreement is a separate map fact, not part of the central theorem.

  Abstract semantic channels (not EVM / source slots; no bytecode refinement):
    channel 0: modeled leaf count (source FullTree._leafNumber, relative slot 1)
    channel 1: modeled leaves[i].value
    channel 2: modeled leaves[i].nextIndex
    channel 3: modeled leaves[i].nextValue
    channel 4: modeled valueToIndex[v]
-/

def leafNumber (s : ContractState) : Uint256 := s.storage 0

def leafValue (s : ContractState) (i : Uint256) : Uint256 :=
  s.storageMapUint 1 i

def nextIndex (s : ContractState) (i : Uint256) : Uint256 :=
  s.storageMapUint 2 i

def nextValue (s : ContractState) (i : Uint256) : Uint256 :=
  s.storageMapUint 3 i

def valueToIndexOf (s : ContractState) (v : Uint256) : Uint256 :=
  s.storageMapUint 4 v

/-- A list of leaf indices forms a valid chain: each element's `nextIndex`
    is the following index, and `nextValue` agrees with the successor's
    `value`. A singleton is always a chain. -/
def isIndexChain (s : ContractState) : List Uint256 → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      nextIndex s a = b ∧
      nextValue s a = leafValue s b ∧
      isIndexChain s (b :: rest)

/-- Strict increase of stored leaf values along consecutive chain hops.
    Distinct from physical append order of array indices. -/
def chainValuesIncrease (s : ContractState) : List Uint256 → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      leafValue s a < leafValue s b ∧
      chainValuesIncrease s (b :: rest)

/-- Reachability of index `b` from index `a` via a concrete witness chain. -/
def reachableIndex (s : ContractState) (a b : Uint256) : Prop :=
  ∃ chain : List Uint256,
    chain.head? = some a ∧
    chain.getLast? = some b ∧
    isIndexChain s chain

def noDuplicateIndices : List Uint256 → Prop
  | [] => True
  | a :: rest => a ∉ rest ∧ noDuplicateIndices rest

/-- Occupied indices are `0 ≤ i < leafNumber`. -/
def occupied (s : ContractState) (i : Uint256) : Prop :=
  i < leafNumber s

def isTail (s : ContractState) (i : Uint256) : Prop :=
  occupied s i ∧ nextIndex s i = 0 ∧ nextValue s i = 0

def isNonTail (s : ContractState) (i : Uint256) : Prop :=
  occupied s i ∧
  0 < nextIndex s i ∧
  nextIndex s i < leafNumber s ∧
  nextValue s i = leafValue s (nextIndex s i)

/-- Sentinel leaf value is 0 at index 0. Non-emptiness of the list is
    implied by a covering chain whose head is 0. -/
def sentinelValueOk (s : ContractState) : Prop :=
  leafValue s 0 = 0

/-- One covering ordered chain: starts at sentinel 0, visits every occupied
    index exactly once, follows `nextIndex` / `nextValue` on internal hops,
    ends at the unique tail (`nextIndex = nextValue = 0`), and has strictly
    increasing leaf values along each hop. -/
def isCoveringOrderedChain (s : ContractState) (chain : List Uint256) : Prop :=
  chain.head? = some 0 ∧
  chain.length = (leafNumber s).val ∧
  noDuplicateIndices chain ∧
  isIndexChain s chain ∧
  (∀ i : Uint256, occupied s i ↔ i ∈ chain) ∧
  chainValuesIncrease s chain ∧
  (∀ t : Uint256, chain.getLast? = some t → nextIndex s t = 0 ∧ nextValue s t = 0)

def coveringOrderedChain (s : ContractState) : Prop :=
  ∃ chain : List Uint256, isCoveringOrderedChain s chain

/-- Combined linked-list order invariant: sentinel value 0 together with
    one covering ordered chain. This is the public theorem target. -/
structure IMTOrder (s : ContractState) : Prop where
  sentinelValue : sentinelValueOk s
  covering : coveringOrderedChain s

/-!
  Intended corollaries of `IMTOrder`, not extra public theorem fields.
  They may be proved later; they are not assumed in `insert_preserves_order`.
-/

/-- Strict increase along every non-tail hop. Corollary of chain increase
    plus `isIndexChain` (`nextValue` agrees with the successor value). -/
def strictlyIncreasing (s : ContractState) : Prop :=
  ∀ i : Uint256, occupied s i → nextValue s i ≠ 0 →
    leafValue s i < nextValue s i

/-- Unique tail: exactly one occupied leaf has nextIndex = 0 and nextValue = 0.
    Corollary: the last element of the covering chain. -/
def uniqueTail (s : ContractState) : Prop :=
  ∃ t : Uint256, isTail s t ∧
    ∀ i : Uint256, isTail s i → i = t

/-- Nonzero: every occupied non-sentinel leaf has value ≠ 0.
    Corollary of `leafValue 0 = 0` plus strict increase along the chain. -/
def nonzeroLeaves (s : ContractState) : Prop :=
  ∀ i : Uint256, occupied s i → i ≠ 0 → leafValue s i ≠ 0

/-- For v ≠ 0, valueToIndex[v] = i > 0 iff i is occupied, holds that value,
    and is reachable from sentinel 0. Separate map fact; not in `IMTOrder`. -/
def valueToIndexAgreement (s : ContractState) : Prop :=
  ∀ v : Uint256, v ≠ 0 →
    let i := valueToIndexOf s v
    (i ≠ 0 ↔ (occupied s i ∧ leafValue s i = v ∧ reachableIndex s 0 i))

/-- Absence from the modeled linked-list value set (not Merkle-authenticated
    non-inclusion). Corollary of a covering strictly increasing chain. -/
def listSetBracket (s : ContractState) : Prop :=
  ∀ i v : Uint256, occupied s i →
    (if nextValue s i = 0 then leafValue s i < v
     else leafValue s i < v ∧ v < nextValue s i) →
    ∀ j : Uint256, occupied s j → leafValue s j ≠ v

/-- Successor/tail domain: every occupied leaf is either the unique tail
    or a non-tail with in-range nextIndex. Corollary of the covering chain. -/
def successorDomains (s : ContractState) : Prop :=
  ∀ i : Uint256, occupied s i → isTail s i ∨ isNonTail s i

/-- Deployment-default / fresh-zero mappings. `setup` does not clear dirty
    `valueToIndex` or unoccupied leaf cells. -/
def freshZeroStorage (s : ContractState) : Prop :=
  leafNumber s = 0 ∧
  (∀ i : Uint256, leafValue s i = 0 ∧ nextIndex s i = 0 ∧ nextValue s i = 0) ∧
  (∀ v : Uint256, valueToIndexOf s v = 0)

/-- `setup` establishes `IMTOrder` from fresh-zero storage. -/
def setup_establishes_spec (s s' : ContractState) : Prop :=
  freshZeroStorage s →
  ((IndexedMerkleTree.setup.run s).snd = s') →
  IMTOrder s'

def insert_succeeds (value lowHint : Uint256) (s : ContractState) : Prop :=
  match (IndexedMerkleTree.insert value lowHint).run s with
  | .success _ _ => True
  | .revert _ _ => False

/-- The inserted value is absent from stored leaf values. Required as an
    explicit premise for order preservation: without it, inserting a value
    equal to an existing leaf value would break strict increase along the
    chain. The `valueToIndex == 0` guard only implies this when the map
    agrees with stored values, which `IMTOrder` deliberately does not
    assume. -/
def valueNotStored (s : ContractState) (v : Uint256) : Prop :=
  ∀ j : Uint256, occupied s j → leafValue s j ≠ v

/-- Successful `insert` preserves `IMTOrder`. -/
def insert_preserves_spec
    (value lowHint : Uint256) (s : ContractState) : Prop :=
  IMTOrder s →
  insert_succeeds value lowHint s →
  valueNotStored s value →
  IMTOrder ((IndexedMerkleTree.insert value lowHint).run s).snd

/-- Leaf-record frame of a successful insert: occupied values at indices
    `< old leafNumber` are unchanged; the only leaf-record mutation is the
    predecessor's `(nextIndex, nextValue)` and the write at `old leafNumber`. -/
def insert_leaf_frame_spec
    (value lowHint : Uint256) (s s' : ContractState) : Prop :=
  let r := (IndexedMerkleTree.insert value lowHint).run s
  match r with
  | .revert _ _ => True
  | .success newIndex sPost =>
      sPost = s' →
      (∀ i : Uint256, i < leafNumber s →
        leafValue s' i = leafValue s i) ∧
      (∀ i : Uint256, i < leafNumber s → i ≠ walkLowLeafFuel (leafNumber s).val s lowHint value →
        nextIndex s' i = nextIndex s i ∧
        nextValue s' i = nextValue s i) ∧
      leafValue s' newIndex = value ∧
      newIndex = leafNumber s ∧
      leafNumber s' = add (leafNumber s) 1 ∧
      valueToIndexOf s' value = newIndex ∧
      (∀ v : Uint256, v ≠ value → valueToIndexOf s' v = valueToIndexOf s v)

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
