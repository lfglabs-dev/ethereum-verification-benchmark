import Contracts.Common
import Verity.Stdlib.Math

namespace Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of Matter Labs' Indexed Merkle Tree engine used by
  `L2InteropCommitmentTree` (zkSync Era atomic interop).

  Upstream: matter-labs/era-contracts
  Commit:   e5f6e004a09f667c6109e44c4fe1f81658127631
  Files:    l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol
            l1-contracts/contracts/atomic-interop/L2InteropCommitmentTree.sol

  In scope: `IndexedMerkleTree.setup`, `IndexedMerkleTree.insert`
            (the wrapper only gates the appender, then delegates).

  Out of scope: FullMerkle hashing / `_nodes` / `_zeros` / `_height`,
  `hashLeaf`, `verifyInclusion`, `verifyNonInclusion`, Merkle paths,
  `_reportLeaf`, gas burn, events.

  Storage representation
  ----------------------
  Solidity `struct IMT { FullTree tree; mapping(uint256 => IMTLeaf) leaves;
  mapping(uint256 => uint256) valueToIndex }`. Pinned Verity (`0cb6b59`)
  does provide `MappingStruct(Uint256, [...])` (`Contracts/Smoke/StructMappings.lean`,
  `docs/ROADMAP.md`). This case still stores `IMTLeaf` as three independent
  `Uint256 → Uint256` maps plus scalar `leafNumber`. That is an explicit
  representation / storage-layout scope choice, not a missing primitive and
  not a syntax-only rewrite: EVM packed-struct layout is not reproduced.
  The three list fields remain independently readable and writable, which is
  enough for `IMTOrder`. The recursive walk lives outside `verity_contract`
  and uses `getMappingUint` on those maps.

  Slot layout (purely abstract semantic channels, not EVM or source slots):
    abstract 0  modeled leaf count (source field FullTree._leafNumber,
                Solidity relative slot 1 after `_height`)
    abstract 1  modeled leaves[i].value
    abstract 2  modeled leaves[i].nextIndex
    abstract 3  modeled leaves[i].nextValue
    abstract 4  modeled valueToIndex[v]
  Solidity relative slots on `_imt` at base 0 are `_height` 0, `_leafNumber` 1,
  `_nodes` 2, `_zeros` 3, `leaves` 4, `valueToIndex` 5. This model does not
  reproduce that layout or packed struct offsets. There is no mechanized
  source-to-model storage relation and no bytecode refinement.

  Simplifications
  ---------------
  What was simplified:
  - The Solidity `while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value)`
    walk (`IndexedMerkleTree.sol:90-93`) is a well-founded recursive `Contract`
    helper `walkLowLeaf` with fuel `leafNumber.val`. `walkLowLeafFuel` is the
    pure projection `(walkLowLeaf ...).run s |>.fst` used by specs.
  Why:
  - Pinned Verity (`0cb6b59`) has no first-class `Stmt.while` or `break`
    (`docs/parity/lido.md`, `docs/INTERPRETER_FEATURE_MATRIX.md`). GitHub
    #1623 / PR #1648 fixed `forEach` source semantics; bounded while/break
    remains tracked by open #1724. Classification: Verity ergonomics
    workaround under `IMTOrder`, not a later-landed while feature.
    `insert` runs stateful `walkLowLeaf` before its first write, so the
    helper still sees pre-write storage. Fuel is the current leaf count;
    under `IMTOrder` the chain is finite and `nextValue` strictly increases,
    so the walk terminates before fuel runs out. If fuel hits 0 the helper
    returns the current index (a model artifact that cannot fire under
    the invariant).
  Risk: semantics-preserving under the pre-state invariant.

  What was simplified:
  - `FullMerkle.setup` / `pushNewLeaf` / `updateLeaf` / `hashLeaf` / root
    bytes are omitted. `setup` and `insert` bump `leafNumber` exactly as
    `pushNewLeaf` does (`FullMerkle.sol:43`: `_leafNumber++`) and write
    the leaf records / `valueToIndex`. Root hashes are unmodeled.
  Why:
  - The selected invariant is linked-list order, not Merkle authentication.
    Classification: scope exclusion (proof-gap-only for any later
    `verifyNonInclusion` theorem).
  Risk: none for `IMTOrder`.

  What was simplified:
  - `L2InteropCommitmentTree.insert` appender gate, `_reportLeaf`,
    `_burnLogGas`, and events are omitted.
  Why:
  - List mutation lives entirely in `IndexedMerkleTree.insert`. The
    appender check is a caller-side runtime precondition. The hook and
    gas burn run after the engine writes; a hook revert rolls the
    transaction back, so the success path cannot un-write the list.
    Classification: scope exclusion + runtime precondition.

  What was simplified:
  - `insert` returns only `newIndex`. Solidity returns `(newIndex, newRoot)`.
  Why:
  - `newRoot` is an opaque hash. Classification: syntax-only.

  What was not simplified:
  - Guards, error names, write order (relink predecessor, append leaf,
    `valueToIndex[_value] = newIndex`, then increment `leafNumber` with
    Solidity-0.8 `addPanic` matching `pushNewLeaf`'s checked `++`),
    sentinel `{0,0,0}` at index 0, and the fact that `setup` never writes
    `valueToIndex[0]`.
-/

/-- Fuel-bounded walk matching `IndexedMerkleTree.sol:90-93`.
    Recurses while `nextValue ≠ 0 ∧ nextValue < value`. Slot numbers
    match the flattened layout above. Implemented as a `Contract`
    helper because `verity_contract` cannot bind a recursive helper
    as a do-source. `insert` calls this before its first write. -/
def walkLowLeaf (fuel : Nat) (lowLeafIndex value : Uint256) : Contract Uint256 :=
  match fuel with
  | 0 => Verity.pure lowLeafIndex
  | fuel' + 1 =>
    Verity.bind
      (getMappingUint (⟨3⟩ : StorageSlot (Uint256 → Uint256)) lowLeafIndex)
      fun nextVal =>
        Verity.bind
          (getMappingUint (⟨2⟩ : StorageSlot (Uint256 → Uint256)) lowLeafIndex)
          fun nextIdx =>
            if nextVal != 0 && nextVal < value then
              walkLowLeaf fuel' nextIdx value
            else
              Verity.pure lowLeafIndex
termination_by fuel

/-- Pure projection of the same walk, used by specs/frame theorems. -/
def walkLowLeafFuel (fuel : Nat) (s : ContractState)
    (lowLeafIndex value : Uint256) : Uint256 :=
  (walkLowLeaf fuel lowLeafIndex value).run s |>.fst

verity_contract IndexedMerkleTree where
  storage
    -- abstract channel 0: modeled leaf count (source field FullTree._leafNumber;
    -- Solidity relative slot 1 after `_height`. Not EVM slot 0.)
    leafNumber : Uint256 := slot 0
    -- abstract channel 1: modeled leaves[i].value (Solidity mapping, not slot 1)
    leaves_value : Uint256 → Uint256 := slot 1
    -- abstract channel 2: modeled leaves[i].nextIndex
    leaves_nextIndex : Uint256 → Uint256 := slot 2
    -- abstract channel 3: modeled leaves[i].nextValue
    leaves_nextValue : Uint256 → Uint256 := slot 3
    -- abstract channel 4: modeled valueToIndex[v] (Solidity mapping, not slot 4)
    valueToIndex : Uint256 → Uint256 := slot 4

  -- src: IndexedMerkleTree.setup (lines 46-54)
  -- FullMerkle.setup does not increment `_leafNumber`; pushNewLeaf does,
  -- so a successful setup leaves `leafNumber = 1` with sentinel at 0.
  -- `valueToIndex[0]` is intentionally not written (stays 0).
  function setup () : Unit := do
    let leafNumber_ ← getStorage leafNumber
    require (leafNumber_ == 0) "IMTAlreadyInitialized"
    setMappingUint leaves_value 0 0
    setMappingUint leaves_nextIndex 0 0
    setMappingUint leaves_nextValue 0 0
    setStorage leafNumber 1

/-- `insert` is defined outside `verity_contract` because the macro cannot
    bind a recursive helper (`walkLowLeaf`) as a do-source. Semantics and
    write order still match `IndexedMerkleTree.sol:65-107`. -/
def IndexedMerkleTree.insert (_value _lowLeafIndex : Uint256) : Contract Uint256 := do
  let leafNumber_ ← getStorage IndexedMerkleTree.leafNumber
  require (leafNumber_ != 0) "IMTNotInitialized"
  require (_value != 0) "IMTValueZero"
  let existing ← getMappingUint IndexedMerkleTree.valueToIndex _value
  require (existing == 0) "IMTValueAlreadyExists"
  require (_lowLeafIndex < leafNumber_) "IMTLowLeafIndexOutOfBounds"
  let hintedValue ← getMappingUint IndexedMerkleTree.leaves_value _lowLeafIndex
  require (hintedValue < _value) "IMTLowLeafValueTooLarge"
  let lowLeafIndex ← walkLowLeaf leafNumber_.val _lowLeafIndex _value
  let oldNextIndex ← getMappingUint IndexedMerkleTree.leaves_nextIndex lowLeafIndex
  let oldNextValue ← getMappingUint IndexedMerkleTree.leaves_nextValue lowLeafIndex
  let newIndex := leafNumber_
  setMappingUint IndexedMerkleTree.leaves_nextIndex lowLeafIndex newIndex
  setMappingUint IndexedMerkleTree.leaves_nextValue lowLeafIndex _value
  setMappingUint IndexedMerkleTree.leaves_value newIndex _value
  setMappingUint IndexedMerkleTree.leaves_nextIndex newIndex oldNextIndex
  setMappingUint IndexedMerkleTree.leaves_nextValue newIndex oldNextValue
  setMappingUint IndexedMerkleTree.valueToIndex _value newIndex
  let nextLeafNumber ← addPanic leafNumber_ 1
  setStorage IndexedMerkleTree.leafNumber nextLeafNumber
  return newIndex

end Benchmark.Cases.ZkSync.InteropCommitmentTreeOrder
