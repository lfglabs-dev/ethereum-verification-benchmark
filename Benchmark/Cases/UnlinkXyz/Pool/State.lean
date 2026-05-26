/-
  Verity model of `abstract contract State` — the protocol-state base of
  `UnlinkPool`, holding the merkle root + LazyIMT spine + nullifier set +
  verifier-router reference.

  Upstream: unlink-xyz/monorepo@7617b3eebcf37ab42124fe570eb7e065cf8c8461
  Source:   protocol/contracts/src/lib/State.sol

  Verity's `verity_contract` macro does not support Solidity inheritance,
  so the helper surface is rendered as `namespace State` operating on a
  `StateStorage` record. `UnlinkPool` mirrors the same storage shape with
  nested `StorageStruct` accessors; this module is the trusted-spec source
  of truth for the pure helper behavior.

  Solidity uses ERC-7201 namespaced storage at `STATE_STORAGE_LOCATION`.
  The constant is recorded here verbatim for audit fidelity; pool storage
  uses Verity's macro-level `storage_namespace` ("unlink.storage.State"
  equivalent) for runtime layout.
-/
import Contracts.Common
import Benchmark.Cases.UnlinkXyz.Pool.Specs
import Benchmark.Cases.UnlinkXyz.Pool.InternalLazyIMT

namespace Benchmark.Cases.UnlinkXyz.Pool

open Verity hiding pure bind
open Verity.EVM.Uint256

/-! ### custom:storage-location erc7201:unlink.storage.State

`struct StateStorage { uint256 merkleRoot; LazyIMTData data;
  mapping(uint256 => bool) rootSeen; mapping(uint256 => bool) nullifierHashes;
  address verifierRouter; }` -/

structure StateStorage where
  merkleRoot      : Uint256
  data            : LazyIMTData
  rootSeen        : Nat → Bool
  nullifierHashes : Nat → Bool
  verifierRouter  : Address
  deriving Inhabited

namespace State

/-- `uint256 public constant MAX_TREE_DEPTH = 32;` -/
def MAX_TREE_DEPTH : Uint256 := 32

/-- `bytes32 private constant STATE_STORAGE_LOCATION =
      0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000;` -/
def STATE_STORAGE_LOCATION : Uint256 :=
  0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000

/-! ### Errors -/

def errStateNullifierAlreadySpent : String := "StateNullifierAlreadySpent"
def errStateNullifierOutOfField   : String := "StateNullifierOutOfField"
def errStateAddressIsNull         : String := "StateAddressIsNull"

/-! ### Public getters (read $.fieldName) -/

def nextLeafIndex (st : StateStorage) : Uint256 :=
  st.data.numberOfLeaves

def merkleRoot (st : StateStorage) : Uint256 :=
  st.merkleRoot

def rootSeen (st : StateStorage) (root : Uint256) : Bool :=
  st.rootSeen (root : Nat)

def nullifierHashes (st : StateStorage) (nullifierHash : Uint256) : Bool :=
  st.nullifierHashes (nullifierHash : Nat)

def verifierRouter (st : StateStorage) : Address :=
  st.verifierRouter

/-! ### Internal getters -/

def _getVerifierRouter (st : StateStorage) : Address :=
  st.verifierRouter

def _isRootSeen (st : StateStorage) (root : Uint256) : Bool :=
  st.rootSeen (root : Nat)

/-! ### Internal state mutations -/

/-- `_initializeState()` — initialise the tree and seed the merkleRoot
    with the depth-32 default zero. -/
def _initializeState (st : StateStorage) : Contract StateStorage := do
  let data' ← InternalLazyIMT._init st.data (MAX_TREE_DEPTH : Uint256)
  let z ← InternalLazyIMT._defaultZero (MAX_TREE_DEPTH : Uint256)
  let st' : StateStorage := { st with data := data', merkleRoot := z }
  return { st' with rootSeen := fun n => if n == (z : Nat) then true else st'.rootSeen n }

/-- `_insertLeaves(uint256[] memory _leafHashes)` — append each leaf into
    the LazyIMT spine and recompute the depth-32 root. -/
partial def _insertLeavesLoop
    (st : StateStorage) (leafHashes : Array Uint256) (i : Nat) :
    Contract StateStorage := do
  if i >= leafHashes.size then
    return st
  let leaf := leafHashes[i]!
  let data' ← InternalLazyIMT._insert st.data leaf
  let st' := { st with data := data' }
  _insertLeavesLoop st' leafHashes (i + 1)

def _insertLeaves (st : StateStorage) (leafHashes : Array Uint256) :
    Contract (StateStorage × Uint256) := do
  let count := leafHashes.size
  if count == 0 then
    return (st, st.merkleRoot)
  let st1 ← _insertLeavesLoop st leafHashes 0
  let updatedRoot ← InternalLazyIMT._rootWithDepth st1.data (MAX_TREE_DEPTH : Uint256)
  let st2 : StateStorage :=
    { st1 with
      rootSeen := fun n => if n == (updatedRoot : Nat) then true else st1.rootSeen n
      merkleRoot := updatedRoot }
  return (st2, updatedRoot)

/-- `_spend(uint256 _nullifierHash)` — bind a nullifier on the spent-set
    and reject duplicate or out-of-field values. -/
def _spend (st : StateStorage) (nullifierHash : Uint256) :
    Contract StateStorage := do
  if (nullifierHash : Nat) >= (PoolConstants.SNARK_SCALAR_FIELD : Nat) then
    require false errStateNullifierOutOfField
  if st.nullifierHashes (nullifierHash : Nat) then
    require false errStateNullifierAlreadySpent
  return { st with
    nullifierHashes :=
      fun n => if n == (nullifierHash : Nat) then true else st.nullifierHashes n }

/-- `_setVerifierRouter(address _verifierRouter)` — replace the router
    address, rejecting the zero address. -/
def _setVerifierRouter (st : StateStorage) (router : Address) :
    Contract StateStorage := do
  if (router.toNat == 0) then
    require false errStateAddressIsNull
  return { st with verifierRouter := router }

/-! ### Concrete helper semantics used by the formal-audit bridge layer -/

/-- Successful `_spend` marks exactly the requested fresh, in-field
    nullifier and leaves the rest of the nullifier map unchanged. -/
theorem spend_success_of_fresh_in_field
    (st : StateStorage) (nullifierHash : Uint256) (cs : ContractState)
    (hBound :
      ¬ (nullifierHash : Nat) >= (PoolConstants.SNARK_SCALAR_FIELD : Nat))
    (hFresh : st.nullifierHashes (nullifierHash : Nat) = false) :
    State._spend st nullifierHash cs =
      ContractResult.success
        { st with
          nullifierHashes :=
            fun n => if n == (nullifierHash : Nat) then true else st.nullifierHashes n }
        cs := by
  unfold State._spend
  simp [hBound, hFresh, Verity.instMonadContract, Verity.bind, Verity.pure]

/-- Empty `_insertLeaves` is a concrete no-op: it returns the original storage
    and current root without touching the EVM contract state. -/
theorem insert_leaves_empty_success
    (st : StateStorage) (cs : ContractState) :
    State._insertLeaves st #[] cs =
      ContractResult.success (st, st.merkleRoot) cs := by
  unfold State._insertLeaves
  simp [Verity.instMonadContract, Verity.pure]

end State

end Benchmark.Cases.UnlinkXyz.Pool
