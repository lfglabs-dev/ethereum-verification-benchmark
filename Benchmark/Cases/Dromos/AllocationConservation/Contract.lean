-- SPDX-License-Identifier: LicenseRef-Dromos-Restricted-Use-1.0
-- Copyright (c) 2026 Perpetual Cyclist Services LLC
-- Modified source-derived model for development/testing/evaluation only.
-- See cases/dromos/allocation_conservation/{LICENSE,NOTICE}.
import Verity.Core

/-!
Dromos Labs MetaDEX03 root allocation ledger, source revision
0058bd9b1d49b0fb0a6d130dd51886b2c64e3d99.

Explicit simplifications and boundaries:
* This is an executable Verity.Contract ledger projection, not generated Solidity
  bytecode or an exact full-contract success/failure translation. Points, slope
  schedules, emissions, fees, native-value transport, events, access-control
  storage and leaf state are excluded. Their local frame is manually source-audited;
  point/cast/transport failures may reject a source execution admitted here.
* Full-width uint256 keys use Verity's injective symbolic mapChain channel, with
  source base slots 3 (amounts) and 4 (packed TokenState). No hashing axiom is used.
* EnumerableSet logical values use the per-token storageArray channel. Its
  index-plus-one positions use a separate symbolic mapChain channel rooted at 2.
  Add/contains/remove consult positions, removal updates the moved last element,
  and clear deletes each represented position before resetting logical length.
  Stale backing-array cells after unsafeSetLength are not represented: source
  operations cannot read them until overwritten by a later push. This logical
  array abstraction and physical nested-array/keccak layout are not mechanized.
  Source-shaped bookkeeping is executable; representation and amount/support
  validity are separate auxiliary induction obligations, not assumed in operations.
* Stake and authorization view results are explicit inputs. Authentication uses
  the actual Verity sender, and the native transient channel models the shared
  guard. Chain status/registration/gas checks are explicit inputs checked locally.
* Outbound sends are represented by arbitrary finite authenticated deallocation
  callback sequences, after local writes. There is no assumed invariant on an
  injected callback post-state. Full adapter/nonce/ABI execution is excluded.
  Late or repeated partial requests can credit remaining current bookings.
* uint128 arithmetic uses Nat with explicit guards before word conversion.
  TokenState packing follows uint128,uint48,uint48,bool. Every arithmetic result
  in these fields must fit before success. No finite bound is imposed on arrays.
These boundaries need independent modelization/Verity/build approval. No proof
or public claim is asserted by this module.
-/

namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity

set_option maxHeartbeats 1000000

def amountLimit : Nat := 2 ^ 128
def timeLimit : Nat := 2 ^ 48
def CHAIN0 : Uint256 := 0
def TOKEN0 : Uint256 := 0

def amountKey (tokenId chainId : Uint256) : StorageKey :=
  .mapChain 3 [tokenId.val, chainId.val] 0

def tokenKey (tokenId : Uint256) : StorageKey := .mapChain 4 [tokenId.val] 0

def allocationChainAmounts (s : ContractState) (tokenId chainId : Uint256) : Nat :=
  (s.readMapChain 3 [tokenId.val, chainId.val] 0).val

def allocationChainIds (s : ContractState) (tokenId : Uint256) : List Uint256 :=
  s.readArray tokenId.val

-- Symbolic source field channel: allocationChainIds is rooted at source slot 2.
-- Offset 1 names its positions member; this is NOT a physical keccak formula.
def positionKey (tokenId chainId : Uint256) : StorageKey :=
  .mapChain 2 [tokenId.val, chainId.val] 1

def allocationChainPositions (s : ContractState) (tokenId chainId : Uint256) : Nat :=
  (s.readMapChain 2 [tokenId.val, chainId.val] 1).val

structure TokenState where
  committed : Nat
  lastStakeEnd : Nat
  lastAllocated : Nat
  isPermanent : Bool
  deriving Repr, DecidableEq

def tokenStates (s : ContractState) (tokenId : Uint256) : TokenState :=
  let word := (s.readMapChain 4 [tokenId.val] 0).val
  { committed := word % amountLimit
    lastStakeEnd := word / amountLimit % timeLimit
    lastAllocated := word / (amountLimit * timeLimit) % timeLimit
    isPermanent := word / (amountLimit * timeLimit * timeLimit) % 256 != 0 }

def writeWord (key : StorageKey) (value : Nat) : Contract Unit :=
  fun s => .success () (match key with
    | .mapChain slot keys offset => s.writeMapChain slot keys offset (Verity.Core.Uint256.ofNat value)
    | .transient slot => s.writeTransient slot (Verity.Core.Uint256.ofNat value)
    | _ => s.withStorageWords (fun k => if k == key then Verity.Core.Uint256.ofNat value else s.storageWords k))

def writeIds (tokenId : Uint256) (ids : List Uint256) : Contract Unit :=
  fun s => .success () (s.writeArray tokenId.val ids)

def writeTokenState (tokenId : Uint256) (state : TokenState) : Contract Unit := do
  require (state.committed < amountLimit) "CommittedOverflow"
  require (state.lastStakeEnd < timeLimit && state.lastAllocated < timeLimit) "TimestampOverflow"
  writeWord (tokenKey tokenId) (state.committed + amountLimit * state.lastStakeEnd +
    amountLimit * timeLimit * state.lastAllocated +
    amountLimit * timeLimit * timeLimit * (if state.isPermanent then 1 else 0))

def setCommitted (tokenId : Uint256) (value : Nat) : Contract Unit := do
  let old ← (fun s => .success (tokenStates s tokenId) s : Contract TokenState)
  writeTokenState tokenId { old with committed := value }

-- Source-shaped OZ 5.6.1 EnumerableSet operations. No representation
-- invariant is consulted or assumed by any executable operation.
def setContains (tokenId chainId : Uint256) : Contract Bool :=
  fun s => .success (allocationChainPositions s tokenId chainId != 0) s

def setValues (tokenId : Uint256) : Contract (List Uint256) :=
  fun s => .success (allocationChainIds s tokenId) s

def setAdd (tokenId chainId : Uint256) : Contract Bool := do
  let contains ← setContains tokenId chainId
  if contains then return false
  let ids ← setValues tokenId
  require (ids.length + 1 < 2 ^ 256) "SetLengthOverflow"
  writeIds tokenId (ids ++ [chainId])
  writeWord (positionKey tokenId chainId) (ids.length + 1)
  return true

def setRemove (tokenId chainId : Uint256) : Contract Bool := do
  let position ← (fun s => .success (allocationChainPositions s tokenId chainId) s : Contract Nat)
  if position == 0 then return false
  let ids ← setValues tokenId
  require (ids.length > 0 && position ≤ ids.length) "SetIndexOutOfBounds"
  let valueIndex := position - 1
  let lastIndex := ids.length - 1
  if valueIndex != lastIndex then
    let lastValue := ids.getLast!
    writeIds tokenId (ids.set valueIndex lastValue)
    writeWord (positionKey tokenId lastValue) position
  let current ← setValues tokenId
  writeIds tokenId current.dropLast
  writeWord (positionKey tokenId chainId) 0
  return true

def clearPositions (tokenId : Uint256) : List Uint256 → Contract Unit
  | [] => Verity.pure ()
  | c :: rest => do writeWord (positionKey tokenId c) 0; clearPositions tokenId rest

def setClear (tokenId : Uint256) : Contract Unit := do
  let ids ← setValues tokenId
  clearPositions tokenId ids
  writeIds tokenId []

structure Shape where
  stakeEnd : Nat
  isPermanent : Bool
  deriving Repr, DecidableEq

structure Snapshot extends Shape where
  staked : Nat
  deriving Repr

structure AllocationContext where
  oldShape : Shape
  liveShape : Shape
  prevCommitted : Nat

structure ChainAllocation where
  chainId : Uint256
  delta : Nat
  registeredActive : Bool
  hasDestinationGas : Bool
  deriving Repr

structure SourceDelta where
  tokenId : Uint256
  amount : Nat
  deriving Repr

structure DestinationDelta extends SourceDelta where
  liveShape : Shape
  deriving Repr

structure DeallocationReturn where
  originChainId : Uint256
  tokenId : Uint256
  amount : Nat
  registered : Bool
  deriving Repr

structure Environment where
  votingEscrow : Address
  orchestrator : Address
  authorizedForToken : Bool
  snapshot : Snapshot
  chainCallbacks : List DeallocationReturn := []
  gaugeCallbacks : List DeallocationReturn := []

-- Guard slot is a symbolic transient channel, separate from ledger storage.
def guarded (body : Contract Unit) : Contract Unit := do
  let held ← (fun s => .success (s.readTransient 0).val s : Contract Nat)
  require (held == 0) "ReentrancyGuardReentrantCall"
  writeWord (.transient 0) 1
  body
  writeWord (.transient 0) 0

def onlyVotingEscrow (env : Environment) : Contract Unit := do
  let caller ← msgSender
  require (caller == env.votingEscrow) "NotVotingEscrow"

def requireLive (stake : Snapshot) (now : Nat) : Contract Unit := do
  require (stake.staked > 0 && (stake.isPermanent || stake.stakeEnd > now)) "StakeExpired"
  require (stake.staked < amountLimit && stake.stakeEnd < timeLimit) "InputRange"

def _sameShapeContext (shape : Shape) : AllocationContext :=
  { oldShape := shape, liveShape := shape, prevCommitted := 0 }

-- Settlement and contribution swaps are local target-ledger frames. Their
-- excluded signed arithmetic may revert the source, not mutate these fields.
def _settleChain (_chainId : Uint256) : Contract Unit := Verity.pure ()
def _settleChain0AndTotal : Contract Unit := Verity.pure ()
def _refreshEmissionsPerVP : Contract Unit := Verity.pure ()

def _applyChainAllocation (tokenId chainId : Uint256) (newAllocated : Nat)
    (context : AllocationContext) : Contract Unit := do
  let prev ← (fun s => .success (allocationChainAmounts s tokenId chainId) s : Contract Nat)
  if prev == newAllocated && context.oldShape == context.liveShape then return ()
  require (newAllocated < amountLimit) "AllocationOverflow"
  -- _swapContribution on chain and total is outside this ledger projection.
  if newAllocated == 0 then
    writeWord (amountKey tokenId chainId) 0
    let _ ← setRemove tokenId chainId
    Verity.pure ()
  else
    writeWord (amountKey tokenId chainId) newAllocated
    let _ ← setAdd tokenId chainId
    Verity.pure ()

def _reanchorLoop (tokenId : Uint256) (context : AllocationContext) : List Uint256 → Contract Unit
  | [] => Verity.pure ()
  | chainId :: rest => do
      _settleChain chainId
      let value ← (fun s => .success (allocationChainAmounts s tokenId chainId) s : Contract Nat)
      _applyChainAllocation tokenId chainId value context
      _reanchorLoop tokenId context rest

def _reanchor (tokenId : Uint256) (context : AllocationContext) : Contract Unit := do
  let ids ← (fun s => .success (allocationChainIds s tokenId) s : Contract (List Uint256))
  _reanchorLoop tokenId context ids

def _reanchorToLiveShape (tokenId : Uint256) (shape : Shape) : Contract Unit := do
  let old ← (fun s => .success (tokenStates s tokenId) s : Contract TokenState)
  _reanchor tokenId { oldShape := ⟨old.lastStakeEnd, old.isPermanent⟩, liveShape := shape, prevCommitted := 0 }
  writeTokenState tokenId { old with lastStakeEnd := shape.stakeEnd, isPermanent := shape.isPermanent }

def _validateAllocations : List ChainAllocation → Nat → Nat → Contract Nat
  | [], _, total => Verity.pure total
  | a :: rest, previous, total => do
      require (previous < a.chainId.val) "AllocationsNotStrictlyAscending"
      require a.registeredActive "ChainNotActive"
      require a.hasDestinationGas "MissingDestinationGasLimit"
      require (a.delta < amountLimit && total + a.delta < amountLimit) "DeltaOverflow"
      _validateAllocations rest a.chainId.val (total + a.delta)

def _applyChainDeltas (tokenId : Uint256) (context : AllocationContext) : List ChainAllocation → Contract Unit
  | [] => Verity.pure ()
  | a :: rest => do
      let old ← (fun s => .success (allocationChainAmounts s tokenId a.chainId) s : Contract Nat)
      _settleChain a.chainId
      _applyChainAllocation tokenId a.chainId (old + a.delta) context
      _applyChainDeltas tokenId context rest

def _applyAllocation (tokenId : Uint256) (allocations : List ChainAllocation)
    (totalDelta : Nat) (context : AllocationContext) (now : Nat) : Contract Unit := do
  let parked ← (fun s => .success (allocationChainAmounts s tokenId CHAIN0) s : Contract Nat)
  require (totalDelta ≤ parked) "InsufficientChain0Allocation"
  if context.oldShape != context.liveShape then _reanchor tokenId context
  let aligned := { context with oldShape := context.liveShape }
  _applyChainDeltas tokenId aligned allocations
  if totalDelta > 0 then
    _settleChain CHAIN0
    _applyChainAllocation tokenId CHAIN0 (parked - totalDelta) aligned
  _refreshEmissionsPerVP
  writeTokenState tokenId {
    committed := context.prevCommitted
    lastStakeEnd := context.liveShape.stakeEnd
    lastAllocated := now % timeLimit
    isPermanent := context.liveShape.isPermanent }

def prepareChainAllocations (env : Environment) (tokenId : Uint256)
    (allocations : List ChainAllocation) : Contract Unit := do
  let total ← _validateAllocations allocations 0 0
  let now ← (fun s => .success s.blockTimestamp.val s : Contract Nat)
  let prev ← (fun s => .success (tokenStates s tokenId) s : Contract TokenState)
  _applyAllocation tokenId allocations total
    { oldShape := ⟨prev.lastStakeEnd, prev.isPermanent⟩, liveShape := env.snapshot.toShape,
      prevCommitted := prev.committed } now

def _removeChain0Contribution (source : SourceDelta) : Contract Unit := do
  if source.amount == 0 then return ()
  require (source.amount < amountLimit) "InputRange"
  let old ← (fun s => .success (allocationChainAmounts s source.tokenId CHAIN0) s : Contract Nat)
  require (source.amount ≤ old) "InsufficientChain0Allocation"
  let prev ← (fun s => .success (tokenStates s source.tokenId) s : Contract TokenState)
  _applyChainAllocation source.tokenId CHAIN0 (old - source.amount)
    (_sameShapeContext ⟨prev.lastStakeEnd, prev.isPermanent⟩)
  require (source.amount ≤ prev.committed) "CommittedUnderflow"
  setCommitted source.tokenId (prev.committed - source.amount)

def _addChain0Contribution (dest : DestinationDelta) : Contract Unit := do
  if dest.amount == 0 then return ()
  require (dest.amount < amountLimit && dest.liveShape.stakeEnd < timeLimit) "InputRange"
  let ids ← (fun s => .success (allocationChainIds s dest.tokenId) s : Contract (List Uint256))
  let prev ← (fun s => .success (tokenStates s dest.tokenId) s : Contract TokenState)
  require (ids.isEmpty || (prev.lastStakeEnd == dest.liveShape.stakeEnd && prev.isPermanent == dest.liveShape.isPermanent)) "DstShapeStale"
  let old ← (fun s => .success (allocationChainAmounts s dest.tokenId CHAIN0) s : Contract Nat)
  _applyChainAllocation dest.tokenId CHAIN0 (old + dest.amount) (_sameShapeContext dest.liveShape)
  setCommitted dest.tokenId (prev.committed + dest.amount)
  if ids.isEmpty then
    let current ← (fun s => .success (tokenStates s dest.tokenId) s : Contract TokenState)
    writeTokenState dest.tokenId { current with lastStakeEnd := dest.liveShape.stakeEnd, isPermanent := dest.liveShape.isPermanent }

def removeSources : List SourceDelta → Contract Unit
  | [] => Verity.pure ()
  | leg :: rest => do _removeChain0Contribution leg; removeSources rest

def addDestinations : List DestinationDelta → Contract Unit
  | [] => Verity.pure ()
  | leg :: rest => do _addChain0Contribution leg; addDestinations rest

def rebalanceChain0 (env : Environment) (sources : List SourceDelta)
    (destinations : List DestinationDelta) : Contract Unit := guarded do
  onlyVotingEscrow env
  if sources.isEmpty && destinations.isEmpty then return ()
  _settleChain0AndTotal
  removeSources sources
  addDestinations destinations
  _refreshEmissionsPerVP

def applyBurn (amount : Nat) : Contract Unit := do
  require (amount > 0 && amount < amountLimit) "ZeroAmountOrInputRange"
  let prev ← (fun s => .success (tokenStates s TOKEN0) s : Contract TokenState)
  let old ← (fun s => .success (allocationChainAmounts s TOKEN0 CHAIN0) s : Contract Nat)
  require (amount ≤ prev.committed) "InsufficientCommitted"
  require (amount ≤ old) "InsufficientChain0Allocation"
  _settleChain0AndTotal
  setCommitted TOKEN0 (prev.committed - amount)
  writeWord (amountKey TOKEN0 CHAIN0) (old - amount)
  if old - amount == 0 then
    let _ ← setRemove TOKEN0 CHAIN0
    Verity.pure ()
  _refreshEmissionsPerVP

def burn (env : Environment) (amount : Nat) : Contract Unit := guarded do
  onlyVotingEscrow env
  applyBurn amount

def parkOnChain0 (env : Environment) (tokenId : Uint256) : Contract Unit := guarded do
  onlyVotingEscrow env
  let now ← (fun s => .success s.blockTimestamp.val s : Contract Nat)
  requireLive env.snapshot now
  let prev ← (fun s => .success (tokenStates s tokenId) s : Contract TokenState)
  let amount := env.snapshot.staked - prev.committed
  _settleChain0AndTotal
  let ids ← (fun s => .success (allocationChainIds s tokenId) s : Contract (List Uint256))
  if !ids.isEmpty && (prev.lastStakeEnd != env.snapshot.stakeEnd || prev.isPermanent != env.snapshot.isPermanent) then
    _reanchorToLiveShape tokenId env.snapshot.toShape
  _addChain0Contribution { tokenId := tokenId, amount := amount, liveShape := env.snapshot.toShape }
  _refreshEmissionsPerVP

def creditDeallocation (origin tokenId : Uint256) (amount : Nat) : Contract Nat := do
  require (amount < amountLimit) "InputRange"
  let old ← (fun s => .success (allocationChainAmounts s tokenId origin) s : Contract Nat)
  let credit := min amount old
  if credit == 0 then return 0
  _settleChain0AndTotal
  _settleChain origin
  let prev ← (fun s => .success (tokenStates s tokenId) s : Contract TokenState)
  let context := _sameShapeContext ⟨prev.lastStakeEnd, prev.isPermanent⟩
  _applyChainAllocation tokenId origin (old - credit) context
  let parked ← (fun s => .success (allocationChainAmounts s tokenId CHAIN0) s : Contract Nat)
  _applyChainAllocation tokenId CHAIN0 (parked + credit) context
  _refreshEmissionsPerVP
  return credit

def processDeallocation (env : Environment) (r : DeallocationReturn) : Contract Unit := do
  let caller ← msgSender
  require (caller == env.orchestrator) "NotAuthorized"
  require (r.registered && r.originChainId != CHAIN0) "ChainNotRegistered"
  let _ ← creditDeallocation r.originChainId r.tokenId r.amount
  Verity.pure ()

def authenticatedReturn (env : Environment) (r : DeallocationReturn) : Contract Unit :=
  fun s => match processDeallocation env r { s with sender := env.orchestrator } with
    | .success _ next => .success () { next with sender := s.sender }
    | .revert reason _ => .revert reason s

def dispatchReturns (env : Environment) : List DeallocationReturn → Contract Unit
  | [] => Verity.pure ()
  | r :: rest => do authenticatedReturn env r; dispatchReturns env rest

def allocateChains (env : Environment) (tokenId : Uint256)
    (allocations : List ChainAllocation) : Contract Unit := guarded do
  require env.authorizedForToken "NotAuthorized"
  let now ← (fun s => .success s.blockTimestamp.val s : Contract Nat)
  requireLive env.snapshot now
  prepareChainAllocations env tokenId allocations
  if !allocations.isEmpty then dispatchReturns env env.chainCallbacks

-- Gauge checks are represented by a read-only success input; full gauge,
-- settlement and dispatch semantics are explicitly excluded, not trusted proved.
def allocate (env : Environment) (tokenId : Uint256) (allocations : List ChainAllocation)
    (gaugeBatchNonempty gaugeChecksPass : Bool) : Contract Unit := guarded do
  require env.authorizedForToken "NotAuthorized"
  let now ← (fun s => .success s.blockTimestamp.val s : Contract Nat)
  requireLive env.snapshot now
  prepareChainAllocations env tokenId allocations
  require gaugeChecksPass "GaugeValidationFailure"
  if !allocations.isEmpty then dispatchReturns env env.chainCallbacks
  if gaugeBatchNonempty then dispatchReturns env env.gaugeCallbacks

def emergencyDeallocate (env : Environment) (tokenId chainId : Uint256)
    (registeredSuspended allowed gasProvided : Bool) : Contract Unit := guarded do
  require env.authorizedForToken "NotAuthorized"
  require (registeredSuspended && chainId != CHAIN0) "ChainNotSuspended"
  require allowed "EmergencyDeallocationNotAllowed"
  require gasProvided "MissingDestinationGasLimit"
  let amount ← (fun s => .success (allocationChainAmounts s tokenId chainId) s : Contract Nat)
  let credit ← creditDeallocation chainId tokenId amount
  require (credit > 0) "NothingToDeallocate"
  dispatchReturns env env.chainCallbacks

def clearAmounts (tokenId : Uint256) : List Uint256 → Contract Unit
  | [] => Verity.pure ()
  | c :: rest => do writeWord (amountKey tokenId c) 0; clearAmounts tokenId rest

def clearToken (env : Environment) (tokenId : Uint256) : Contract Unit := guarded do
  onlyVotingEscrow env
  require (tokenId != TOKEN0) "Token0NotClearable"
  let ids ← (fun s => .success (allocationChainIds s tokenId) s : Contract (List Uint256))
  clearAmounts tokenId ids
  setClear tokenId
  writeWord (tokenKey tokenId) 0

-- Nonwriters with external sends can execute the same admitted root returns.
-- This is a target-ledger projection, not full implementations of these entries.
def nonwriterWithReturns (env : Environment) (returns : List DeallocationReturn) : Contract Unit :=
  guarded (dispatchReturns env returns)

end Benchmark.Cases.Dromos.AllocationConservation
