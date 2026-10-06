/-
Executable source-structured model of the pinned QueryRedeemQueue.sol (SHA-256
6fb63f25a4af6a64e287291f7a664f265c2b90efe521990e1ccd444a295ab0de).

Simplifications and applicability boundaries (none impose conservation):
* ERC-7201 storage words and Solidity's dynamic-array encoding are represented by
  Lean arrays of the same records. Indexes remain 1-based at the public boundary.
  This is NOT a bytecode or storage-slot refinement proof.
* All Solidity uint256 operands are natural numbers with explicit checks at every
  successful arithmetic/array-length boundary. Math.mulDiv uses an unbounded
  intermediate product, floors the quotient and reverts when the quotient cannot
  fit a word. There is no bound on ghost totals, operation count or array length
  other than individual successful Solidity uint256 operations.
* SafeERC20 call sites are emitted, in source order, as external-call boundaries;
  a failed call reverts its enclosing transaction. Token balances, approvals, code
  execution, returndata and economically delivered token amounts are not modeled.
  The property is about NOMINAL amounts, not balances or actual received tokens.
  The finite recursive schedule permits arbitrary nesting and list lengths, with
  callbacks at each emitted transfer site and rollback scoped to each invocation.
  The entrypoints do NOT have nonReentrant. There is no callback inside the redeem
  loop: its sole transfer follows all demand writes. No queue accounting write
  follows an emitted transfer, so its published state is available to callbacks.
  This is a storage projection, NOT a mechanized nested-EVM callback refinement.
  Return values are discarded: `remainingShares` is read AFTER redeem's transfer
  and can reflect a callback redeeming the same demand, unlike a pre-call result.
* Initialization checks address/code existence and decimals as supplied external
  observations. IVehicle inherits IERC20Metadata whose `decimals()` is external
  view, as is the explicit IERC20Metadata call; Solidity uses STATICCALL, under
  which a state-changing nested queue invocation cannot succeed. The model takes
  their read-only result/revert as supplied observations rather than modeling
  read-only observations. The Interceptor setup, guard initialization, proxy/beacon wiring,
  emitted Solidity logs, gas/OOG and ABI error payloads are outside the nominal
  accounting projection. No state can be changed through those omitted facilities
  in this model. Caller authorization on queue entrypoints IS preserved.
* `encodeVerity`/`decodeVerity` provide an executable Verity.ContractState/Contract
  connection using synthetic proof-only lanes. This is not a `verity_contract`
  EDSL translation, ERC-7201 storage refinement or generated-Yul equivalence;
  arbitrary hand-crafted Verity states need not decode to reachable queue states.
* Ghost redemption records append the actual overlap, fulfillment ID and nominal
  payout calculated by each successful loop iteration. They do not guard any
  execution, consume any uint256 budget or enforce the desired invariant.
* The library's interpreter for `forEach` is not an executable counted loop
  (`Contracts.Common.forEach` evaluates its body once); this model instead uses
  an explicit 32-step fold over the SOURCE loop body. No loop axiom is used.
-/
import Contracts.Common

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Source words, represented without wraparound; every successful write is checked. -/
abbrev Word := Nat

def maxWord : Nat := 2 ^ 256 - 1

def checkedWord (n : Nat) : Except String Word :=
  if n ≤ maxWord then .ok n else .error "Panic(0x11): uint256 overflow"

def checkedAdd (a b : Word) : Except String Word := checkedWord (a + b)

def checkedSub (a b : Word) : Except String Word :=
  if b ≤ a then .ok (a - b) else .error "Panic(0x11): uint256 underflow"

/-- OpenZeppelin Math.mulDiv(x,y,denominator,Floor): 512-bit product, word quotient. -/
def mulDivFloor (x y denominator : Word) : Except String Word :=
  if denominator = 0 then .error "Math: division by zero"
  else checkedWord ((x * y) / denominator)

structure Demand where
  position : Word
  amountIn : Word
  maxAmountOut : Word
  highestFulfillmentId : Word
  deriving Repr, BEq, Inhabited

structure Fulfillment where
  position : Word
  filledAmountIn : Word
  amountOut : Word
  deriving Repr, BEq, Inhabited

/-- Ghost event: never consulted by demand/fulfill/redeem/resolve/retrieve. -/
structure Allocation where
  demandId : Word
  fulfillmentId : Word
  start : Word
  length : Word
  nominalPayout : Word
  deriving Repr, BEq, Inhabited

structure QueueState where
  initialized : Bool := false
  selfAddress : Nat := 0x387d9d519ad7a0147f27ba460fbc1323d6846f77
  multiVehicle : Nat := 0
  manager : Nat := 0
  assetIn : Nat := 0
  assetOut : Nat := 0
  retrievable : Word := 0
  demands : Array Demand := #[]
  fulfillments : Array Fulfillment := #[]
  allocations : Array Allocation := #[]
  deriving Repr, Inhabited

/-- Exact point where an ERC20/IVehicle call can execute/reenter. -/
inductive ExternalCall where
  | transferFrom (token fromAddr toAddr : Nat) (amount : Word)
  | transfer (token toAddr : Nat) (amount : Word)
  deriving Repr, BEq

/-- Reversion restores pre-call state, including every nested successful callback. -/
def attempt (s : QueueState) (r : Except String (QueueState × Array ExternalCall))
    (allTokenCallsSucceed : Bool := true) : QueueState :=
  match r with
  | .ok (post, _) => if allTokenCallsSucceed then post else s
  | .error _ => s

def checkInitialized (s : QueueState) : Except String Unit :=
  if s.initialized then .ok () else .error "not initialized"

def onlyMultiVehicle (s : QueueState) (caller : Nat) : Except String Unit :=
  if caller = s.multiVehicle then .ok () else .error "Unauthorized"

def onlyMultiVehicleOrManager (s : QueueState) (caller : Nat) : Except String Unit :=
  if caller = s.multiVehicle || caller = s.manager then .ok () else .error "OnlyMultiVehicleOrManager"

def onlyManager (s : QueueState) (caller : Nat) : Except String Unit :=
  if caller = s.manager then .ok () else .error "Unauthorized"

def checkValue (n : Word) : Except String Unit :=
  if n > 0 then .ok () else .error "ZeroValue"

def _idToIdx (id : Word) : Except String Nat := checkedSub id 1

def _idxToId (idx : Nat) : Except String Word := checkedAdd idx 1

def _isValidDemandId (s : QueueState) (id : Word) : Bool :=
  id > 0 && id ≤ s.demands.size

def _isFullyRedeemed (s : QueueState) (id : Word) : Bool :=
  (s.demands[id - 1]!).amountIn = 0

def validDemand (s : QueueState) (id : Word) : Except String Demand := do
  if !_isValidDemandId s id then throw "InvalidDemandId"
  return s.demands[id - 1]!

def validFulfillment (s : QueueState) (id : Word) : Except String Fulfillment := do
  if !(id > 0 && id ≤ s.fulfillments.size) then throw "InvalidFulfillmentId"
  return s.fulfillments[id - 1]!

/-- `initialize` / `__QueryRedeemQueue_init`: caller is permissionless exactly once.
    `hasCode*` and decimals are observations from external dependencies. -/
def «initialize» (s : QueueState) (parent manager assetIn assetOut : Nat)
    (hasCodeIn hasCodeOut : Bool) (decimalsIn decimalsOut : Nat) :
    Except String (QueueState × Array ExternalCall) := do
  if s.initialized then throw "InvalidInitialization"
  if parent = 0 || manager = 0 then throw "ZeroAddress"
  if assetIn = 0 || assetOut = 0 then throw "ZeroAddress"
  if parent ≥ 2 ^ 160 || manager ≥ 2 ^ 160 ||
     assetIn ≥ 2 ^ 160 || assetOut ≥ 2 ^ 160 then
    throw "not an EVM address"
  if !hasCodeIn || !hasCodeOut then throw "ZeroCode"
  if decimalsIn > 18 || decimalsOut > 18 then throw "UnsupportedAsset"
  let s' : QueueState := { s with initialized := true, multiVehicle := parent, manager := manager, assetIn := assetIn, assetOut := assetOut }
  return (s', #[])

/-- `demand`: check both amounts, append at the previous demand's immutable end,
    publish demand before calling assetIn.safeTransferFrom. -/
def demand (s : QueueState) (caller : Nat) (amountIn maxAmountOut : Word) :
    Except String (QueueState × Array ExternalCall) := do
  checkInitialized s
  onlyMultiVehicle s caller
  checkValue amountIn
  checkValue maxAmountOut
  let _ ← checkedWord amountIn
  let _ ← checkedWord maxAmountOut
  let _demandId ← _idxToId s.demands.size
  let position ← if s.demands.isEmpty then pure 0 else
    checkedAdd s.demands.back!.position s.demands.back!.amountIn
  let highestFulfillmentId := if s.fulfillments.isEmpty then 1 else s.fulfillments.size
  let _ ← checkedWord highestFulfillmentId
  let d : Demand := ⟨position, amountIn, maxAmountOut, highestFulfillmentId⟩
  let s' := { s with demands := s.demands.push d }
  return (s', #[.transferFrom s.assetIn caller s.selfAddress amountIn])

/-- `fulfill`: publish immutable interval and amountOut before TWO token calls. -/
def fulfill (s : QueueState) (caller : Nat) (amountInFilled amountOutProvided : Word) :
    Except String (QueueState × Array ExternalCall) := do
  checkInitialized s
  onlyMultiVehicleOrManager s caller
  checkValue amountInFilled
  checkValue amountOutProvided
  let _ ← checkedWord amountInFilled
  let _ ← checkedWord amountOutProvided
  let _fulfillmentId ← _idxToId s.fulfillments.size
  let position ← if s.fulfillments.isEmpty then pure 0 else
    checkedAdd s.fulfillments.back!.position s.fulfillments.back!.filledAmountIn
  let f : Fulfillment := ⟨position, amountInFilled, amountOutProvided⟩
  let s' := { s with fulfillments := s.fulfillments.push f }
  return (s', #[.transferFrom s.assetOut caller s.selfAddress amountOutProvided,
                 .transfer s.assetIn caller amountInFilled])

/-- `_isMatchingFulfillment`: the checked endpoint matters even for comparisons. -/
def _isMatchingFulfillment (position : Word) (f : Fulfillment) : Except String Bool := do
  let endpoint ← checkedAdd f.position f.filledAmountIn
  return position ≥ f.position && position < endpoint

/-- `_redeemable`: source checks only the height, NOT the search hint. -/
def _redeemable (s : QueueState) (id : Word) : Except String Bool := do
  if s.fulfillments.isEmpty then return false
  let d ← validDemand s id
  let last := s.fulfillments.back!
  let endPosition ← checkedAdd last.position last.filledAmountIn
  return d.position < endPosition

/-- Source binary lookup, including window, two fast paths and lower-bound search.
    Fuel strictly decreases with the window; no accounting premise is inserted. -/
def _lookupLoop (s : QueueState) (position : Word) (lo hi fuel : Nat) :
    Except String Word :=
  match fuel with
  | 0 => .error "lookup fuel exhausted (unreachable for checked window)"
  | fuel + 1 => do
    if lo ≥ hi then
      let f ← validFulfillment s (lo + 1)
      if ← _isMatchingFulfillment position f then _idxToId lo else pure 0
    else
      let mid ← checkedAdd lo hi
      let mid := mid / 2
      let f ← validFulfillment s (mid + 1)
      let endpoint ← checkedAdd f.position f.filledAmountIn
      if position ≥ endpoint then _lookupLoop s position (mid + 1) hi fuel
      else _lookupLoop s position lo mid fuel
termination_by fuel

def _lookupFulfillment (s : QueueState) (position startId endId : Word) :
    Except String Word := do
  if startId > endId then return 0
  let lo ← _idToIdx startId
  let hi ← _idToIdx endId
  let flo ← validFulfillment s startId
  if ← _isMatchingFulfillment position flo then return startId
  let fhi ← validFulfillment s endId
  if ← _isMatchingFulfillment position fhi then return endId
  _lookupLoop s position lo hi (hi - lo + 1)

/-- `resolve` is permissionless and only changes the demand search hint. -/
def resolve (s : QueueState) (demandId fulfillmentId : Word) :
    Except String (QueueState × Array ExternalCall) := do
  checkInitialized s
  let d ← validDemand s demandId
  if d.amountIn = 0 then throw "DemandIdAlreadyRedeemed"
  let f ← validFulfillment s fulfillmentId
  if !(← _isMatchingFulfillment d.position f) then throw "FulfillmentNotMatchingDemand"
  if d.highestFulfillmentId = fulfillmentId then throw "UnchangedDemand"
  let d' := { d with highestFulfillmentId := fulfillmentId }
  return ({ s with demands := s.demands.set! (demandId - 1) d' }, #[])

/-- Source loop-carried values. `stop` encodes `break`, not a trace bound. -/
structure RedeemCursor where
  state : QueueState
  fulfillmentId : Word
  redeemedAmount : Word := 0
  stop : Bool := false
  deriving Inhabited

/-- One literal source loop iteration. No token callback can run here. -/
def _redeemOne (demandId fulfillmentLength : Word) (c : RedeemCursor) :
    Except String RedeemCursor := do
  if c.stop || c.fulfillmentId > fulfillmentLength then return { c with stop := true }
  let f ← validFulfillment c.state c.fulfillmentId
  let d ← validDemand c.state demandId
  if !(← _isMatchingFulfillment d.position f) then return { c with stop := true }
  let dEnd ← checkedAdd d.position d.amountIn
  let fEnd ← checkedAdd f.position f.filledAmountIn
  let start := max d.position f.position
  let endpoint := min dEnd fEnd
  let overlap ← checkedSub endpoint start
  let demandAssets ← mulDivFloor overlap d.maxAmountOut d.amountIn
  let fulfillmentAssets ← mulDivFloor overlap f.amountOut f.filledAmountIn
  let payout := min demandAssets fulfillmentAssets
  let redeemedAmount ← checkedAdd c.redeemedAmount payout
  let newPosition ← checkedAdd d.position overlap
  let newAmountIn ← checkedSub d.amountIn overlap
  let newMaxAmountOut ← checkedSub d.maxAmountOut payout
  let nextFulfillmentId ← checkedAdd c.fulfillmentId 1
  let d' : Demand := ⟨newPosition, newAmountIn, newMaxAmountOut, nextFulfillmentId⟩
  let a : Allocation := ⟨demandId, c.fulfillmentId, d.position, overlap, payout⟩
  let mut state := { c.state with
    demands := c.state.demands.set! (demandId - 1) d',
    allocations := c.state.allocations.push a }
  -- Even if there is no excess, the source evaluates demandAssets + 1.
  let threshold ← checkedAdd demandAssets 1
  if fulfillmentAssets > threshold then
    let excess ← checkedSub fulfillmentAssets threshold
    let updated ← checkedAdd state.retrievable excess
    state := { state with retrievable := updated }
  return ⟨state, nextFulfillmentId, redeemedAmount, newAmountIn = 0⟩

/-- `_redeemDemandWithFulfillments`: explicit 32 repetitions PER CALL.
    A later redeem call can execute another 32; trace length is unrestricted. -/
def _redeemDemandWithFulfillments (s : QueueState) (demandId firstId : Word) :
    Except String (QueueState × Word) := do
  let initial : RedeemCursor := ⟨s, firstId, 0, false⟩
  let cursor ← (List.range 32).foldlM
    (fun c _ => _redeemOne demandId s.fulfillments.size c) initial
  return (cursor.state, cursor.redeemedAmount)

/-- `redeem`: caller guard, ID/empty/height checks, source lookup and 32-loop.
    The only token call is after all writes; transfer amount can be zero. -/
def redeem (s : QueueState) (caller : Nat) (demandId : Word) :
    Except String (QueueState × Array ExternalCall) := do
  checkInitialized s
  onlyMultiVehicle s caller
  let d ← validDemand s demandId
  if d.amountIn = 0 then throw "DemandIdAlreadyRedeemed"
  if !(← _redeemable s demandId) then throw "UnredeemableDemand"
  let firstId ← _lookupFulfillment s d.position d.highestFulfillmentId s.fulfillments.size
  let (s', redeemedAmount) ← _redeemDemandWithFulfillments s demandId firstId
  return (s', #[.transfer s.assetOut caller redeemedAmount])

/-- `retrieve`: decrease excess before manager token transfer, not a redemption. -/
def retrieve (s : QueueState) (caller : Nat) (amount : Word) :
    Except String (QueueState × Array ExternalCall) := do
  checkInitialized s
  onlyManager s caller
  checkValue amount
  let _ ← checkedWord amount
  if amount > s.retrievable then throw "InvalidValue"
  let newRetrievable ← checkedSub s.retrievable amount
  return ({ s with retrievable := newRetrievable },
    #[.transfer s.assetOut caller amount])

/-- Views: same checks, no state updates. `unredeemable` can underflow/revert. -/
def redeemable (s : QueueState) (id : Word) : Except String Bool := do
  let d ← validDemand s id
  if d.amountIn = 0 then return false
  _redeemable s id

def pending (s : QueueState) (id : Word) : Except String Word := do
  return (← validDemand s id).amountIn

def demandFromId := validDemand

def fulfillmentFromId := validFulfillment

def demandsCount (s : QueueState) : Nat := s.demands.size

def fulfillmentsCount (s : QueueState) : Nat := s.fulfillments.size

def retrievable (s : QueueState) : Word := s.retrievable

def multiVehicle (s : QueueState) : Nat := s.multiVehicle

def assetIn (s : QueueState) : Nat := s.assetIn

def assetOut (s : QueueState) : Nat := s.assetOut

def lookup (s : QueueState) (id : Word) : Except String Word := do
  let d ← validDemand s id
  if d.amountIn = 0 || s.fulfillments.isEmpty then return 0
  _lookupFulfillment s d.position d.highestFulfillmentId s.fulfillments.size

def unredeemable (s : QueueState) : Except String Word := do
  if s.demands.isEmpty then return 0
  let demandHeight ← checkedAdd s.demands.back!.position s.demands.back!.amountIn
  let fulfillmentHeight ← if s.fulfillments.isEmpty then pure 0 else
    checkedAdd s.fulfillments.back!.position s.fulfillments.back!.filledAmountIn
  checkedSub demandHeight fulfillmentHeight

/-- All queue entrypoints, including read-only calls and repeat initialization.
    View returns are discarded by the state-transition trace, but their source
    revert checks run. `resolve` remains permissionless. -/
inductive QueueOperation where
  | «initialize» (parent manager assetIn assetOut : Nat)
      (hasCodeIn hasCodeOut : Bool) (decimalsIn decimalsOut : Nat)
  | demand (caller amountIn maxAmountOut : Nat)
  | fulfill (caller filledAmountIn amountOutProvided : Nat)
  | redeem (caller demandId : Nat)
  | resolve (demandId fulfillmentId : Nat)
  | retrieve (caller amount : Nat)
  | redeemable (demandId : Nat)
  | pending (demandId : Nat)
  | demandFromId (demandId : Nat)
  | fulfillmentFromId (fulfillmentId : Nat)
  | lookup (demandId : Nat)
  | unredeemable
  | demandsCount
  | fulfillmentsCount
  | retrievable
  | multiVehicle
  | assetIn
  | assetOut
  deriving Repr

def execute (s : QueueState) : QueueOperation → Except String (QueueState × Array ExternalCall)
  | .«initialize» parent manager assetIn assetOut hasCodeIn hasCodeOut decimalsIn decimalsOut =>
      «initialize» s parent manager assetIn assetOut hasCodeIn hasCodeOut decimalsIn decimalsOut
  | .demand caller amountIn maxAmountOut => demand s caller amountIn maxAmountOut
  | .fulfill caller amountIn amountOut => fulfill s caller amountIn amountOut
  | .redeem caller id => redeem s caller id
  | .resolve id fid => resolve s id fid
  | .retrieve caller amount => retrieve s caller amount
  | .redeemable id => do
      let _ ← redeemable s id
      return (s, #[])
  | .pending id => do
      let _ ← pending s id
      return (s, #[])
  | .demandFromId id => do
      let _ ← demandFromId s id
      return (s, #[])
  | .fulfillmentFromId id => do
      let _ ← fulfillmentFromId s id
      return (s, #[])
  | .lookup id => do
      let _ ← lookup s id
      return (s, #[])
  | .unredeemable => do
      let _ ← unredeemable s
      return (s, #[])
  | .demandsCount | .fulfillmentsCount | .retrievable
  | .multiVehicle | .assetIn | .assetOut => .ok (s, #[])

/-- Legacy shallow regression helper only: nested operations here do not schedule
    their own token boundaries. The recursive theorem below NEVER uses this. -/
def executeWithCallbacks (s : QueueState) (op : QueueOperation)
    (callbacks : List (List QueueOperation)) : Except String QueueState := do
  let (published, calls) ← execute s op
  let (_, finalState) ← calls.toList.zipIdx.foldlM (fun (unused, state) (_call, i) => do
    let ops := callbacks[i]?.getD []
    let nextState := ops.foldl (fun acc nested => attempt acc (execute acc nested)) state
    return (unused, nextState)) ((), published)
  return finalState

/-- Legacy shallow helper; not used by `executeCallbackHistory`. -/
def attemptWithCallbacks (s : QueueState) (op : QueueOperation)
    (callbacks : List (List QueueOperation)) (allTokenCallsSucceed : Bool) : QueueState :=
  if allTokenCallsSucceed then (executeWithCallbacks s op callbacks).toOption.getD s
  else s

/-- Any finite sequence, with failing calls leaving the original storage intact.
    Keep this simple history independent of the recursive callback semantics. -/
def executeHistory (s : QueueState) (ops : List QueueOperation) : QueueState :=
  ops.foldl (fun state op => attempt state (execute state op)) s

/-! The custom finite tree/lists below make the nested evaluator structurally
recursive (not depth-fuel bounded). A node has one callback sequence for each
transfer site, in emitted order. Missing sites mean empty callbacks; excess
sites are ignored. Each descendant has its OWN token-success flag and child
sites. The outer list of invocations is unrestricted. -/
mutual
  inductive ScheduledOperation where
    | node (operation : QueueOperation) (callbacks : CallbackSites)
        (tokenCallsSucceed : Bool)
    deriving Repr

  inductive CallbackSites where
    | nil
    | cons (atSite : CallbackSequence) (remaining : CallbackSites)
    deriving Repr

  inductive CallbackSequence where
    | nil
    | cons (first : ScheduledOperation) (remaining : CallbackSequence)
    deriving Repr
end

/-- Convert an ordinary finite list to the structurally recursive callback list. -/
def CallbackSequence.ofList : List ScheduledOperation → CallbackSequence
  | [] => .nil
  | item :: rest => .cons item (ofList rest)

/-- One callback list per emitted transfer, no preset nesting or width bound. -/
def CallbackSites.ofLists : List (List ScheduledOperation) → CallbackSites
  | [] => .nil
  | items :: rest => .cons (CallbackSequence.ofList items) (ofLists rest)

/- Evaluate a finite call tree using structurally smaller descendants. Every
    successful queue transition publishes all its accounting writes BEFORE its
    token calls. Failure at any level returns that invocation's complete pre-call
    state, including rollback of successful descendants; a failed child alone
    leaves its enclosing invocation free to continue. A false token flag is an
    extensional nominal-storage projection of failure at any of its call sites:
    callbacks before the failure also roll back and need not be evaluated.
    The model omits ERC20 balances, return data, gas and read-only observations. -/
mutual
  def executeScheduled (s : QueueState) : ScheduledOperation → QueueState
    | .node op callbacks tokenCallsSucceed =>
        match execute s op with
        | .error _ => s
        | .ok (published, calls) =>
            if !tokenCallsSucceed && !calls.isEmpty then s
            else executeCallSites published calls.toList callbacks

  def executeCallSites (s : QueueState) (calls : List ExternalCall) : CallbackSites → QueueState
    | .nil => s
    | .cons atSite rest =>
        match calls with
        | [] => s
        | _ :: remaining => executeCallSites (executeCallbackSequence s atSite) remaining rest

  def executeCallbackSequence (s : QueueState) : CallbackSequence → QueueState
    | .nil => s
    | .cons item rest => executeCallbackSequence (executeScheduled s item) rest
end

/-- Every outer invocation has its own recursive finite callback tree. -/
def executeCallbackHistory (s : QueueState)
    (schedule : List ScheduledOperation) : QueueState :=
  schedule.foldl executeScheduled s

/-! ## Executable Verity ContractState projection

`QueueState` above is the source-shaped executable semantics. The following
adapter stores its words in a PROOF-ONLY layout in Verity.ContractState and
executes the SAME `execute` transition as a Verity.Contract monad. This ties
all specifications to an executable Verity state transition, but does not
claim a `verity_contract` EDSL/Yul translation or ERC-7201 layout identity.
The actual deployed storage layout is not assigned the synthetic slot numbers.
-/

private def asWord (n : Nat) : Verity.Uint256 := Verity.Core.Uint256.ofNat n
private def asWords (xs : Array Nat) : List Verity.Uint256 :=
  xs.toList.map asWord
private def fromWords (xs : List Verity.Uint256) : Array Nat :=
  (xs.map (fun x => (x : Nat))).toArray

/-- The adapter's slots are deliberately disjoint PROOF-ONLY lanes.
    10..13: demand fields; 20..22: fulfillment fields; 30..34: ghost. -/
def encodeVerity (q : QueueState) (v : Verity.ContractState) : Verity.ContractState :=
  { v with
    storageWords := fun key =>
      match key with
      | .slot 0 => asWord (if q.initialized then 1 else 0)
      | .slot 1 => asWord q.multiVehicle
      | .slot 2 => asWord q.manager
      | .slot 3 => asWord q.assetIn
      | .slot 4 => asWord q.assetOut
      | .slot 5 => asWord q.retrievable
      | .slot 6 => asWord q.selfAddress
      | _ => v.storageWords key,
    storageArray := fun laneIdx =>
      if laneIdx = 10 then asWords (q.demands.map (·.position))
      else if laneIdx = 11 then asWords (q.demands.map (·.amountIn))
      else if laneIdx = 12 then asWords (q.demands.map (·.maxAmountOut))
      else if laneIdx = 13 then asWords (q.demands.map (·.highestFulfillmentId))
      else if laneIdx = 20 then asWords (q.fulfillments.map (·.position))
      else if laneIdx = 21 then asWords (q.fulfillments.map (·.filledAmountIn))
      else if laneIdx = 22 then asWords (q.fulfillments.map (·.amountOut))
      else if laneIdx = 30 then asWords (q.allocations.map (·.demandId))
      else if laneIdx = 31 then asWords (q.allocations.map (·.fulfillmentId))
      else if laneIdx = 32 then asWords (q.allocations.map (·.start))
      else if laneIdx = 33 then asWords (q.allocations.map (·.length))
      else if laneIdx = 34 then asWords (q.allocations.map (·.nominalPayout))
      else v.storageArray laneIdx }

def decodeVerity (v : Verity.ContractState) : QueueState := Id.run do
  let lane := fun laneIdx => fromWords (v.storageArray laneIdx)
  let valueAt := fun laneIdx i => (lane laneIdx)[i]?.getD 0
  let demands := ((List.range (lane 10).size).map fun i =>
    (⟨valueAt 10 i, valueAt 11 i, valueAt 12 i, valueAt 13 i⟩ : Demand)).toArray
  let fulfillments := ((List.range (lane 20).size).map fun i =>
    (⟨valueAt 20 i, valueAt 21 i, valueAt 22 i⟩ : Fulfillment)).toArray
  let allocations := ((List.range (lane 30).size).map fun i =>
    (⟨valueAt 30 i, valueAt 31 i, valueAt 32 i, valueAt 33 i, valueAt 34 i⟩ : Allocation)).toArray
  return { initialized := v.storage 0 != 0, multiVehicle := v.storage 1, manager := v.storage 2, assetIn := v.storage 3, assetOut := v.storage 4, retrievable := v.storage 5, selfAddress := v.storage 6, demands := demands, fulfillments := fulfillments, allocations := allocations }

/-- Executable Verity state transition, the central bridge for subsequent
    proof obligations. Failed execution reverts to precisely the prestate. -/
def executeVerity (op : QueueOperation) : Verity.Contract Unit := fun v =>
  match execute (decodeVerity v) op with
  | .ok (q', _) => .success () (encodeVerity q' v)
  | .error err => .revert err v

/-- The adapter is definitionally connected to the source-structured
    transition; this is NOT the missing Solidity/EDSL bytecode refinement. -/
theorem executeVerity_success (op : QueueOperation) (v : Verity.ContractState)
    (post : QueueState) (calls : Array ExternalCall)
    (h : execute (decodeVerity v) op = .ok (post, calls)) :
    (executeVerity op).run v = .success () (encodeVerity post v) := by
  simp only [Verity.Contract.run, executeVerity, h]

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
