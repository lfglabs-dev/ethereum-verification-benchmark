import Benchmark.Cases.Dromos.AllocationConservation.Specs

/-! Small finite executable regressions, separate from proof modules. These
exercise the actual Verity model, not Solidity or deployed state. No regression
is presented as an arbitrary-input conservation proof. -/
namespace Benchmark.Cases.Dromos.AllocationConservation
open Verity

set_option maxHeartbeats 1000000

def emptyState : ContractState := {
  storageWords := fun _ => 0
  storageArray := fun _ => []
  sender := 11
  thisAddress := 100
  msgValue := 0
  blockTimestamp := 100
  knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty }

def testEnvironment : Environment := {
  votingEscrow := 11
  orchestrator := 22
  authorizedForToken := true
  snapshot := { stakeEnd := 0, isPermanent := true, staked := 100 } }

def expect (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

def successful (op : Contract Unit) (s : ContractState) : IO ContractState :=
  match op.run s with
  | .success _ next => pure next
  | .revert reason _ => throw (IO.userError s!"unexpected revert: {reason}")

def rejected (op : Contract Unit) (s : ContractState) (label : String) : IO Unit :=
  match op.run s with
  | .success _ _ => throw (IO.userError s!"unexpected success: {label}")
  | .revert _ rolledBack => do
      for t in ([0,1,2] : List Uint256) do
        expect (tokenStates rolledBack t == tokenStates s t) s!"rollback token {label}"
        expect (allocationChainIds rolledBack t == allocationChainIds s t) s!"rollback set {label}"
        for c in ([0,1,2,3] : List Uint256) do
          expect (allocationChainAmounts rolledBack t c == allocationChainAmounts s t c) s!"rollback amount {label}"
          expect (allocationChainPositions rolledBack t c == allocationChainPositions s t c) s!"rollback position {label}"

def checkLedger (s : ContractState) (label : String) : IO Unit := do
  for t in ([0,1,2] : List Uint256) do
    expect (allocationSum s t == (tokenStates s t).committed) s!"sum {label}"
    expect (decide (allocationChainIds s t).Nodup) s!"duplicates {label}"
    for c in ([0,1,2,3] : List Uint256) do
      expect ((c ∈ allocationChainIds s t) == (allocationChainAmounts s t c > 0)) s!"support {label}"
      expect (allocationChainPositions s t c == expectedPosition (allocationChainIds s t) c) s!"position {label}"

def runRegression : IO Unit := do
  let e := testEnvironment
  checkLedger emptyState "initial"
  let parked ← successful (parkOnChain0 e 1) emptyState
  expect (allocationChainAmounts parked 1 0 == 100) "park full stake"
  checkLedger parked "park"
  let allocations : List ChainAllocation := [⟨1,30,true,true⟩,⟨2,20,true,true⟩]
  let allocated ← successful (allocateChains e 1 allocations) parked
  expect (allocationChainAmounts allocated 1 0 == 50 && allocationChainAmounts allocated 1 1 == 30 &&
    allocationChainAmounts allocated 1 2 == 20) "partial allocation"
  checkLedger allocated "allocation"
  let returned ← successful (authenticatedReturn e ⟨1,1,10,true⟩) allocated
  expect (allocationChainAmounts returned 1 0 == 60 && allocationChainAmounts returned 1 1 == 20) "partial return"
  checkLedger returned "partial return"
  let repeated ← successful (authenticatedReturn e ⟨1,1,10,true⟩) returned
  expect (allocationChainAmounts repeated 1 1 == 10) "repeat credits remaining booking, not universally zero"
  checkLedger repeated "repeat return"
  let drained ← successful (authenticatedReturn e ⟨1,1,100,true⟩) repeated
  expect (allocationChainAmounts drained 1 1 == 0 && allocationChainAmounts drained 1 0 == 80) "clamped full return"
  checkLedger drained "clamp"
  let noop ← successful (authenticatedReturn e ⟨1,1,100,true⟩) drained
  expect (allocationChainAmounts noop 1 0 == 80) "drained return no-op"
  checkLedger noop "drained return"
  let synchronous := { e with chainCallbacks := [⟨1,1,10,true⟩] }
  let callbackState ← successful (allocateChains synchronous 1 [⟨1,10,true,true⟩]) parked
  expect (allocationChainAmounts callbackState 1 1 == 0 && allocationChainAmounts callbackState 1 0 == 100) "guard admits synchronous return"
  checkLedger callbackState "callback"
  let composedEnv := { e with chainCallbacks := [⟨1,1,10,true⟩], gaugeCallbacks := [⟨1,1,20,true⟩] }
  let composed ← successful (allocate composedEnv 1 [⟨1,30,true,true⟩] true true) parked
  expect (allocationChainAmounts composed 1 0 == 100 && allocationChainAmounts composed 1 1 == 0) "composed allocation callbacks"
  checkLedger composed "composed allocation"
  let emergency ← successful (emergencyDeallocate e 1 2 true true true) allocated
  expect (allocationChainAmounts emergency 1 0 == 70 && allocationChainAmounts emergency 1 2 == 0) "emergency full return"
  checkLedger emergency "emergency"
  let reanchored ← successful (parkOnChain0 { e with snapshot := { staked := 100, stakeEnd := 1000, isPermanent := false } } 1) allocated
  expect ((tokenStates reanchored 1).lastStakeEnd == 1000 && (tokenStates reanchored 1).isPermanent == false &&
    allocationChainAmounts reanchored 1 1 == 30) "shape change preserves amount"
  checkLedger reanchored "reanchor"
  let framed ← successful (nonwriterWithReturns e [⟨1,1,5,true⟩]) allocated
  expect (allocationChainAmounts framed 1 0 == 55 && allocationChainAmounts framed 1 1 == 25) "nonwriter callback closure"
  checkLedger framed "nonwriter callback"
  let wrappedTime ← successful (allocateChains e 1 []) { parked with blockTimestamp := Verity.Core.Uint256.ofNat (timeLimit + 100) }
  expect ((tokenStates wrappedTime 1).lastAllocated == 100) "uint48 timestamp cast, not an extra time-range assumption"
  checkLedger wrappedTime "timestamp cast"
  let zeroPark ← successful (parkOnChain0 { e with snapshot := { e.snapshot with staked := 80 } } 1) parked
  expect ((tokenStates zeroPark 1).committed == 100) "saturating park"
  checkLedger zeroPark "saturating park"
  let rebalance ← successful (rebalanceChain0 e [⟨1,20⟩,⟨1,10⟩]
    [⟨⟨1,10⟩,⟨0,true⟩⟩,⟨⟨0,20⟩,⟨0,true⟩⟩]) parked
  expect ((tokenStates rebalance 1).committed == 80 && (tokenStates rebalance 0).committed == 20) "alias and TOKEN0 destination"
  checkLedger rebalance "rebalance"
  let burned ← successful (burn e 20) rebalance
  expect ((tokenStates burned 0).committed == 0 && allocationChainIds burned 0 == []) "TOKEN0 drained burn"
  checkLedger burned "burn"
  let cleared ← successful (clearToken e 1) allocated
  expect ((tokenStates cleared 1).committed == 0 && allocationChainIds cleared 1 == [] &&
    allocationChainAmounts cleared 1 1 == 0 && allocationChainAmounts cleared 1 2 == 0) "clear all stored chains"
  checkLedger cleared "clear"
  rejected (clearToken e 0) rebalance "TOKEN0 not clearable"
  rejected (allocateChains e 1 [⟨0,1,true,true⟩]) parked "CHAIN0 forbidden in caller allocation"
  rejected (allocateChains e 1 [⟨1,1,true,true⟩,⟨1,1,true,true⟩]) parked "duplicate chain allocation"
  rejected (allocateChains e 1 [⟨1,101,true,true⟩]) parked "insufficient CHAIN0"
  rejected (authenticatedReturn e ⟨0,1,1,true⟩) parked "origin CHAIN0 forbidden"
  rejected (burn e 1) parked "burn insufficient TOKEN0"
  rejected (parkOnChain0 { e with snapshot := { e.snapshot with staked := 0 } } 1) emptyState "withdrawn stake"
  rejected (guarded (burn e 1)) rebalance "nested guarded writer rejected"
  rejected (allocateChains e 1 [⟨1,amountLimit - 1,true,true⟩,⟨2,1,true,true⟩]) parked "uint128 total delta overflow"
  rejected (parkOnChain0 e 1) { parked with sender := 99 } "wrong escrow sender"
  rejected (processDeallocation e ⟨1,1,1,true⟩) allocated "wrong orchestrator sender"
  rejected (allocateChains { e with authorizedForToken := false } 1 []) parked "false token authorization"
  -- First source leg writes successfully; second fails and the outer run rolls
  -- back values, positions, amounts and commitment, not just the last leg.
  rejected (rebalanceChain0 e [⟨1,10⟩,⟨1,100⟩] []) parked "late batch underflow"
  let hi : Uint256 := Verity.Core.Uint256.ofNat (2 ^ 200 + 1)
  let hiPark ← successful (parkOnChain0 e hi) allocated
  let hiAlloc ← successful (allocateChains e hi [⟨hi,40,true,true⟩]) hiPark
  expect (allocationChainAmounts hiAlloc hi hi == 40 && allocationChainAmounts hiAlloc hi 1 == 0) "full-width chain separation"
  expect (allocationChainAmounts hiAlloc 1 1 == 30 && (tokenStates hiAlloc 1).committed == 100) "full-width token separation"
  expect (allocationChainIds hiAlloc hi == [0,hi] && allocationChainPositions hiAlloc hi hi == 2 &&
    allocationChainPositions hiAlloc hi 1 == 0) "full-width positions separation"
  let hiClear ← successful (clearToken e hi) hiAlloc
  expect (allocationChainIds hiClear hi == [] && allocationChainPositions hiClear hi hi == 0 &&
    allocationChainPositions hiClear hi 0 == 0 && allocationChainAmounts hiClear hi hi == 0) "high-key clear positions"
  let reused ← successful (parkOnChain0 e hi) hiClear
  expect (allocationChainIds reused hi == [0] && allocationChainPositions reused hi 0 == 1) "clear then reuse"
  let add123 : Contract Unit := do
    let _ ← setAdd 2 1
    let _ ← setAdd 2 2
    let _ ← setAdd 2 3
    Verity.pure ()
  let setState ← successful add123 emptyState
  let removeFirst : Contract Unit := do let _ ← setRemove 2 1; Verity.pure ()
  let swapped ← successful removeFirst setState
  expect (allocationChainIds swapped 2 == [3,2] && allocationChainPositions swapped 2 3 == 1 &&
    allocationChainPositions swapped 2 2 == 2 && allocationChainPositions swapped 2 1 == 0) "OZ moved-position update"
  let removeLast : Contract Unit := do let _ ← setRemove 2 3; Verity.pure ()
  let popped ← successful removeLast setState
  expect (allocationChainIds popped 2 == [1,2] && allocationChainPositions popped 2 3 == 0 &&
    allocationChainPositions popped 2 1 == 1 && allocationChainPositions popped 2 2 == 2) "OZ remove last"
  let addExisting : Contract Unit := do
    let added ← setAdd 2 2
    require (!added) "ExistingElementAdded"
  let unchanged ← successful addExisting setState
  expect (allocationChainIds unchanged 2 == [1,2,3] && allocationChainPositions unchanged 2 2 == 2) "OZ duplicate add no-op"
  let removeAbsent : Contract Unit := do
    let removed ← setRemove 2 0
    require (!removed) "AbsentElementRemoved"
  let absent ← successful removeAbsent setState
  expect (allocationChainIds absent 2 == [1,2,3] && allocationChainPositions absent 2 0 == 0) "OZ absent remove no-op"
  let setCleared ← successful (setClear 2) setState
  for c in ([0,1,2,3] : List Uint256) do
    expect (allocationChainPositions setCleared 2 c == 0) "OZ clear positions loop"
  expect (allocationChainIds setCleared 2 == []) "OZ clear logical length"
  IO.println "PASS: initial state; 16 original ledger transitions; 4 high-key ledger transitions; 13 rejection/rollback checks; 5 concrete set scenarios with positions"

#eval runRegression
end Benchmark.Cases.Dromos.AllocationConservation
