import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.Contract
import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.Specs
import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.Proofs

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-- Executable regression: TWO redeem calls, each allowed 32 fulfillments.
    This is not the general theorem; it exercises the real 32-step fold. -/
def sampleInitialized : QueueState :=
  ((«initialize» {} 11 22 11 33 true true 18 6).toOption.getD
    (({} : QueueState), (#[] : Array ExternalCall))).1

def sixtyFourFills : List QueueOperation :=
  (List.range 64).map (fun _ => .fulfill 22 1 1)

def repeatedRedeemSample : QueueState :=
  executeHistory sampleInitialized
    ([.demand 11 64 64] ++ sixtyFourFills ++ [.redeem 11 1, .redeem 11 1])

/-- Alternate demand order: demand 2 consumes its own interval first. -/
def reversedOrderSample : QueueState :=
  executeHistory sampleInitialized
    [.demand 11 2 2, .demand 11 2 2, .fulfill 22 4 4,
     .redeem 11 2, .redeem 11 1]

/-- Callback during the FIRST token transfer in fulfill (before share transfer). -/
def callbackSample : QueueState :=
  let pre := executeHistory sampleInitialized [.demand 11 1 1]
  (executeWithCallbacks pre (.fulfill 22 1 1) [[.redeem 11 1], []]).toOption.getD pre

/-- Source clamps a better-funded fulfillment to the demand's payout cap;
    excess becomes retrievable (minus one rounding unit). -/
def overfundedSample : QueueState :=
  executeHistory sampleInitialized
    [.demand 11 1 1, .fulfill 22 1 10, .redeem 11 1, .retrieve 22 7]

/-- A permissionless resolve changes the search hint, not the intervals. -/
def resolvedSample : QueueState :=
  executeHistory sampleInitialized
    [.demand 11 1 1, .demand 11 1 1, .fulfill 22 1 1,
     .fulfill 22 1 1, .resolve 2 2, .redeem 11 2, .redeem 11 1]

#eval (mulDivFloor maxWord maxWord maxWord).toOption == some maxWord
#eval (repeatedRedeemSample.demands[0]!.amountIn,
       repeatedRedeemSample.allocations.size,
       cumulativeNominalRedeem repeatedRedeemSample,
       cumulativeNominalFulfill repeatedRedeemSample)
#eval (cumulativeNominalRedeem reversedOrderSample,
       cumulativeNominalFulfill reversedOrderSample,
       reversedOrderSample.allocations.size)
#eval (cumulativeNominalRedeem callbackSample,
       cumulativeNominalFulfill callbackSample)
#eval (cumulativeNominalRedeem overfundedSample,
       cumulativeNominalFulfill overfundedSample,
       overfundedSample.retrievable)
#eval (cumulativeNominalRedeem resolvedSample,
       cumulativeNominalFulfill resolvedSample,
       resolvedSample.allocations.size)

/-- Two levels of recursion: first transfer of outer fulfill invokes another
    fulfill; its first transfer invokes redeem. The second transfer at either
    level is a separately addressable callback site. -/
def twoLevelCallback : ScheduledOperation :=
  let grandchild := ScheduledOperation.node (.redeem 11 1) .nil true
  let child := ScheduledOperation.node (.fulfill 22 1 1)
    (CallbackSites.ofLists [[grandchild], []]) true
  .node (.fulfill 22 1 1) (CallbackSites.ofLists [[child], []]) true

def callbackPrestate : QueueState := executeHistory sampleInitialized [.demand 11 2 2]

def twoLevelResult : QueueState :=
  executeCallbackHistory callbackPrestate [twoLevelCallback]

/-- If the child transfer fails, its appended fulfillment and the grandchild's
    redeemed allocations revert; the enclosing fulfill remains successful. -/
def nestedRevertResult : QueueState :=
  let grandchild := ScheduledOperation.node (.redeem 11 1) .nil true
  let failingChild := ScheduledOperation.node (.fulfill 22 1 1)
    (CallbackSites.ofLists [[grandchild], []]) false
  executeCallbackHistory callbackPrestate
    [.node (.fulfill 22 1 1) (CallbackSites.ofLists [[failingChild], []]) true]

/-- Failure of the containing transfer restores its WHOLE pre-call state, not
    just the immediate child's prestate, even with successful descendants. -/
def enclosingRevertResult : QueueState :=
  let .node op sites _ := twoLevelCallback
  executeCallbackHistory callbackPrestate [.node op sites false]

/-- Fulfill's second transfer boundary also executes callbacks. -/
def secondTransferCallbackResult : QueueState :=
  executeCallbackHistory callbackPrestate
    [.node (.fulfill 22 1 1)
      (CallbackSites.ofLists [[], [.node (.redeem 11 1) .nil true]]) true]

/-- A repeated initialize attempt reverts, with no nominal state change. -/
def repeatedInitializeReverts : Bool :=
  match execute sampleInitialized
      (.«initialize» 11 22 11 33 true true 18 6) with
  | .error "InvalidInitialization" => true
  | _ => false

/-- Compare every field in the modeled queue state (including ghost records). -/
def sameNominalState (a b : QueueState) : Bool :=
  a.initialized == b.initialized && a.selfAddress == b.selfAddress &&
  a.multiVehicle == b.multiVehicle && a.manager == b.manager &&
  a.assetIn == b.assetIn && a.assetOut == b.assetOut &&
  a.retrievable == b.retrievable && a.demands == b.demands &&
  a.fulfillments == b.fulfillments && a.allocations == b.allocations

#eval (twoLevelResult.fulfillments.size, twoLevelResult.allocations.size,
       cumulativeNominalRedeem twoLevelResult, cumulativeNominalFulfill twoLevelResult)
#eval (nestedRevertResult.fulfillments.size, nestedRevertResult.allocations.size,
       nestedRevertResult.demands[0]!.amountIn)
#eval (enclosingRevertResult.fulfillments.size, enclosingRevertResult.allocations.size,
       enclosingRevertResult.demands[0]!.amountIn)
#eval (secondTransferCallbackResult.fulfillments.size,
       secondTransferCallbackResult.allocations.size)
#eval (sameNominalState enclosingRevertResult callbackPrestate,
       sameNominalState nestedRevertResult callbackPrestate,
       sameNominalState (executeHistory sampleInitialized
         [.«initialize» 11 22 11 33 true true 18 6]) sampleInitialized)
#eval repeatedInitializeReverts

/-- Regression for the actual Verity.ContractState adapter (not EDSL codegen). -/
def verityAdapterExecutesDemand : Bool :=
  let v := encodeVerity sampleInitialized Verity.defaultState
  match (executeVerity (.demand 11 1 1)).run v with
  | .success () v' => (decodeVerity v').demands.size == 1
  | .revert _ _ => false

#eval verityAdapterExecutesDemand

/- Final theorem signatures and axiom reports are intentionally emitted by
this checked module; no generated agent-facing task proof is imported. -/
#check conservation_for_every_finite_history
#check conservation_for_every_reachable_state
#check conservation_for_callbacks
#check nominal_conservation_all_histories
#check derived_queue_induction_targets
#print axioms conservation_for_every_finite_history
#print axioms conservation_for_every_reachable_state
#print axioms conservation_for_callbacks
#print axioms nominal_conservation_all_histories
#print axioms derived_queue_induction_targets

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
