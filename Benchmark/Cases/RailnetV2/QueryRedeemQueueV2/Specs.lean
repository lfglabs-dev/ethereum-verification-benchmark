import Benchmark.Cases.RailnetV2.QueryRedeemQueueV2.Contract

namespace Benchmark.Cases.RailnetV2.QueryRedeemQueueV2

/-!
The Railnet Luca (2026-09-30) specification: for ANY finite queue history
from a successful initialize, in any redeem order and with any number of
repeated partial redeem calls, total nominal payout cannot exceed total
nominal assets provided by fulfill calls. No coverage/last-redeemer premise,
no per-history bound and no budget check in `Contract.lean`.
-/

/-- Σ of actual nominal payouts calculated by the loop, recorded only after
    successful source transitions. Ghost accounting is unbounded Nat. -/
def cumulativeNominalRedeem (s : QueueState) : Nat :=
  s.allocations.toList.foldl (fun total a => total + a.nominalPayout) 0

/-- Σ of immutable `amountOutProvided` values in successful fulfill calls.
    Nominal inputs, not current ERC20 balance or token economic value. -/
def cumulativeNominalFulfill (s : QueueState) : Nat :=
  s.fulfillments.toList.foldl (fun total f => total + f.amountOut) 0

/-- Headline invariant: R(H) = Σ payouts ≤ F(H) = Σ fulfill amountOutProvided. -/
def nominalConservation (s : QueueState) : Prop :=
  cumulativeNominalRedeem s ≤ cumulativeNominalFulfill s

/-- Initial states arise ONLY from successful source initialization. The
    supplied address/code/decimal observations are checked by `initialize`. -/
def Initialized (s : QueueState) : Prop :=
  ∃ parent manager assetIn assetOut : Nat, ∃ hasCodeIn hasCodeOut : Bool,
    ∃ decimalsIn decimalsOut : Nat,
    ( «initialize» {} parent manager assetIn assetOut
        hasCodeIn hasCodeOut decimalsIn decimalsOut).map Prod.fst = .ok s

/-- Source execution is the only way to reach a new state. Reverted calls have
    no effect. `op` is unrestricted: authorization is checked by `execute`,
    not assumed by the theorem. Nesting/callback qualifications in Contract.lean. -/
inductive Reachable : QueueState → Prop where
  | init (s : QueueState) : Initialized s → Reachable s
  | success (s s' : QueueState) (op : QueueOperation) (calls : Array ExternalCall) :
      Reachable s → execute s op = .ok (s', calls) → Reachable s'
  | revert (s : QueueState) (op : QueueOperation) (err : String) :
      Reachable s → execute s op = .error err → Reachable s

/-- Arbitrary finite traces: NO bound on list length, number of redeems or
    demand/fulfillment amount beyond checks performed by successful calls. -/
def conservationForEveryFiniteHistory : Prop :=
  ∀ s : QueueState, Initialized s → ∀ ops : List QueueOperation,
    nominalConservation (executeHistory s ops)

/-- Reachability version of the same target; useful for transition induction. -/
def conservationForEveryReachableState : Prop :=
  ∀ s : QueueState, Reachable s → nominalConservation s

/-- Verity.ContractState view of the exact same executable accounting
    projection, via the explicit decode adapter in Contract.lean. -/
def nominalConservationVerity (v : Verity.ContractState) : Prop :=
  nominalConservation (decodeVerity v)

/-- Finite outer calls with arbitrary finite recursive callback trees: nested
    invocations have independent callbacks at EACH emitted transfer boundary,
    including the gap between fulfill's TWO transfers. A failed child reverts
    only itself; a failed containing token call reverts its entire subtree.
    The target is nominal storage, not returndata, balances, or a mechanized
    EVM-to-Lean simulation. No guards on allocation or coverage are introduced. -/
def conservationForCallbacks : Prop :=
  ∀ s : QueueState, Initialized s →
    ∀ schedule : List ScheduledOperation,
      nominalConservation (executeCallbackHistory s schedule)

/-- Half-open redeemed intervals [start, start+length). The required
    disjointness is a DERIVED invariant of source transitions, never an
    operation precondition. It includes different demands, different
    fulfillments and arbitrarily many separate redeem calls. -/
def disjointAllocations (s : QueueState) : Prop :=
  s.allocations.toList.Pairwise (fun a b : Allocation =>
    a.start + a.length ≤ b.start ∨ b.start + b.length ≤ a.start)

/-- Only allocations whose recorded ID matches this particular fulfillment. -/
def allocatedLengthByFulfillment (s : QueueState) (fid : Nat) : Nat :=
  s.allocations.toList.foldl (fun total a =>
    if a.fulfillmentId = fid then total + a.length else total) 0

/-- A useful intermediate target, NOT a premise of nominalConservation:
    successful updates alone must establish the no-double-spend bound. -/
def fulfillmentIntervalsNotDoubleSpent (s : QueueState) : Prop :=
  ∀ fid : Nat, fid > 0 → fid ≤ s.fulfillments.size →
    allocatedLengthByFulfillment s fid ≤
      (s.fulfillments[fid - 1]!).filledAmountIn

/-- Explicit non-assumptive assertion about the actual transition code.
    Used to organize the later proof, not to constrain reachable executions. -/
def queueInductionTargets (s : QueueState) : Prop :=
  nominalConservation s ∧ disjointAllocations s ∧
  fulfillmentIntervalsNotDoubleSpent s

end Benchmark.Cases.RailnetV2.QueryRedeemQueueV2
