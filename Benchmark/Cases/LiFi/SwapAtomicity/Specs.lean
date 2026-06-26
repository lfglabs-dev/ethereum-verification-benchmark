import Verity.Specs.Common
import Benchmark.Cases.LiFi.SwapAtomicity.Contract

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity
open Verity.EVM.Uint256

/-!
# LI.FI swap atomicity specifications

The selected guarantee:

> A LI.FI source-chain swap route over the provided `_swapData` cannot commit a
> final receiver transfer unless every modeled public-route gate succeeded,
> every modeled step in the route succeeded, and the minimum-output check
> passed.

The specs use `Option.none` as the revert/no-commit result. This matches the
EVM-level source-chain atomicity boundary used by the model: when a route
reverts, no LI.FI route commit is observable.
-/

/-- Any failed modeled route step forces the whole route to revert. -/
def failed_step_reverts_spec (steps : List SwapStep) : Prop :=
  (∃ step, step ∈ steps ∧ stepSucceeds step = false) →
  executeSwapsCount steps = none

/-- A failed modeled route step prevents the public final receiver transfer. -/
def no_final_transfer_on_failed_step_spec
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) : Prop :=
  (∃ step, step ∈ steps ∧ stepSucceeds step = false) →
  finalTransferCommitted (depositAndSwap route minAmount outputAmount steps) =
    false

/-- If the public final transfer commits, every modeled route step succeeded. -/
def final_transfer_implies_all_steps_succeeded_spec
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) : Prop :=
  finalTransferCommitted (depositAndSwap route minAmount outputAmount steps) =
    true →
  allStepsSucceeded steps

/-- A committed route cannot represent a partially executed route. -/
def committed_route_executes_every_step_spec
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) : Prop :=
  finalTransferCommitted (depositAndSwap route minAmount outputAmount steps) =
    true →
  committedSwapCount (depositAndSwap route minAmount outputAmount steps) =
    steps.length

/-- The minimum-output check gates successful public route commits. -/
def min_output_required_for_commit_spec
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) : Prop :=
  outputAmount < minAmount →
  finalTransferCommitted (depositAndSwap route minAmount outputAmount steps) =
    false

/-- Any modeled public-route gate failure prevents a committed final transfer. -/
def route_gate_failure_prevents_commit_spec
    (route : RouteGuards) (steps : List SwapStep)
    (minAmount outputAmount : Nat) : Prop :=
  routeGateFails route steps →
  finalTransferCommitted (depositAndSwap route minAmount outputAmount steps) =
    false

end Benchmark.Cases.LiFi.SwapAtomicity
