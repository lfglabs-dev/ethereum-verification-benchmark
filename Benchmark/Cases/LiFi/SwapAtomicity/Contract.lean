import Contracts.Common

namespace Benchmark.Cases.LiFi.SwapAtomicity

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
# LI.FI swap route atomicity model

This is a focused model of the LI.FI source-chain swap route used by the
original `GenericSwapFacet.swapTokensGeneric`, `SwapperV2._depositAndSwap`,
`SwapperV2._executeSwaps`, and `LibSwap.swap`.

Simplifications:

- Each `LibSwap.SwapData` item is represented by an already-decoded `SwapStep`.
  The calldata selector, native/ERC20 distinction, deposit flag, approve target
  relation, token-call success, and DEX-call success are represented by
  booleans because the selected invariant is about all-or-nothing control
  flow. `approveNeeded` means the non-native approval path runs; `approveAllowed`
  abstracts the approve-target allow-list condition and is true when
  `approveTo == callTo` or when the distinct approve target is allow-listed.
- Short calldata is represented by `calldataWellFormed = false`, matching the
  revert behavior of `bytes4(currentSwap.callData[:4])`.
- External token, refund, transfer, and DEX calls are represented by success
  flags. The model verifies LI.FI's propagation of those failures, not
  third-party protocol internals or whether a successful DEX call performed the
  intended economic swap beyond the modeled minimum-output gate.
- EVM transaction rollback is represented by `Option.none`: a reverting route
  has no committed `RouteCommit`, so there is no final receiver transfer or
  partial-success result.
- Event fields, integrator/referrer strings, exact balances, and leftover
  refund amounts are outside the first theorem set. The success or failure of
  the leftover-refund phase is modeled explicitly, while the exact refund
  amounts are abstracted away. The final output amount is modeled by an
  `outputAmount` parameter checked against `minAmount`.
- The native-reserve `_depositAndSwap` overload, `GenericSwapFacetV3`, and
  periphery `Executor` swap loops are out of scope for this case.
-/

/-- Decoded controls for one LI.FI swap or generic-call step. -/
structure SwapStep where
  calldataWellFormed : Bool
  callAllowed : Bool
  approveAllowed : Bool
  approveNeeded : Bool
  approveToNonzero : Bool
  approvalSucceeds : Bool
  callToIsContract : Bool
  amountPositive : Bool
  stepBalanceReadsSucceed : Bool
  requiresDeposit : Bool
  depositSucceeds : Bool
  callSucceeds : Bool
  deriving Repr, DecidableEq

/--
`LibAsset.depositAssets` runs before `_executeSwaps` and deposits only swaps
with `requiresDeposit == true`.
-/
def depositForStepSucceeds (step : SwapStep) : Bool :=
  !step.requiresDeposit || step.depositSucceeds

/-- All required route-level deposits succeeded before the swap loop starts. -/
def depositsSucceed : List SwapStep → Bool
  | [] => true
  | step :: rest => depositForStepSucceeds step && depositsSucceed rest

/-- Count only `SwapData` entries that require a pre-loop deposit. -/
def requiredDepositCount : List SwapStep → Nat
  | [] => 0
  | step :: rest =>
      (if step.requiresDeposit then 1 else 0) + requiredDepositCount rest

/--
Route-level public-facet and `_depositAndSwap` gates that are not properties of
one specific swap step.

The order modeled by `depositAndSwap` is:

1. `GenericSwapFacet.swapTokensGeneric` rejects a zero receiver.
2. The `nonReentrant` entry guard allows the call.
3. `_depositAndSwap` rejects an empty swap array.
4. Initial/fetch balance reads succeed.
5. Required deposits succeed.
6. `_executeSwaps` runs the ordered swap loop.
7. The `noLeftovers` refund phase succeeds.
8. The final post-swap balance read and minimum-output check succeed.
9. The final receiver transfer and `refundExcessNative` trailing transfer
   succeed, so the public call commits.
-/
structure RouteGuards where
  receiverNonzero : Bool
  nonReentrantEntered : Bool
  preSwapBalanceReadsSucceed : Bool
  leftoverRefundsSucceed : Bool
  postSwapBalanceReadSucceeds : Bool
  finalTransferSucceeds : Bool
  excessNativeRefundSucceeds : Bool
  deriving Repr, DecidableEq

/--
The preconditions that must hold before `LibSwap.swap` can make and accept the
external call for one step.

This combines:
- `SwapperV2._executeSwaps` calldata selector extraction,
- `callTo+selector` allow-list check,
- approve-target allow-list, non-zero spender, and approval success checks when
  approval is needed,
- `LibSwap.swap` contract and non-zero amount checks,
- receiving-asset balance reads around the low-level external call.
-/
def stepPreconditionsHold (step : SwapStep) : Bool :=
  step.calldataWellFormed &&
  step.callAllowed &&
  (!step.approveNeeded ||
    (step.approveAllowed && step.approveToNonzero && step.approvalSucceeds)) &&
  step.callToIsContract &&
  step.amountPositive &&
  step.stepBalanceReadsSucceed

/--
One route step succeeds exactly when all LI.FI preconditions hold and the
external low-level call returns `success == true`.
-/
def stepSucceeds (step : SwapStep) : Bool :=
  stepPreconditionsHold step && step.callSucceeds

/--
Execute LI.FI route steps in order.

`none` models any revert in the loop. `some n` means the loop completed and
committed `n` step executions.
-/
def executeSwapsCount : List SwapStep → Option Nat
  | [] => some 0
  | step :: rest =>
      if stepSucceeds step then
        match executeSwapsCount rest with
        | some count => some (count + 1)
        | none => none
      else
        none

/-- Committed route summary visible after the public facet succeeds. -/
structure RouteCommit where
  depositedRequiredSteps : Nat
  executedSteps : Nat
  finalTransferCommitted : Bool
  outputAmount : Nat
  deriving Repr, DecidableEq

/--
Focused model of `SwapperV2._depositAndSwap` plus the final receiver transfer in
`GenericSwapFacet.swapTokensGeneric`.

The route commits only when:
- the receiver is non-zero,
- the swap array is non-empty,
- the balance reads, required deposits, leftover refunds, final receiver
  transfer, and excess-native refund complete without reverting,
- every step succeeds,
- the modeled final output is at least `minAmount`.
-/
def depositAndSwap (route : RouteGuards) (minAmount outputAmount : Nat)
    (steps : List SwapStep) : Option RouteCommit :=
  if !route.receiverNonzero then
    none
  else if !route.nonReentrantEntered then
    none
  else if steps = [] then
    none
  else if !route.preSwapBalanceReadsSucceed then
    none
  else if !depositsSucceed steps then
    none
  else
    match executeSwapsCount steps with
    | none => none
    | some _executed =>
        if !route.leftoverRefundsSucceed then
          none
        else if !route.postSwapBalanceReadSucceeds then
          none
        else if minAmount ≤ outputAmount then
          if route.finalTransferSucceeds && route.excessNativeRefundSucceeds then
            some {
              depositedRequiredSteps := requiredDepositCount steps
              executedSteps := steps.length
              finalTransferCommitted := true
              outputAmount := outputAmount
            }
          else
            none
        else
          none

/-- At least one route-level gate outside the swap loop reverted. -/
def routeGateFails (route : RouteGuards) (steps : List SwapStep) : Prop :=
  steps = [] ∨
  route.receiverNonzero = false ∨
  route.nonReentrantEntered = false ∨
  route.preSwapBalanceReadsSucceed = false ∨
  depositsSucceed steps = false ∨
  route.leftoverRefundsSucceed = false ∨
  route.postSwapBalanceReadSucceeds = false ∨
  route.finalTransferSucceeds = false ∨
  route.excessNativeRefundSucceeds = false

/-- Reader-friendly projection: did the public route reach the receiver transfer? -/
def finalTransferCommitted (result : Option RouteCommit) : Bool :=
  match result with
  | some commit => commit.finalTransferCommitted
  | none => false

/-- Reader-friendly projection: how many swap steps are committed? -/
def committedSwapCount (result : Option RouteCommit) : Nat :=
  match result with
  | some commit => commit.executedSteps
  | none => 0

/-- Every modeled route step from the provided `_swapData` succeeded. -/
def allStepsSucceeded (steps : List SwapStep) : Prop :=
  ∀ step, step ∈ steps → stepSucceeds step = true

end Benchmark.Cases.LiFi.SwapAtomicity
