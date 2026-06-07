import Benchmark.Cases.ERC4337.EntryPointInvariant.Trace
import Benchmark.Cases.ERC4337.EntryPointInvariant.IndexedCounting
import Benchmark.Cases.ERC4337.EntryPointInvariant.Yoav

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
# `handleAggregatedOps` — added without duplicating proofs

EntryPoint v0.9 exposes two top-level entry points sharing the same
two-loop validation+execution structure:

* `handleOps` — per-op signature validation.
* `handleAggregatedOps` — ops grouped by aggregator; the EntryPoint
  calls `aggregator.validateSignatures(ops)` per group, then per-op
  validation.

Structural insight: per-op validation in `handleAggregatedOps` is the
**same** validation step as in `handleOps`, with the per-op signature
gate replaced by the aggregator decision. We reuse the abstract
`validationLoop` by composing the approvals list with the aggregator
verdicts — no proof duplication.

## Modelling

`validateAggregator : Address → Bool` is the oracle parameter (the
actual `aggregator.validateSignatures` call is opaque). The combined
`accountApprovals[i] = aggregatorOk(groupOf i) ∧ accountOk[i]`.

`handleAggregatedOps` reduces to `handleOpsMulti` with combined
approvals. The Yoav biconditional + indexed counting + frame conditions
apply without re-proof — they're parametric in `approvals`.
-/

/-- A group of ops sharing a single aggregator. -/
structure OpsGroup where
  aggregator : Address
  ops        : List PackedUserOperation
  deriving Repr

/-- Flatten a list of aggregator groups into the ordered op list. -/
def flattenGroups : List OpsGroup → List PackedUserOperation
  | [] => []
  | g :: rest => g.ops ++ flattenGroups rest

/-- The per-op approval flag combining the aggregator verdict and the
    account decision. Index `i` is the *flat* position. -/
def combineApproval
    (aggOk : Bool) (accountFlag : Bool) : Bool :=
  aggOk && accountFlag

/-- Build the combined approvals list one group at a time. Takes a list
    of per-group `(aggOk, ops.length)` and a flat `accountOk` list,
    returns the combined approvals in flat order. -/
def combinedApprovals
    : List (Bool × Nat) → List Bool → List Bool
  | [], _ => []
  | (aggOk, n) :: rest, acc =>
    (acc.take n).map (combineApproval aggOk) ++
      combinedApprovals rest (acc.drop n)

/-- Project each group to its `(aggregator-decision, ops.length)` pair. -/
def groupVerdicts
    (groups : List OpsGroup)
    (aggregatorOk : Address → List PackedUserOperation → Bool)
    : List (Bool × Nat) :=
  groups.map fun g => (aggregatorOk g.aggregator g.ops, g.ops.length)

/-- **The aggregated entry point**: validates by groups then executes,
    reusing `handleOpsMulti` with the combined approvals. -/
def handleAggregatedOps
    (groups : List OpsGroup)
    (aggregatorOk : Address → List PackedUserOperation → Bool)
    (table : Nonce2DTable)
    (accountOk : List Bool)
    : Option (Nonce2DTable × Trace) :=
  handleOpsMulti
    (flattenGroups groups)
    table
    (combinedApprovals (groupVerdicts groups aggregatorOk) accountOk)

/-! ## Reusing the Yoav biconditional for the aggregated path -/

/-- **The Yoav biconditional applied to `handleAggregatedOps`** — derived
    directly from the indexed counting biconditional by passing through
    the flattened ops + combined approvals. No new proof required. -/
theorem yoav_aggregated_biconditional
    (groups : List OpsGroup)
    (aggregatorOk : Address → List PackedUserOperation → Bool)
    (table : Nonce2DTable) (accountOk : List Bool) (i : Nat)
    (hi : i < (flattenGroups groups).length) :
    countByIndex
      (handleOpsIndexedTrace (flattenGroups groups) table
        (combinedApprovals (groupVerdicts groups aggregatorOk) accountOk)) i = 1 ↔
    batchValidated (flattenGroups groups) table
      (combinedApprovals (groupVerdicts groups aggregatorOk) accountOk) = true ∧
    hasCallData (flattenGroups groups)[i] = true :=
  yoav_indexed_counting_biconditional
    (flattenGroups groups) table
    (combinedApprovals (groupVerdicts groups aggregatorOk) accountOk) i hi

end Benchmark.Cases.ERC4337.EntryPointInvariant
