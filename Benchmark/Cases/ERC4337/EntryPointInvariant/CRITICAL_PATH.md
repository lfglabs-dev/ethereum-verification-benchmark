# ERC-4337 EntryPoint invariant — critical path map

This case ships **76+ theorems** across several files. Most are supporting
or historic. Only **a small subset** is load-bearing for the headline
Yoav-grade theorem `yoav_counting_biconditional_under_arbitrary_callees`.

Use this map to navigate the proof for review.

## Headline theorem

`IndexedCounting.lean::yoav_indexed_counting_biconditional`

> For each op index `i`, the execution-event count is `1` iff the batch
> validated AND op `i` has non-empty callData. Otherwise the count is `0`.
> **No pairwise-distinctness premise** — op indices are inherently unique,
> so two ops with identical `(sender, callData)` are still counted
> separately by index.

For aggregated batches (BLS aggregator path),
`Aggregator.lean::yoav_aggregated_biconditional` applies the same
theorem to `handleAggregatedOps` via `combinedApprovals`. No proof
duplication.

For the `(sender, callData)` form (which requires pairwise distinctness),
see `Yoav.lean::yoav_counting_biconditional_under_arbitrary_callees`.

## Critical path (10 lemmas + 1 theorem)

These are the lemmas the headline theorem *directly* depends on. If any
one of them broke, the headline would no longer compile.

| # | Lemma | File | Purpose |
|---|-------|------|---------|
| L1 | `bump_strictly_increases` | `UserOp.lean` | replay protection (nonce monotonicity) |
| L2 | `executionLoop_event_origin` | `Trace.lean` | every emitted event came from some op |
| L3 | `Verity.EVM.Frame.external_call_preserves_caller_storage` | (upstream) | EVM CALL frame for storage |
| L4 | `Verity.EVM.Frame.external_call_preserves_caller_memory` | (upstream) | EVM CALL frame for memory |
| L5 | `Verity.EVM.Layout.call_buffer_disjoint_from_heap` | (upstream) | solc layout disjointness |
| L6 | `executionLoop_count_le_one` | `Trace.lean` | at-most-once under pairwise distinct |
| L7 | `executionLoop_count_ge_one` | `Trace.lean` | at-least-once when validated |
| L8 | `EntryPointV09.handleOp` EOA guard checks | `EntryPointV09.lean` / `Bytecode.lean` | EntryPoint v0.9 `nonReentrant` rejects non-EOA callers |
| L9 | `yoav_count_eq_one_when_validated_and_executable` | `Yoav.lean` | bridges loop to counting |
| L10| `yoav_count_eq_zero_when_validation_fails` | `Yoav.lean` | failure side |
| **T** | `yoav_counting_biconditional_under_arbitrary_callees` | `Yoav.lean` | the composition |

## Supporting (corollaries / refinements)

These follow from the critical path or strengthen it on subsystems. Useful
for review but not load-bearing for the headline.

- `Proofs.lean` — abstract control flow (23 theorems): biconditional,
  all-or-nothing, length/bounds, batch composition, lifecycle. Originally
  the headline statement before the counting form was introduced.
- `Frame.lean` (`Benchmark` namespace) — 10 theorems: Verity-contract
  shape of the frame conditions. The EVM CALL frame lemmas are consumed
  from upstream `Verity.EVM.Frame`; `EvmYulFrame.lean` is only a stable
  benchmark namespace adapter.
- `Bytecode.lean` — 4 theorems: composes the abstract biconditional with
  the upstream frame conditions and records the EntryPointV09 EOA-only
  guard shape.
- `Refinement.lean` — connects `EntryPointV09`'s storage delta to the
  abstract `validationLoop` / `executionLoop`. (item A)
- `Trace.lean` extra lemmas (`executionLoop_event_origin`,
  `executionLoop_contains_op_event`) — used by L6/L7.
- `UserOp.lean` — `PackedUserOperation`, 2D nonce, `ValidationData`
  decomposition. Replay-protection and time-window facts.

## Historic (proven; kept for archaeology)

- The original 8 theorems documented in `cases/erc4337/.../tasks/*.yaml`
  before the counting form was introduced. The biconditional + lifecycle
  theorems are now corollaries of `yoav_counting_biconditional`.

## Reviewing the proof

If you only have an hour, read `Yoav.lean` end-to-end and check the 10
critical-path lemmas above. Everything else is supporting material.

If you have a day, also read `Trace.lean` (the abstract model) and
`Refinement.lean` (the bridge to `EntryPointV09`).

The upstream frame/layout lemmas (L3, L4, L5) now exist in verity main
(`Verity.EVM.Frame.external_call_preserves_caller_storage` /
`external_call_preserves_caller_memory`,
`Verity.EVM.Layout.call_buffer_disjoint_from_heap`), shipped via
`lfglabs-dev/verity#1969`, and this benchmark now consumes them directly.
`Layout.lean` keeps the EntryPoint-specific `opInfos` field names as a thin
adapter over upstream `Verity.EVM.Layout`.

`TransientGuard.lean` remains only as a smoke invoking upstream
`Verity.Core.nonReentrantTransient_locked_reverts`. It is not part of the
EntryPoint critical path because EntryPoint v0.9's
`nonReentrant` modifier is an EOA-only gate
`tx.origin == msg.sender && msg.sender.code.length == 0`, modeled in
`EntryPointV09.lean` with `msgSender` plus `txOriginOracle` and
`callerCodeLength` oracles for the origin and code-length conjuncts.
