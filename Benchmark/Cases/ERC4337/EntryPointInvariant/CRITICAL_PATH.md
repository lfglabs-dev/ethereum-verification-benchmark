# ERC-4337 EntryPoint invariant — critical path map

This case ships **76+ theorems** across several files. Most are supporting
or historic. Only **a small subset** is load-bearing for the headline
Yoav-grade theorem `yoav_counting_biconditional_under_arbitrary_callees`.

Use this map to navigate the proof for review.

## Headline theorem

`Yoav.lean::yoav_counting_biconditional_under_arbitrary_callees`

> In any non-reverting `handleOps` batch, for any sequence of arbitrary
> EVM callee invocations, `countExecCalls trace ops[i].sender
> ops[i].callData = 1` iff `batchValidated ∧ opExecutable i`. Otherwise
> the count is `0`.

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
| L8 | `Verity.Core.nonReentrantTransient_locked_reverts` | (upstream) | re-entry blocked (EIP-1153 lock) |
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
  shape of the frame conditions. Subsumed by `Verity.EVM.Frame`.
- `Bytecode.lean` — 4 theorems: composes the abstract biconditional with
  the upstream frame conditions. Wires the toy `EntryPointFrame`.
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

The upstream lemmas (L3, L4, L5, L8) live in `Verity` itself; their proofs
are shipped in `lfglabs-dev/verity#1969`.
