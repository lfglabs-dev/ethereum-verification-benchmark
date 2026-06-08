# EntryPoint v0.9 differential test harness

This directory contains the differential-testing scaffold for the
Verity-compiled `EntryPointV09` projection and the original `EntryPoint.sol`
v0.9 bytecode. The Verity contract intentionally exposes a flattened one-op
`handleOps` projection instead of Solidity's dynamic
`handleOps(PackedUserOperation[],address)` ABI, so the tests compare the
selected control-flow observations rather than claiming byte-for-byte
equivalence of the full contract interface.

## Pipeline

1. Compile the Verity source:
   ```
   lake env lean --run \
     Benchmark/Cases/ERC4337/EntryPointInvariant/differential/compile-entrypoint.lean \
     build/differential/yul \
     build/differential/entrypoint-abi-adapters.yul
   ```
2. Compile the Yul output to EVM bytecode:
   ```
   solc --strict-assembly build/differential/EntryPointV09.linked.yul \
        --bin
   ```
3. Compile the original EntryPoint v0.9 source pinned to commit
   `b36a1ed52ae00da6f8a4c8d50181e2877e4fa410`:
   ```
   forge build --root vendor/account-abstraction \
               --use 0.8.28 --via-ir --optimizer-runs 200
   ```
4. Run the differential suite:
   ```
   forge test --root Benchmark/Cases/ERC4337/EntryPointInvariant/differential -vv
   ```

`EntryPointDifferential.t.sol` deploys both bytecodes at fresh addresses. The
original EntryPoint is exercised through its real ABI; the Verity artifact is
exercised through the flattened projection interface. Validation/paymaster
callbacks are linked as explicit deterministic ECM stubs, while the sender
execution path remains a real low-level EVM call.

## Test scope

We test the subset of the upstream suite that exercises the validation /
execution control flow — exactly what the Yoav-grade biconditional cares
about:

| Test | Asserts |
|------|---------|
| `testValidateAndExecuteSingleOp` | one op, callData non-empty: upstream executes once; Verity projection reaches its execution path without revert |
| `testNonceReplayRejected` | re-submitting the same `(sender, nonce)` reverts |
| `testReentrancyBlocked` | re-entry into each entry point reverts |
| `testEmptyCallDataNoExec` | op with empty callData: neither path records a sender execution call |

Out of scope (documented divergences, ignored in assertions):

- Gas costs (the Verity model elides gas accounting).
- Custom-error parameter encoding (Verity translates errors as string
  reverts; we compare revert *occurrence* and *selector*, not full bytes).
- Aggregator path (`handleAggregatedOps`) — not in the Verity translation.
- `EntryPoint.simulateValidation` / off-chain helpers — out of scope.
- Dynamic calldata-array decoding and byte-for-byte calldata forwarding are out
  of scope for this projection; those remain Verity ABI support work.

## Running locally

```
bash Benchmark/Cases/ERC4337/EntryPointInvariant/differential/run.sh
```

The `run.sh` target wraps the four pipeline steps above and reports any
divergence as a test failure. CI runs the same target on PRs touching the
EntryPoint benchmark or differential harness.

## What this discharges

Differential testing is empirical, not formal — it cannot replace the
Lean proof. But it gives an independent line of evidence that the compiled
projection reaches the same selected control-flow outcomes as the upstream
EntryPoint on the chosen scenarios. Combined with the Lean proof of
`yoav_counting_biconditional_under_arbitrary_callees`, the residual trust
assumption is narrowed to the explicitly documented projection and ECM
boundaries, not the full Solidity ABI.

A failing test is a model bug. Fix the Verity contract, re-run the proof,
re-run the test.
