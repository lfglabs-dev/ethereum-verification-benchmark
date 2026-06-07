# EntryPoint v0.9 differential test harness

This directory contains the differential-testing scaffold that compares the
Verity-compiled `EntryPointV09` bytecode against the original
`EntryPoint.sol` v0.9 compiled by solc. The goal is empirical
certification of the hand translation: same input → same output for every
test case.

## Pipeline

1. Compile the Verity source:
   ```
   verity-cli compile \
     --case Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09 \
     --emit yul \
     --output build/EntryPointV09.yul
   ```
2. Compile the Yul output to EVM bytecode:
   ```
   solc --strict-assembly build/EntryPointV09.yul \
        --bin --bin-runtime \
        -o build/
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

`EntryPointDifferential.t.sol` is the Foundry test that deploys both bytecodes
at fresh addresses and asserts equivalent behaviour across the chosen test
scenarios. This directory is a self-contained Foundry project; the test uses a
minimal local cheatcode/assertion interface instead of depending on
`forge-std`.

## Test scope

We test the subset of the upstream suite that exercises the validation /
execution control flow — exactly what the Yoav-grade biconditional cares
about:

| Test | Asserts |
|------|---------|
| `testValidateAndExecuteSingleOp` | one op, callData non-empty: sender called once with op.callData |
| `testNonceReplayRejected` | re-submitting the same `(sender, nonce)` reverts |
| `testPaymasterRejectedReverts` | paymaster returning a failure word reverts the whole batch |
| `testReentrancyBlocked` | callee re-entering `handleOps` reverts with the guard message |
| `testEmptyCallDataNoExec` | op with empty callData: no `Exec.call` is recorded |
| `testHandleOpsBatchPreservesOrder` | execution events match validation order |

Out of scope (documented divergences, ignored in assertions):

- Gas costs (the Verity model elides gas accounting).
- Custom-error parameter encoding (Verity translates errors as string
  reverts; we compare revert *occurrence* and *selector*, not full bytes).
- Aggregator path (`handleAggregatedOps`) — not in the Verity translation.
- `EntryPoint.simulateValidation` / off-chain helpers — out of scope.

## Running locally

```
bash Benchmark/Cases/ERC4337/EntryPointInvariant/differential/run.sh
```

The `Makefile` target wraps the four pipeline steps above and reports any
divergence as a test failure. CI runs the same target on PRs touching
`Benchmark/Cases/ERC4337/EntryPointInvariant/EntryPointV09.lean`.

## What this discharges

Differential testing is empirical, not formal — it cannot replace the
Lean proof. But it gives an independent line of evidence: the
hand-translated Verity contract behaves identically to the original
Solidity contract on the chosen scenarios. Combined with the Lean proof
of `yoav_counting_biconditional_under_arbitrary_callees`, the residual
trust assumption "the hand translation is faithful" is reduced to
"on the chosen scenarios, the hand translation matches solc output
byte-for-byte (modulo documented divergences)."

A failing test is a model bug. Fix the Verity contract, re-run the proof,
re-run the test.
