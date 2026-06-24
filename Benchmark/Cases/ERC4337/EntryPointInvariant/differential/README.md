# EntryPoint v0.9 differential test harness

This directory contains the differential-testing scaffold for the
Verity-compiled `EntryPointV09` ABI path and the original `EntryPoint.sol`
v0.9 bytecode. The generated Verity bytecode accepts Solidity's real
`handleOps(PackedUserOperation[],address)` calldata selector and decodes that
payload into the current proof model. The older flattened one-op projection is
still emitted by the Verity contract, but the differential tests no longer call
it as a substitute for the upstream ABI.

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

`EntryPointDifferential.t.sol` deploys both bytecodes at fresh addresses. Both
the original EntryPoint and the Verity artifact are exercised through the same
`IEntryPoint.handleOps(PackedUserOperation[] calldata,address payable)` ABI.
The generated Verity runtime also exposes the upstream setup views used by the
Hardhat suite smoke path: `senderCreator()`, `depositTo(address)`,
`balanceOf(address)`, `getDepositInfo(address)`, `getNonce(address,uint192)`,
`getSenderAddress(bytes)`, `getUserOpHash(PackedUserOperation)`, and
`getCurrentUserOpHash()` as supported by the Verity model. On the upstream ABI
path, Verity #2057 generates the dynamic tuple-array decoder for
`handleOps(PackedUserOperation[],address)` directly. The runner no longer
injects a post-Yul `handleOps` case; it only links the `createSender` external
adapter and patches the receive/deposit fallback used by the focused
differential tests. Full gas accounting and the complete simulation surface
remain compatibility targets.

## Test scope

We test the subset of the upstream suite that exercises the validation /
execution control flow — exactly what the Yoav-grade biconditional cares
about:

| Test | Asserts |
|------|---------|
| `testValidateAndExecuteSingleOp` | one op, callData non-empty: upstream executes once; Verity ABI path reaches its execution path without revert |
| `testNonceReplayRejected` | re-submitting the same `(sender, nonce)` reverts |
| `testReentrancyBlocked` | re-entry into each entry point reverts |
| `testEmptyCallDataNoExec` | op with empty callData: neither path records a sender execution call |

Out of scope (documented divergences, ignored in assertions):

- Full gas accounting (the Verity model only implements the focused unused-gas
  paymaster penalty/payment slice used by the upstream smokes).
- Full prefund economics (the shim models the focused low-gas prefund branch
  used by upstream smoke tests, not the complete gas schedule).
- Custom-error parameter encoding (Verity translates some projection errors as
  string reverts; we compare revert occurrence and ABI-path behavior, not full
  custom-error payload parity yet).
- Exact custom-error artifact recognition for the raw Verity EntryPoint
  bytecode. The aggregation shim currently surfaces `SignatureValidationFailed`
  as a matcher-compatible reason string because Hardhat does not recognize
  Verity bytecode as the Solidity EntryPoint artifact.
- Full `EntryPoint.simulateValidation` / off-chain helper coverage beyond the
  paymaster stake/delay smoke.
- The ABI shim decodes the fields needed by the current proof projection:
  sender, nonce key/sequence, initCode presence, callData presence, paymaster
  presence/address, and beneficiary. Full byte-for-byte forwarding of every
  dynamic field remains a named refinement obligation.

## Running locally

```
bash Benchmark/Cases/ERC4337/EntryPointInvariant/differential/run.sh
```

The `run.sh` target wraps the four pipeline steps above and reports any
divergence as a test failure. CI runs the same target on PRs touching the
EntryPoint benchmark or differential harness.

## Upstream Hardhat Smokes

After `run.sh` has produced `build/differential/verity-solc.out`, a focused
set of original upstream tests can be run against the Verity bytecode with the
upstream TypeScript ABI:

```
VERITY_BYTECODE=$(awk '/Binary representation:/{getline; print; exit}' \
  build/differential/verity-solc.out)
(
  cd ../account-abstraction-upstream
  VERITY_ENTRYPOINT_BYTECODE=0x$VERITY_BYTECODE \
  MNEMONIC_FILE=/tmp/nonexistent-mnemonic \
  corepack yarn hardhat test test/entrypoint.test.ts --grep '<test name>'
)
```

Currently passing upstream smoke names:

- `should deposit for transfer into EntryPoint`
- `should revert on signature failure`
- `account should pay for tx`
- `handleOps should fail with zero-address paymaster`
- Paymaster subset probe: `should fail with nonexistent paymaster`
- `should fail if paymaster has no deposit`
- `should not revert when paymaster reverts with custom error on postOp`
- `should not revert when paymaster reverts with known EntryPoint error in postOp`
- `simulateValidation should return paymaster stake and delay`
- `paymaster should pay for tx including unused gas penalty`
- `paymaster should pay for tx including unused execution and postOp gas penalties`
- `without paymaster` under `should pay prefund and revert account if prefund is not enough`
- `should expose the currentUserOpHash to the execution`
- `with paymaster` under `should pay prefund and revert account if prefund is not enough`
- Validation time-range block:
  `should accept non-expired owner`
- Validation time-range block:
  `should not reject expired owner`
- Validation time-range block:
  `should accept non-expired paymaster request`
- Validation time-range block:
  `should not reject expired paymaster request`
- Validation time-range block:
  `should revert on expired account`
- Validation time-range block:
  `should revert on date owner`
- Validation time-range block:
  `should revert on expired account block range`
- Validation time-range block:
  `should accept account with valid block range`
- Validation time-range block:
  `should revert on expired paymaster block range`
- Validation time-range block:
  `should accept paymaster with valid block range`
- `should fail with AA23 if account reverts`
- `should fail with AA23 and original error if account reverts`
- `should pay for reverted tx`
- `account should not pay if too low gas limit was set`
- `should fail with AA20 if account not deployed`
- `should report failure on insufficient verificationGas after creation`
- `account should pay a penalty for unused gas only above threshold`
- `should reject create if sender address is wrong`
- `should reject create if account not funded`
- `should succeed to create account after prefund`
- `should accept and ignore initCode if account already created`
- Aggregation block:
  `should fail to execute aggregated account without an aggregator`
- Aggregation block:
  `should fail to execute aggregated account with wrong aggregator`
- Aggregation block:
  `should reject non-contract (address(1)) aggregator`
- Aggregation block:
  `should fail to execute aggregated account with wrong agg. signature`
- Aggregation block:
  `should run with multiple aggregators (and non-aggregated-accounts)`
- Aggregation block:
  `simulateValidation should return aggregator and its stake`
- Aggregation block:
  `should create account in handleOps`

These smokes are intentionally narrow: they prove the original Hardhat stack can
deploy Verity bytecode, connect it as `EntryPoint`, call the upstream setup
views, send ETH through the receive path, validate a real `SimpleAccount`
operation, reject a bad signature through the real account ABI, forward account
execution calldata, derive/create counterfactual senders through `initCode`,
reach real paymaster validation and postOp calls, observe canonical
`UserOperationEvent`/`PostOpRevertReason` logs, and move modeled paymaster
deposits/beneficiary ETH for the unused-gas penalty slice. They also cover the
direct `SenderCreator.createSender` custom error and the upstream aggregation
block, including aggregate signature validation failure, wrong aggregator
rejection, multi-aggregator event ordering, and aggregated account creation.
They also cover the focused non-paymaster prefund-too-low path and
`getCurrentUserOpHash()` during account execution, plus the upstream validation
time-range block for account and paymaster validation data. The focused AA23
validation-revert wrapping and reverted execution payment smokes also pass. They
also cover focused AA20/AA95/low-verification-gas aborts and the non-paymaster
unused-gas penalty event-field smoke. They are not yet a claim that the full
upstream suite passes.

Known upstream gaps after the current smoke set include broader gas accounting
and penalty precision, full simulation coverage, and exact custom-error artifact
recognition for Verity EntryPoint bytecode.

## What this discharges

Differential testing is empirical, not formal — it cannot replace the
Lean proof. But it gives an independent line of evidence that the compiled ABI
path reaches the same selected control-flow outcomes as the upstream EntryPoint
on the chosen scenarios. Combined with the Lean proofs
`abi_backed_yoav_counting_biconditional` and
`yoav_counting_biconditional_under_arbitrary_callees`, the residual trust
assumption is narrowed to the ABI shim's decoded-field projection and the
explicit ECM boundaries.

A failing test is a model bug. Fix the Verity contract, re-run the proof,
re-run the test.
