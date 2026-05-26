# Phase 2 - Modelization

## Files

- `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Contract.lean`
- `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Specs.lean`
- `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Proofs.lean`
- `Benchmark/Cases/OneDelta/CallerAddressIntegrity/Compile.lean`
- `Benchmark/Generated/OneDelta/CallerAddressIntegrity/Tasks/*.lean`
- `cases/onedelta/caller_address_integrity/**`
- `families/onedelta/**`

## Model shape

The model is an event-log slice of `OneDeltaComposerEthereum`. It tracks the outer caller, whether each modeled pull occurred, and the `from` argument supplied to ERC20 and Permit2 fund-pull calls. Command classes are reduced to decoded transfer ids:

- `TRANSFER_FROM = 0`
- `PERMIT2_TRANSFER_FROM = 4`

The aggregate theorem uses a fixed all-path execution: direct ERC20 pull,
flash-callback ERC20 pull, swap-callback Permit2 pull, and the V3 direct
callback pull all occur in the same modeled batch. The general invariant
remains event-style: each modeled pull that occurs uses the outer caller.

The modeled slice keeps explicit function boundaries close to the Solidity surface:

- `deltaCompose`
- `_deltaComposeInternal_transferFrom`
- `_deltaComposeInternal_permit2TransferFrom`
- `_transfers_transferFrom`
- `_transfers_permit2TransferFrom`
- `_transferFrom`
- `_permit2TransferFrom`
- `flashLoanCallbackTransferFrom`
- `swapCallbackPermit2TransferFrom`
- `v3SwapCallbackDirectTransferFrom`
- `allModeledPullsHarness`

## Semantics preserved

- `deltaCompose` obtains the caller from `msgSender` and records only the outer caller.
- Every modeled transfer-command path receives the same explicit `callerAddress`.
- Flash-loan and swap callbacks forward that same `callerAddress`.
- ERC20 and Permit2 external call arguments record both occurrence and `callerAddress` as the pull source.
- The V3 callback `calldataLength == 0` shortcut records `callerAddress` as the direct ERC20 pull source.

## Abstractions

- Calldata offsets and loop advancement are represented by decoded transfer-command entrypoints.
- External token calls are represented by occurrence flags plus event-log storage writes.
- Callback authentication and protocol-specific pool validation are outside the proven property.

## Build gate

Completed:

- `lake build Benchmark.Cases.OneDelta.CallerAddressIntegrity.Contract`
- `lake build Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs`
- `lake build Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs`
- `lake build Benchmark.Cases.OneDelta.CallerAddressIntegrity.Compile`
- `lake build`

Result: all commands completed successfully. The full `lake build` emitted
pre-existing warnings in unrelated benchmark cases, but no 1delta errors.
