# Phase 2 - Modelization

## Files

- `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`
- `Benchmark/Cases/Polaris/BondingCurve/Specs.lean`
- `Benchmark/Cases/Polaris/BondingCurve/Proofs.lean`
- `Benchmark/Cases/Polaris/BondingCurve/Compile.lean`
- `Benchmark/Generated/Polaris/BondingCurve/Tasks/*.lean`
- `cases/polaris/bonding_curve/**`
- `families/polaris/**`

## Modeled Solidity Surface

The model targets `BaseBondingCurve` at commit `540c4ba5d0b86c0f42399d214f02120f3f8719b0`.

Modeled functions:

- `init`
- `buy`
- `sell`
- `floorSellAndBurn`

Modeled storage:

- `virtualBalance`
- `floorSupply`
- `floorBalance`
- aggregate `totalSupply`
- `feePercentage`
- `initialized`

## Simplifications

- `_getBalanceFromReserveRatio` is represented by opaque `curveBalance : Uint256 -> Uint256`. The executable transition functions receive the Solidity helper's computed result as an input, and theorem hypotheses tie that value to `curveBalance` at the resulting supply. This avoids treating the reserve helper as an identity function while keeping PRB/ABDK fixed-point exponentiation outside the executable model.
- ERC20 per-account balances and reserve-token custody are omitted. Aggregate `totalSupply` is kept because it determines `virtualSupply`.
- External calls and token transfers are omitted from the state transition because the selected invariant is the contract's own curve-point deviation check, not token custody.
- Caller-dependent behavior is represented by successful-path inputs: `buy` carries the fee-router branch through a caller marker plus fee amount hypothesis, and `floorSellAndBurn` carries the fee-router authorization guard.
- Solidity checked arithmetic is represented as theorem hypotheses.

## Build Results

Commands run:

```bash
lake build Benchmark.Cases.Polaris.BondingCurve.Contract
lake build Benchmark.Cases.Polaris.BondingCurve.Specs
lake build Benchmark.Cases.Polaris.BondingCurve.Proofs
lake build Benchmark.Cases.Polaris.BondingCurve.Compile
```

Current result: all four targets build.

`lake build Benchmark.Cases` replayed existing repository targets and reached
`Built Benchmark.Cases.Polaris`, confirming the aggregate import for the new
case. It was then interrupted in an unrelated pre-existing
`PaladinVotes/StreamRecoveryClaimUsdc/Proofs.lean` tail under shared
environment contention.

## Known Risk

The main semantic risk is still the fixed-point exponentiation abstraction. The model no longer uses an identity reserve helper; it assumes the source helper output as an explicit transition input and proves/axiomatizes preservation under hypotheses that bind that input to opaque `curveBalance`. The public claim must say the current terminal result proves operation-level preservation under this abstraction, not the full PRB/ABDK pow formula.

## Review Resolution

Phase 2 modelization review initially blocked the identity-helper encoding and several missing successful-path guards. The model was updated to:

- replace `curveBalance supply := supply` with an opaque `curveBalance`;
- pass computed helper results into `init`, `buy`, `sell`, and `floorSellAndBurn`;
- add source-aligned nonzero amount guards for `buy`, net-amount `sell`, and `floorSellAndBurn`;
- add the `buy` fee-router branch as an explicit fee amount hypothesis;
- add `floorSellAndBurn` fee-router authorization as a transition guard;
- remove the direct `initialized` guard from `sell`, matching the Solidity surface.

The init model intentionally scopes out one-time deployment authority and curve
parameterization semantics: initializer authorization, deletion of
`initializerAccount`, `_alpha` override behavior, `A == 0`, and `A > MIN_ALPHA`.
The benchmark starts from the successful initialized curve-parameter path and
tracks the storage variables needed for the selected reserve-ratio invariant.

The Verity reviewer confirmed the opaque-helper-in-contract-body limitation is real, but storage normalization and Uint256 cancellation should be described as unresolved proof obligations in this benchmark, not general Verity defects.
