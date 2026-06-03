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
- `alpha`
- `bPlusOne`

## Simplifications

- `_getBalanceFromReserveRatio` is modeled through its source-shaped outer arithmetic:
  `(A * pow(supply, B_PLUS_1) + DECIMAL_PRECISION - 1) / B_PLUS_1`.
  Executable transitions receive only the raw fixed-point `pow` result because
  `curvePow` is the opaque PRB/ABDK boundary. The model computes the helper's
  multiplication and decimal-precision rounding division itself.
- ERC20 per-account balances and reserve-token custody are omitted. Aggregate `totalSupply` is kept because it determines `virtualSupply`.
- External calls and token transfers are omitted from the state transition because the selected invariant is the contract's own curve-point deviation check, not token custody.
- Caller-dependent behavior is represented by successful-path inputs: `buy`
  carries the fee-router branch through a caller marker plus fee amount
  hypothesis, and `floorSellAndBurn` carries the fee-router authorization guard.
- `initialized` abstracts the source condition `initializerAccount == address(0)`
  after `init` deletes the initializer. Buy/sell slippage checks are omitted
  because they do not write the reserve checkpoints; this widens the successful
  path for invariant preservation. The buy nonzero guard and burn-supply guards
  model checks reached through source helper/ERC20 paths.
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

The main semantic risk is still the fixed-point exponentiation abstraction. The
model no longer uses an identity reserve helper or broad helper-output input.
Init, buy, sell, and floor-burn preservation now prove operation-level storage
alignment from the modeled helper outer arithmetic plus bounded Uint256
arithmetic assumptions. The public claim must say the current terminal result
proves operation-level preservation with no custom Lean axioms but under
explicit raw pow-output preconditions, not the full PRB/ABDK pow formula.

## Review Resolution

Phase 2 modelization review initially blocked the identity-helper encoding and several missing successful-path guards. The model was updated to:

- replace `curveBalance supply := supply` with source-shaped helper outer arithmetic;
- represent computed pow values with `trustedCurvePowOutput` instead of trusting
  the whole reserve helper output;
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

## Source Traceability Notes

At upstream commit `540c4ba5d0b86c0f42399d214f02120f3f8719b0`,
`BaseBondingCurve.sol` computes `_getBalanceFromReserveRatio` at lines 388-391
as `left = _getReserveRatioLeftFormula(_supply)` followed by
`(left + DECIMAL_PRECISION - 1) / B_PLUS_1`. `_getReserveRatioLeftFormula`
is `A * pow(_supply, B_PLUS_1)` at lines 394-397.

`floorSellAndBurn` computes `newFloorSupply = initialFloorSupply +
_bcTokenAmount` and then reaches `_getBalanceFromReserveRatio(newFloorSupply)`
through `getSellAmountFromFloorUpwards` at lines 261-295. The model writes the
new floor balance directly to that helper value, which is equivalent under the
pre-state floor checkpoint alignment.
