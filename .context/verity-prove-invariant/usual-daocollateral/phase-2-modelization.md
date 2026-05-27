# Phase 2 - Modelization

Artifacts:

- `Benchmark/Cases/Usual/DaoCollateral/Contract.lean`
- `Benchmark/Cases/Usual/DaoCollateral/Specs.lean`
- `Benchmark/Cases/Usual/DaoCollateral/Compile.lean`
- `cases/usual/dao_collateral/verity/{Contract,Specs,Compile}.lean`

The model preserves the source function boundaries relevant to conservation:
`swap`, `_calculateFee`, `_burnStableTokenAndTransferCollateral`, and
`_getTokenAmountForAmountInUSD` are represented by `swapDirect`,
`redeemFeeAmount`, `redeemDirect`, `tokenAmountForUsd`, and
`cbrAdjustedTokenAmount`.

Build commands required by the skill:

```bash
lake build Benchmark.Cases.Usual.DaoCollateral.Contract
lake build Benchmark.Cases.Usual.DaoCollateral.Specs
lake build
```

Current status: `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` completed successfully after adding explicit successful-call hypotheses for checked arithmetic, quote bounds, treasury collateral sufficiency, and DaoCollateral configuration bounds.
