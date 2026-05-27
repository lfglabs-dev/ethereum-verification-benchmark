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
`cbrAdjustedTokenAmount`. `swapDirect` now computes the swap quote from explicit
oracle price and supported token-unit inputs rather than accepting a free quote
parameter. The state variables that stand in for external token effects are
named `ghostUsd0Supply` and `ghostTreasuryCollateral` so the model surface does
not imply real ERC20/USD0 balance verification.

Build commands required by the skill:

```bash
lake build Benchmark.Cases.Usual.DaoCollateral.Contract
lake build Benchmark.Cases.Usual.DaoCollateral.Specs
lake build
```

Current status: `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` completed successfully after adding explicit successful-call hypotheses for checked arithmetic, quote bounds, ghost collateral sufficiency, and DaoCollateral configuration bounds.
