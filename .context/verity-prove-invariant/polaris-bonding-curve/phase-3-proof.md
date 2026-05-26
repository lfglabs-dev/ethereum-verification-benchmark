# Phase 3 - Proof Terminal Result

Terminal condition: PROOF with one trusted helper axiom.

The proof target keeps one explicit axiom in `Benchmark/Cases/Polaris/BondingCurve/Proofs.lean`:

- `trustedCurveHelperOutput_correct`

All four transition results are Lean theorems:

- `init_reserve_ratio_zero`
- `buy_preserves_reserve_ratio_zero`
- `sell_preserves_reserve_ratio_zero`
- `floorSellAndBurn_preserves_reserve_ratio_zero`

They prove successful-path preservation from the executable storage writes, the documented `curveBalance` abstraction, labeled helper-output trust, and bounded-Uint256 assumptions. They do not assume the post-state reserve/curve equality; that equality is established as part of `reserveRatioDeviationZero s'`.

## Why the Axiom Was Used

The executable model builds and the four state-transition preservation theorems discharge. The remaining axiom is the boundary to the Solidity reserve helper:

- `trustedCurveHelperOutput_correct supply reserve`: if the Solidity helper returned `reserve` for `supply`, then `reserve = curveBalance supply`.

This is a modeling boundary, not the reserve-ratio invariant itself. `curveBalance` stands in for `_getBalanceFromReserveRatio`, which is the source helper containing PRB/ABDK pow and rounding. Arithmetic facts that previously appeared as theorem premises are now local lemmas where possible; the remaining premises are bounded Uint256 conditions needed to rule out wraparound/underflow on source-level checked arithmetic.

## Commands

```bash
lake build Benchmark.Cases.Polaris.BondingCurve.Proofs
lake build Benchmark.Cases.Polaris.BondingCurve.Compile
```

Both commands currently succeed.

## Publication Constraint

Any article or benchmark README must describe this as proven under the trusted helper-output axiom, not as a full proof of the exact PRB/ABDK reserve function. It must not say the post-state reserve equation is assumed; it is the theorem conclusion.
