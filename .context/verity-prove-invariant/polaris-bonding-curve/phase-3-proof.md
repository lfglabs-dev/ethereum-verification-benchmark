# Phase 3 - Proof Terminal Result

Terminal condition: AXIOM.

The proof target builds with four explicit axioms in `Benchmark/Cases/Polaris/BondingCurve/Proofs.lean`:

- `init_reserve_ratio_zero`
- `buy_preserves_reserve_ratio_zero`
- `sell_preserves_reserve_ratio_zero`
- `floorSellAndBurn_preserves_reserve_ratio_zero`

Each axiom states the successful-path transition preserves the curve-balance alignment corresponding to zero reserve-ratio deviation under the documented `curveBalance` abstraction.

## Why Axioms Were Used

The executable model builds, but the proof loop did not discharge two proof obligations within this benchmark:

- Storage-write normalization over multiple slots required manual slot-equality rewriting.
- Uint256 `sub`/`add` cancellation required more detailed no-underflow and no-overflow lemmas for the exact storage terms.

These are unresolved proof-work items here, not established Verity limitations. The larger semantic abstraction remains fixed-point exponentiation. `curveBalance` stands in for `_getBalanceFromReserveRatio`, which is the source helper containing PRB/ABDK pow, and transition axioms require helper-output hypotheses tying computed values back to that opaque function.

## Commands

```bash
lake build Benchmark.Cases.Polaris.BondingCurve.Proofs
lake build Benchmark.Cases.Polaris.BondingCurve.Compile
```

Both commands currently succeed.

## Publication Constraint

Any article or benchmark README must describe this as proven with assumptions/axioms, not as a full proof of the exact PRB/ABDK reserve function. It must not claim that storage normalization or Uint256 cancellation are missing Verity features.
