# Phase 3 - Proof Terminal Result

Terminal condition: PROOF with zero Lean axioms and an explicit helper-output precondition.

The prior broad helper axiom `trustedCurveHelperOutput_correct` has been removed.
`trustedCurveHelperOutput supply reserve` is now a definition in `Specs.lean`:
`reserve = curveBalance supply`.

All four transition results are Lean theorems:

- `init_reserve_ratio_zero`
- `buy_preserves_reserve_ratio_zero`
- `sell_preserves_reserve_ratio_zero`
- `floorSellAndBurn_preserves_reserve_ratio_zero`

They prove successful-path preservation from the executable storage writes, the documented `curveBalance` abstraction, labeled helper-output preconditions, and bounded-Uint256 assumptions. They do not assume the whole post-state invariant; that invariant is established as part of `reserveRatioDeviationZero s'`.

## Residual Helper Boundary

The executable model builds and the four state-transition preservation theorems discharge with no Lean axiom. The remaining boundary is not an axiom, but it is still semantically important:

- `trustedCurveHelperOutput supply reserve`: the helper output supplied to the modeled transition equals `curveBalance supply`.

This is a modeling boundary, not the reserve-ratio invariant itself. `curveBalance` stands in for `_getBalanceFromReserveRatio`, which is the source helper containing PRB/ABDK pow and rounding. The benchmark does not bit-prove PRB/ABDK `SD59x18.pow`, `log2`, `exp2`, or the integer ceil division path. Arithmetic facts that previously appeared as theorem premises are now local lemmas where possible; the remaining premises are bounded Uint256 conditions needed to rule out wraparound/underflow on source-level checked arithmetic.

## Verity Gap / Issue Draft

Pinned Verity revision: `9eaf64218be14b59f6253219c111a5abf958e7b7`.

Observed support in `.lake/packages/verity/`:

- `Verity/Macro/Translate.lean` recognizes ordinary word-level `pow` and `ceilDiv`.
- `Contracts/Smoke.lean` documents 512-bit `mulDiv512Down` / `mulDiv512Up` helpers for OpenZeppelin/Solmate-style integer full-precision division.
- `AXIOMS.md` records EVM arithmetic and selected helper bridge coverage, including ordinary arithmetic, `ceilDiv`, and `mulDiv*` helpers.

Missing feature for this case:

- A faithful library-level model and proof surface for PRB `SD59x18.pow`, including signed 59.18 fixed-point scaling, PRB `log2` iterative approximation, `exp2` reconstruction, overflow/revert guards, and final conversion to the unsigned helper value consumed by Polaris.

Proposed upstream issue:

> Add a Verity fixed-point math library model for PRB `SD59x18.pow`.
>
> Polaris `BaseBondingCurve._getReserveRatioLeftFormula` computes `A * pow(_supply, B_PLUS_1)` through `PRBBondingCurve.pow`, which wraps PRB `SD59x18.pow(base, exponent)`. The current Verity surface can model word-level `pow`, `ceilDiv`, and 512-bit integer `mulDiv`, but it does not provide a faithful PRB signed fixed-point `pow` model with `log2`/`exp2` approximation steps, scaling, rounding, and revert-condition lemmas. Add a reusable model and bridge lemmas so benchmark cases can prove `_getBalanceFromReserveRatio(supply) = ceil(A * pow(supply, B + 1) / (B + 1))` directly instead of using an explicit helper-output precondition.

## Commands

```bash
lake build Benchmark.Cases.Polaris.BondingCurve.Proofs
lake build Benchmark.Cases.Polaris.BondingCurve.Compile
```

Both commands currently succeed.

## Publication Constraint

Any article or benchmark README must describe this as proven with zero Lean axioms but under explicit helper-output preconditions, not as a full proof of the exact PRB/ABDK reserve function. It must not say the whole post-state invariant is assumed.
