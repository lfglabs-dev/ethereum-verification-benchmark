# Phase 3 - Proof Terminal Result

Terminal condition: PROOF with zero Lean axioms and an explicit raw pow-output precondition.

The broad helper-output boundary has been removed. The model no longer accepts
`_getBalanceFromReserveRatio` balances as trusted inputs. Instead, each
transition receives only the raw fixed-point `pow` output for the target supply,
then computes the helper's outer arithmetic directly:

```text
left = A * pow(supply, B_PLUS_1)
balance = (left + DECIMAL_PRECISION - 1) / B_PLUS_1
```

In Lean this residual boundary is:

```lean
trustedCurvePowOutput s supply powOut :=
  powOut = curvePow supply (bPlusOneOf s)
```

All four transition results are Lean theorems:

- `init_reserve_ratio_zero`
- `buy_preserves_reserve_ratio_zero`
- `sell_preserves_reserve_ratio_zero`
- `floorSellAndBurn_preserves_reserve_ratio_zero`

They prove successful-path preservation from the executable storage writes,
modeled helper multiplication and decimal-precision rounding division, explicit
raw pow-output preconditions, and bounded-Uint256 assumptions. They do not assume the whole
post-state invariant, and they no longer assume the reserve helper's final
balance output.

## Residual Pow Boundary

The remaining boundary is not a Lean axiom, but it is semantically important:

- `curvePow supply bPlusOne`: opaque model of the concrete PRB/ABDK fixed-point
  exponentiation implementation.
- `trustedCurvePowOutput s supply powOut`: the supplied raw pow result equals
  that opaque `curvePow` value for the relevant supply and exponent.

This is narrower than the earlier helper-output precondition. The benchmark now
models `A * pow(...)` and the source rounding division path, but it still does not
bit-prove PRB `SD59x18.pow`, ABDK `exp_2(log_2(...))`, or their rounding and
revert behavior.

## Verity Gap / Issue Draft

Pinned Verity revision: `9eaf64218be14b59f6253219c111a5abf958e7b7`.

Observed support in the current repo:

- `verity_contract` rejects opaque Lean helper calls in executable bodies; the
  direct `curvePow` call failed at `Contract.lean:89` with "unsupported
  expression in verity_contract body".
- `Verity.Stdlib.Math` and existing cases cover word-level arithmetic,
  rounding division, and `mulDiv`-style integer helpers.
- `Benchmark/Cases/Reserve/AuctionPriceBand/Contract.lean` keeps PRB
  fixed-point `exp` / `ln` as explicit opaque boundaries.

Missing feature for this case:

- A faithful library-level model and proof surface for PRB `SD59x18.pow` and
  ABDK `64x64` pow, including fixed-point scaling, `log2` / `exp2` approximation
  steps, rounding, overflow/revert guards, and bridge lemmas into Verity
  executable models.

Proposed upstream issue:

> Add Verity fixed-point math models for PRB `SD59x18.pow` and ABDK 64x64
> exponentiation.
>
> Polaris `BaseBondingCurve._getReserveRatioLeftFormula` computes
> `A * pow(_supply, B_PLUS_1)`. The current Verity surface can model the outer
> multiplication and `(left + DECIMAL_PRECISION - 1) / B_PLUS_1` division, but it does not provide a faithful PRB or
> ABDK fixed-point `pow` model with `log2` / `exp2` approximation steps, scaling,
> rounding, and revert-condition lemmas. Add reusable models and bridge lemmas so
> benchmark cases can prove the raw pow output directly rather than using an
> explicit pow-output precondition.

## Commands

```bash
lake build Benchmark.Cases.Polaris.BondingCurve.Proofs
lake build Benchmark.Cases.Polaris.BondingCurve.Compile
```

Focused proof target currently succeeds.

## Publication Constraint

Any article or benchmark README must describe this as proven with zero Lean
axioms under explicit raw pow-output preconditions. It must not market the case
as a bit-level proof of PRB/ABDK fixed-point exponentiation, protocol solvency,
reserve-token custody, or ERC-20 user balances.
