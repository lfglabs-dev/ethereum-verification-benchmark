## Status

Active benchmark case.

This case proves the fee-adjusted constant-product curve safety invariant for
1inch Aqua XYCSwap. The theorem shows that the output amount computed by
`_quoteExactIn` satisfies the integer-division rounding bound:

    output * denominator <= feeAdjustedInput * balanceOut

This is the direct analog of the Uniswap V2 K invariant, adapted to XYCSwap's
basis-points fee structure. It proves that no swap can extract more output
tokens than the reserve curve permits.

Validation:

```bash
python3 scripts/validate_manifests.py
time lake build Benchmark.Cases.OneInch.XYCSwapCurveSafety.Proofs
./scripts/run_task.sh 1inch/xycswap_curve_safety/quote_exact_in_curve_safety
```

The generated task stub in
`Benchmark/Generated/OneInch/XYCSwapCurveSafety/Tasks/` contains an `exact ?_`
hole; the reference proof lives only in the hidden `Proofs.lean` module.
