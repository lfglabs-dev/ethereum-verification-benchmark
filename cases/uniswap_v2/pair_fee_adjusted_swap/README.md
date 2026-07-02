## Status

Active benchmark case.

On 2026-03-22, the four reference theorems for
`Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap` were proved and committed in
`Benchmark/Cases/UniswapV2/PairFeeAdjustedSwap/Proofs.lean`.

On 2026-07-02 the case was promoted from the backlog to the active suite and
extended with two harder tasks over the same slice, both with complete hidden
reference proofs:

- `two_swap_k_monotone`: after two sequential fee-adjusted swaps the reserve
  product never decreases (`k' >= k`), under explicit no-overflow hypotheses.
- `swap_sandwich_output_bound`: the output extracted by a victim swap after an
  adversarial same-direction front-run stays within the no-front-run output
  bound derived from the original reserves.

Validation:

```bash
python3 scripts/validate_manifests.py
timeout 600s lake build Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap.Proofs
./scripts/run_task.sh uniswap_v2/pair_fee_adjusted_swap/two_swap_k_monotone
./scripts/run_task.sh uniswap_v2/pair_fee_adjusted_swap/swap_sandwich_output_bound
```

The generated task stubs in
`Benchmark/Generated/UniswapV2/PairFeeAdjustedSwap/Tasks/` contain `exact ?_`
holes; the reference proofs live only in the hidden `Proofs.lean` module.
