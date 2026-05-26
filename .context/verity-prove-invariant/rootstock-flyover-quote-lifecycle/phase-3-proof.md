# Phase 3 Proof: Rootstock Flyover Quote Lifecycle

## Terminal condition

PROOF.

The reference solution is in
`Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Proofs.lean`.

## Theorems

- `depositPegOut_registers_required_amount`
- `refundPegOut_conserves_quote_amount`
- `refundUserPegOut_conserves_quote_amount`

## Proof strategy

The proofs unfold the executable Verity model and the readable specs, then
simplify the successful path under the explicit source-aligned preconditions:

- quote is fresh for deposit through `quoteRegistered == 0`
- quote is registered for refunds through `quoteRegistered == completedFlag`
- quote is incomplete through `quoteCompleted == 0`
- deposit value covers `value + callFee + gasFee`
- checked-addition successful paths hold for deposit required amount, LP
  penalty timing, and fallback balance credits

The refund proofs split on the modeled external transfer result and, for LP
refund, on the modeled penalty branch. In the failed-transfer branch they prove
that the recipient-keyed fallback balance increases by the deposited quote
amount. The slash proof obligation is scoped to `slashCallAmount`, a local
witness that the external collateral slash call is reached with the expected
penalty input; it does not claim to prove CollateralManagement storage.

## Commands run

```bash
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Contract
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Proofs
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Compile
lake build Benchmark.Generated.Rootstock.FlyoverQuoteLifecycle.Tasks.DepositPegOutRegistersRequiredAmount Benchmark.Generated.Rootstock.FlyoverQuoteLifecycle.Tasks.RefundPegOutConservesQuoteAmount Benchmark.Generated.Rootstock.FlyoverQuoteLifecycle.Tasks.RefundUserPegOutConservesQuoteAmount
lake build
```

All commands completed successfully. The full `lake build` emitted warnings from
pre-existing non-Rootstock cases, but no Rootstock warnings or errors remained.
