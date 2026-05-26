# Phase 2 Modelization: Rootstock Flyover Quote Lifecycle

## Files

- `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Contract.lean`
- `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Specs.lean`
- `Benchmark/Cases/Rootstock/FlyoverQuoteLifecycle/Compile.lean`
- `cases/rootstock/flyover_quote_lifecycle/verity/{Contract,Specs,Compile}.lean`

## Model scope

The model keeps the storage effects of `depositPegOut`, `refundPegOut`, and
`refundUserPegOut`. It tracks the registered quote amount, quote-existence
flag, completion flag, direct LP assignment, direct user assignment,
recipient-keyed internal fallback balance, and explicit collateral slash call
amount. It also stores the quote deposit timestamp so the LP penalty branch is
computed from the same timing inputs used by Solidity.

The source contract calls external systems for provider registration, signature
checking, Bitcoin transaction validation, bridge confirmations, and collateral
management. The Verity model represents those as successful-path preconditions
or explicit inputs where their outcome affects accounting. `depositPegOut`
models both overpayment paths: below-dust change is retained, while change at
or above `dustThreshold` requires a successful change refund.

## Storage mapping

- slot 0: `quoteAmount`
- slot 1: `quotePenalty`
- slot 2: `quoteCompleted`
- slot 3: `lpPaid`
- slot 4: `userPaid`
- slot 5: `internalBalance`
- slot 6: `slashCallAmount`
- slot 7: `quoteRegistered`
- slot 8: `quoteDepositTimestamp`

## Spec alignment

`Specs.lean` exposes helper names intended to be readable in the public article:

- `depositedAmount`
- `penaltyAmount`
- `completed`
- `paidToLp`
- `paidToUser`
- `fallbackBalance`
- `slashCallAmountOf`
- `registered`
- `depositTimestampOf`
- `slashCallMatchesPenalty`

The three theorem-facing specs are:

- `depositPegOut_registers_required_amount_spec`
- `refundPegOut_conserves_quote_amount_spec`
- `refundUserPegOut_conserves_quote_amount_spec`

## Build notes

The build gates completed successfully:

```bash
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Contract
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Specs
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Proofs
lake build Benchmark.Cases.Rootstock.FlyoverQuoteLifecycle.Compile
lake build
```

The full repository build emitted warnings from pre-existing non-Rootstock
cases; the Rootstock case built without warnings after proof simplification
cleanup.

## Review-driven corrections

The phase-1 reviewers identified that fallback balances must be recipient-keyed
like Solidity `_balances`, and that quote existence must not be inferred from a
nonzero amount. The model was updated accordingly: refund functions now take
the LP/user recipient address and credit `internalBalance recipient` with
`oldBalance + amount` on failed transfers; `quoteRegistered` models the
`quote.lbcAddress != address(0)` existence check.

Phase-2 reviewers identified three fidelity issues: deposit overpayment change
refunds, checked arithmetic, and an unconstrained LP penalty Boolean. The model
now includes `dustThreshold`, `changeRefundSucceeds`, deposit timestamp storage,
guarded checked additions for the required amount, and a computed penalty
predicate over confirmation and expiry timing inputs. The penalty timing
additions and `_increaseBalance` fallback balance additions now have explicit
no-overflow successful-path guards. `refundUserPegOut` no longer has a separate
completed precondition in either the model or theorem; successful quote
existence is tracked through `quoteRegistered`, matching the deleted-quote
behavior.
