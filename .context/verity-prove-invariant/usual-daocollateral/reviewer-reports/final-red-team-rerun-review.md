status: pass_with_minor_findings
critical_findings:
- none
major_findings:
- none
minor_findings:
- The proof remains scoped to direct swap/redeem only, with oracle values and token effects parameterized/ghosted. This is disclosed and not blocking.
- `Math.mulDiv(..., Floor)` is modeled as `div (mul x y) denominator` with no-wrap hypotheses, so full-precision `mulDiv` success cases with overflowing intermediate products are outside scope.
- `tokenUnit` is treated as an explicit parameter, not constrained to a power-of-ten decimal unit in every helper theorem. Main redeem proofs require `tokenUnit != 0`; this is a fidelity boundary, not a proof blocker.
evidence:
- `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` completed successfully.
- `Proofs.lean` contains five reference declarations: `swap_conservation`, `swap_value_conservation`, `redeem_fee_formula`, `redeem_return_formula`, `redeem_conservation`.
- No reference-proof `sorry`, `admit`, local `axiom`, or `?_` placeholders found in `Benchmark/Cases/Usual/DaoCollateral/Proofs.lean`.
- `Contract.lean` records proxy `0xde6e1F680C4816446C8D515989E2358636A38b04`, implementation `0x0eEc861D49f15F585D6Bb4301FC4f89BCe22AF4e`, oracle/decimal parameterization, ghosted ERC20/USD0 effects, CBR, fee, floor rounding, and successful-call preconditions.
- Sourcify verified source confirms the reviewed direct `swap`, `redeem`, `_calculateFee`, `_burnStableTokenAndTransferCollateral`, `_getTokenAmountForAmountInUSD`, `Normalize`, and constants paths.
- Article table lists exactly the five `Proofs.lean` declarations, all `Proven`.
- Article has `<Disclosure title="Verify it yourself"...>` immediately after the proof table.
required_changes:
- none
confidence:
- high
