# Invariant Review

status: fixed

critical_findings: none

major_findings:
- Initial fee/return specs were too close to helper definitions.
- Initial `swap_value_conservation_spec` only used the value formula as an implication antecedent.
- Checked arithmetic and successful-call assumptions were missing from theorem interfaces.

resolution:
- Added explicit `expectedFeeUsd0`, `expectedReturnedCollateral`, and `expectedSwapUsdQuote` expressions in `Specs.lean`.
- Strengthened `swap_value_conservation_spec` so the postcondition includes the expected quote as the minted USD0 delta.
- Added `successfulSwapArithmetic` and `successfulRedeemArithmetic` preconditions covering nonzero quote, uint128 amount bound, no-wrap products/additions, fee bounds, supply/collateral debit bounds, and DaoCollateral fee/CBR configuration bounds.

evidence:
- `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` passes.
- Task metadata now discloses `successful_call_preconditions`.

confidence: high
