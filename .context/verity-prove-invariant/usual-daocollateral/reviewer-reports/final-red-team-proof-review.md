status: pass_with_minor_findings
critical_findings:
- none
major_findings:
- none
minor_findings:
- The proof is ready only for the explicitly scoped protocol slice: direct `swap` / `redeem`, ghosted ERC20/USD0 effects, parameterized oracle values, and theorem-level successful-call arithmetic preconditions. It should not be marketed as full deployed-contract solvency or full USD0/token correctness.
- `Math.mulDiv(..., Floor)` is modeled as `div (mul x y) denominator` plus no-wrap hypotheses. This is disclosed, but it excludes some Solidity-success cases where OpenZeppelin full-precision `mulDiv` could succeed despite `x * y` exceeding 256 bits.
- `redeem_fee_formula` proves the helper formula without a `tokenUnit != 0` well-formedness hypothesis. The main redeem theorem has the nonzero token-unit hypothesis, so this is not blocking.
evidence:
- `lake build Benchmark.Cases.Usual.DaoCollateral.Contract Benchmark.Cases.Usual.DaoCollateral.Specs Benchmark.Cases.Usual.DaoCollateral.Proofs Benchmark.Cases.Usual.DaoCollateral.Compile` passed.
- `python3 scripts/validate_manifests.py` passed: 19 family, 21 implementation, 20 case, 113 task manifests.
- `python3 scripts/check_reference_solutions.py` passed: 20 files checked, no `sorry`/`admit` placeholders in reference solutions.
- `Proofs.lean` contains no local `sorry`/axiom usage and proves five declared tasks: `swap_conservation`, `swap_value_conservation`, `redeem_fee_formula`, `redeem_return_formula`, and `redeem_conservation`.
- Manifests and review matrix disclose the key abstractions: oracle parameterization, ghosted ERC20/USD0 effects, checked-arithmetic preconditions, successful-call preconditions, direct swap/redeem-only scope, and CBR redeem branch modeling.
- Verified-source snippets align with the modeled arithmetic shape: `_calculateFee`, `_burnStableTokenAndTransferCollateral`, `_getTokenAmountForAmountInUSD`, direct `swap`, and direct `redeem` are the relevant selected functions.
required_changes:
- none before final proof readiness, assuming the public claim remains scoped to the documented protocol slice and successful-call hypotheses.
confidence:
- high
