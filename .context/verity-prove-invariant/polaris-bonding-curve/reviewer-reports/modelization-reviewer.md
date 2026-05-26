# Modelization Reviewer Report

status: pass_with_minor_findings

critical_findings:
- The original model used `curveBalance supply := supply`, so it proved a reserve-coordinate identity rather than the Solidity `_getBalanceFromReserveRatio` relation.
- The four terminal results remain axioms and must be presented as AXIOM terminal results.

major_findings:
- `buy` missed the fee-router caller branch.
- `init` omitted several source-path constraints, including nonzero floor supply.
- `sell` and `floorSellAndBurn` missed nonzero amount checks.
- `floorSellAndBurn` omitted fee-router authorization.
- Re-review found `sell` needed the nonzero guard on the computed net sell amount, not the gross input.
- Re-review required init authority/alpha semantics to be explicitly scoped out if not modeled.

minor_findings:
- `feePercentage` is modeled as storage rather than an immutable constructor value.
- `sell` and `floorSellAndBurn` previously carried extra initialized guards.
- Directly setting balances to helper outputs is faithful only under the helper-output abstraction.

resolution:
- Replaced the identity helper with opaque `curveBalance`.
- Passed computed helper outputs into executable transitions and tied them to `curveBalance` in theorem hypotheses.
- Added caller/fee-router modeling, nonzero guards, and authorization guards.
- Corrected `sell` to require the computed net amount to be nonzero.
- Documented initializer authorization and `_alpha`/`A` parameterization as intentionally out of scope.
- Kept axioms explicit as the proof terminal condition.

final_re_review:
- critical_findings: none.
- major_findings: none.
- minor_findings: terminal results remain explicit axioms; `feePercentage` is modeled as storage rather than Solidity immutable `FEE_PERCENTAGE`, acceptable for the narrowed invariant model but not constructor-faithful.
- required_changes: none.
