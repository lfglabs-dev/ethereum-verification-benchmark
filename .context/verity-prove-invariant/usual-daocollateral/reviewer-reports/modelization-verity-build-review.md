# Modelization, Verity, And Build Review

status: fixed

critical_findings: none

major_findings:
- Reviewers flagged modular Uint256 arithmetic where Solidity 0.8 and OpenZeppelin `Math.mulDiv` would revert or use full precision.
- Reviewers flagged missing treasury collateral sufficiency, fee/CBR storage bounds, nonzero quote, and uint128 swap amount boundary.
- Build reviewer found regenerated metadata was stale and `generate_metadata.py --check` is not a real check mode.

resolution:
- Kept the executable Verity model focused, and moved Solidity-success boundaries into theorem/task preconditions because the `verity_contract` macro does not support the required Prop/decide guards in contract bodies.
- Updated mirrored `cases/usual/dao_collateral/verity` files, generated task placeholders, YAML abstraction notes, `REPORT.md`, and `benchmark-inventory.json`.
- Ran manifest validation and targeted Lean builds successfully.

evidence:
- `python3 scripts/validate_manifests.py` passes: 19 family, 21 implementation, 20 case, 113 task manifests.
- `lake build Benchmark.Cases.Usual.DaoCollateral.Contract`, `Specs`, `Proofs`, and `Compile` pass.

confidence: high
