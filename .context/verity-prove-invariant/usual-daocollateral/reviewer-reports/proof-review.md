status: pass_with_minor_findings
critical_findings:
- none
major_findings:
- none
minor_findings:
- Generated task files under `Benchmark/Generated/Usual/DaoCollateral/Tasks` still contain `exact ?_` placeholders and fail if built directly. This is documented in `phase-3-proof.md` as intentional, and task YAMLs point to hidden reference declarations in `Benchmark.Cases.Usual.DaoCollateral.Proofs`, so this is not blocking for the reference proof terminal state.
- The proof is only for the disclosed protocol slice: direct swap/redeem arithmetic with oracle values parameterized and ERC20/USD0 effects ghosted. It does not prove oracle correctness, USD0 token correctness, registry/access-control behavior, SwapperEngine/intent paths, or whole-protocol solvency.
evidence:
- `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` completed successfully.
- `rg -n "\bsorry\b|\baxiom\b|admit" Benchmark/Cases/Usual cases/usual Benchmark/Generated/Usual/DaoCollateral` returned no proof-artifact matches.
- `Benchmark/Cases/Usual/DaoCollateral/Proofs.lean` proves all five reference declarations: `swap_conservation`, `swap_value_conservation`, `redeem_fee_formula`, `redeem_return_formula`, and `redeem_conservation`.
- Specs tie swap value conservation to `expectedSwapUsdQuote`, and redeem conservation to explicit fee, net burn, CBR, oracle conversion, and treasury debit formulas.
- Standalone generated task builds for `SwapConservation` and `RedeemConservation` fail on `exact ?_`, confirming those are unsolved stubs rather than proof artifacts.
required_changes:
- none for the reference proof target.
- Optional cleanup: make generated task placeholder status explicit in case metadata/reporting so build-green claims cannot be mistaken as applying to those stub modules.
confidence:
- high
