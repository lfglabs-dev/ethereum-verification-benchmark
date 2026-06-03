status: pass_with_minor_findings

superseded_note:
- This report reviewed the earlier AXIOM-terminal branch state. Later post-axiom-elimination work removed the custom Lean axiom and replaced it with explicit helper-output preconditions. The PRB/ABDK pow, rounding, custody, and solvency scope limitations in this report still apply.

critical_findings:
- None.

major_findings:
- This is not a proof of the PRB/ABDK reserve formula. The core curve math is abstracted behind `curveBalance` and the single axiom `trustedCurveHelperOutput_correct`. That is honest if published as the trust boundary, but it means the hardest numerical part is trusted, not verified.
- The executable model takes computed helper balances as inputs. The proof verifies that each transition stores a trusted helper output for the intended supply point; it does not prove the Solidity helper itself computes that output.

minor_findings:
- Generated task files under `Benchmark/Generated/Polaris/BondingCurve/Tasks` still contain `exact ?_` holes and YAML task status is `open`; these are challenge stubs, not the built proof target.
- Some arithmetic hypotheses are redundant or proof-shaping, e.g. both `hNetLeTotalSupply` and `hNetValLeTotalSupply`, and unused `_hMintNoOverflow`. They do not appear circular, but they should be described as successful-path checked-arithmetic assumptions.

evidence:
- `rg "axiom|sorry|admit" ...` found only `trustedCurveHelperOutput_correct` as a Lean axiom in `Benchmark/Cases/Polaris/BondingCurve/Proofs.lean`; no `sorry` or `admit` in the requested case/proof paths.
- `lake build Benchmark.Cases.Polaris.BondingCurve.Proofs` completed successfully.
- All four operation claims are Lean theorems in current `Proofs.lean`: `init_reserve_ratio_zero`, `buy_preserves_reserve_ratio_zero`, `sell_preserves_reserve_ratio_zero`, and `floorSellAndBurn_preserves_reserve_ratio_zero`.
- The invariant is `virtualBalance = curveBalance virtualSupply` and `floorBalance = curveBalance floorSupply`, not a direct proof of the closed-form reserve equation.
- The proof is not tautological in the storage/accounting part: it proves post-state supply identities for init, buy, sell, and floorSellAndBurn, including sell net burn and floor fee burn effects.
- The axiom is narrow but central: it converts `trustedCurveHelperOutput supply reserve` into `reserve = curveBalance supply`. It does not itself assert the whole post-state invariant, but it does assume correctness of the helper output against the abstract curve.

required_changes:
- Do not market this as a full formal verification of Polaris bonding-curve math.
- Explicitly document the trust boundary: PRB/ABDK fixed-point exponentiation, rounding, reserve-token custody, ERC20 per-account accounting, external transfers, init authority, and parameter validation are not verified here.

confidence:
- High. The current proof has real value for operation-level curve-point accounting under the helper abstraction, but it does not verify the actual fixed-point reserve math or full protocol solvency/custody behavior.
