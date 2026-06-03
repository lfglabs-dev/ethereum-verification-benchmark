status: pass_with_minor_findings
critical_findings:
none

major_findings:
none

minor_findings:
1. The Lean spec is aligned with the selected reserve-ratio invariant, but it proves the structural helper-alignment form `virtualBalance = curveBalance(virtualSupply)` and `floorBalance = curveBalance(floorSupply)`, not the literal Solidity arithmetic expression `reserveRatioDeviation(...) == 0`.
2. The invariant is meaningful for curve-state drift, but it intentionally does not cover actual reserve-token custody. Foundry also checks reserve/token balance accounting in `invariant_TokenBalances`, while the Lean spec only targets virtual/floor reserve-ratio alignment.

evidence:
- Research selects current and floor reserve-ratio deviation as the minimum useful invariant.
- Foundry asserts `reserveRatioDeviation() == 0` and `reserveRatioDeviation(floorSupply, floorBalance) == 0`: `test/BondingCurveInvariants.t.sol:7-18`.
- Solidity computes deviation from `(B_PLUS_1 * balance - left) / DECIMAL_PRECISION`, while `_getBalanceFromReserveRatio` uses rounded-up balance: `src/BaseBondingCurve.sol:376-391`.
- Lean spec expresses the invariant as equality to opaque `curveBalance`: `Benchmark/Cases/Polaris/BondingCurve/Specs.lean:20-34`.
- The model documents `curveBalance` as an abstraction of `_getBalanceFromReserveRatio`: `Benchmark/Cases/Polaris/BondingCurve/Contract.lean`.
- The selected transitions are relevant because `init`, `buy`, `sell`, and `floorSellAndBurn` update virtual/floor supply or balance around the curve helper.

required_changes:
none for invariant alignment. Recommended minor documentation tweak: phrase the Lean property as "curve-balance alignment corresponding to the Solidity zero-deviation invariant under the `curveBalance` abstraction," rather than an exact literal match.

confidence:
high

