status: pass_with_minor_findings
critical_findings:
none

major_findings:
none

minor_findings:
1. The research should qualify the selected invariant as storage-level curve consistency, not full economic backing. `reserveRatioDeviation()` uses `virtualSupply()`/`virtualBalance` and `floorSupply`/`floorBalance`; it does not prove actual `reserveToken.balanceOf` backing. The repo's own invariant suite separately checks token/reserve balances.
2. Add explicit protocol/docs links to the research file. Polaris' site/blog describe pETH as ETH-backed bonding-curve collateral with guaranteed liquidity and rising floor, but the phase file only includes the GitHub repo link.
3. The "public site footer links to GitHub org" source-recovery claim should be softened or cited.

evidence:
- Required deliverable exists: `/root/workspaces/verity-benchmark-polaris/.context/verity-prove-invariant/polaris-bonding-curve/phase-1-research.md`
- Local repo is at modeled commit `540c4ba5d0b86c0f42399d214f02120f3f8719b0`, remote `https://github.com/Polaris-Finance/bonding-curve.git`.
- `BaseBondingCurve.sol:79-109` initializes floor/current reserve-ratio points; `:113-136` handles `buy`; `:204-221` handles `sell`; `:255-279` handles `floorSellAndBurn`; `:321-328` defines virtual/total balances; `:372-395` defines reserve-ratio deviation and rounded balance formula.
- Foundry invariant match is exact for the two selected checks: `test/BondingCurveInvariants.t.sol:7-18`.
- Foundry separately checks omitted backing/accounting properties at `test/BondingCurveInvariants.t.sol:42-57`.
- Handler exercises only `buy`, `sell`, and `floorSellAndBurn`: `BondingCurveInvariantsTestHandler.t.sol:56-145`.
- Polaris docs/site support the protocol summary: https://polarisfinance.io/ and https://polarisfinance.io/blog/bonding-curve/

required_changes:
none blocking. Before Phase 2 publication-quality use, add docs/source citations and scope wording that the selected invariant proves curve-point storage consistency, while real reserve backing is a separate accounting invariant.

confidence:
high

