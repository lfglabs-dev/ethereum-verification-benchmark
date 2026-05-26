# Phase 4 - Article

Article repository: `https://github.com/lfglabs-dev/lfglabs.dev`

Branch: `polaris-bonding-curve-case-study`

Files:

- `pages/research/polaris-bonding-curve-reserve-ratio.jsx`
- `components/research/PolarisBondingCurveGuarantee.jsx`
- `data/research.js`
- `public/images/logos/polaris.svg`

The article presents the Polaris reserve-ratio guarantee in plain English and
as math matching `Specs.lean`:

- `virtualBalance = curveBalance(virtualSupply)`
- `floorBalance = curveBalance(floorSupply)`

Proof status is stated as an AXIOM terminal result. The article does not claim
a fully closed proof of PRB/ABDK fixed-point exponentiation, reserve-token
custody, external transfers, or ERC20 per-account accounting.

Review findings were resolved:

- The verification command clones the benchmark branch
  `polaris-bonding-curve-reserve-ratio`.
- The top guarantee sentence now qualifies the claim with the AXIOM terminal
  assumptions before readers reach the proof-status section.

Build:

```bash
npm run build
```

Result: success.
