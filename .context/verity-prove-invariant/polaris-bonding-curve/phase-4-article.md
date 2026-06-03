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

- `virtualBalance = curveBalanceAt(state, virtualSupply)`
- `floorBalance = curveBalanceAt(state, floorSupply)`

Proof status is stated as a zero-axiom proof under explicit raw pow-output
preconditions. The article does not claim a fully closed proof of PRB/ABDK
fixed-point exponentiation, reserve-token custody, external transfers, or ERC20
per-account accounting.

Review findings were resolved:

- The verification command clones the benchmark branch
  `polaris-bonding-curve-reserve-ratio`.
- The top guarantee sentence now states the reserve equation as the transition
  conclusion, while the proof-status section names the raw pow boundary.

Build:

```bash
npm run build
```

Result: success.
