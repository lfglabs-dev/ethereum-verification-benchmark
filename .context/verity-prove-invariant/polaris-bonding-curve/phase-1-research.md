# Phase 1 - Polaris Bonding Curve Research

## Source Recovery

The exact public repository was recovered by following Polaris' public GitHub organization link and verifying the organization repo list contains `bonding-curve`.

- Repository: https://github.com/Polaris-Finance/bonding-curve
- Commit modeled: `540c4ba5d0b86c0f42399d214f02120f3f8719b0`
- Target path: `src/BaseBondingCurve.sol`
- Math implementation paths: `src/PRBBondingCurve.sol`, `src/ABDKBondingCurve.sol`
- Test invariant path: `test/BondingCurveInvariants.t.sol`
- Public context: https://polarisfinance.io/ and https://polarisfinance.io/blog/bonding-curve/

## Protocol Summary

Polaris uses a pETH bonding curve backed by ETH-like reserve accounting. The source contract mints and burns bonding-curve ERC20 supply against a reserve-token balance according to `p = A * s^B`, with `0 < B < 1e18`. The value at risk is reserve collateral held by the curve and the fee-router floor reserve. The target functions are `init`, `buy`, `sell`, and `floorSellAndBurn`, because they are the state transitions that change virtual reserve, virtual supply, floor supply, or floor reserve. This benchmark scopes the proof to curve-point storage consistency. Actual reserve-token custody and per-account ERC20 balance accounting are separate upstream invariants.

## Candidate Invariants

1. Current reserve ratio deviation is zero: `reserveRatioDeviation(virtualSupply(), virtualBalance) == 0`.
2. Floor reserve ratio deviation is zero: `reserveRatioDeviation(floorSupply, floorBalance) == 0`.
3. Token accounting matches virtual accounting: `totalSupply() == virtualSupply() - floorSupply`.
4. Reserve accounting matches virtual accounting: contract reserve balance equals `virtualBalance - floorBalance`.

The selected invariant is the first two together. This is the minimum useful invariant because it exercises the core curve math and the fee-burn/floor transition. The Lean spec proves the curve-balance alignment corresponding to the Solidity zero-deviation invariant under the documented `curveBalance` abstraction.

## User-Proposed Invariant

The user invariant is valid and precisely matches the repo's Foundry invariant:

```solidity
assertEq(bondingCurve.reserveRatioDeviation(), 0, "Too much reserve ratio deviation");
assertEq(
    bondingCurve.reserveRatioDeviation(bondingCurve.floorSupply(), bondingCurve.floorBalance()),
    0,
    "Too much reserve ratio deviation"
);
```

It is not too weak: drift in either the current curve point or the floor point directly means virtual reserve accounting no longer matches the mathematical curve. It is not too broad if scoped to the bonding-curve operations rather than the whole pUSD/CDP system. It does not claim to prove the separate custody invariant that the actual reserve token balance equals `virtualBalance - floorBalance`.

## Translation Fidelity Audit

| Solidity construct | Path / snippet | Verity surface | Classification | Syntax or semantics risk |
| --- | --- | --- | --- | --- |
| `virtualBalance`, `floorSupply`, `floorBalance`, ERC20 `totalSupply` | `BaseBondingCurve.sol` storage | Scalar storage slots | no issue | syntax-only |
| `virtualSupply() = floorSupply + totalSupply()` | `BaseBondingCurve.sol: virtualSupply` | `virtualSupplyOf` helper | no issue | syntax-only |
| `_getBalanceFromReserveRatio(supply)` | `left = A * pow(supply, B_PLUS_1); (left + DECIMAL_PRECISION - 1) / B_PLUS_1` | `curveBalance` opaque helper | proof-gap-only | semantics risk is documented: proof assumes helper computes the same rounded reserve function |
| `buy` | sets `virtualBalance = _getBalanceFromReserveRatio(oldVirtualSupply + net + fee)` | state transition with same branch and state target | no issue except external token transfer omitted | syntax-only for invariant |
| `sell` | burns net amount, transfers the sell fee to the fee router, and sets `virtualBalance = _getBalanceFromReserveRatio(oldVirtualSupply - net)` | state transition with explicit sell fee and net burn | no issue | syntax-only |
| `floorSellAndBurn` | increases `floorSupply`, burns fee-router pETH, sets `floorBalance = _getBalanceFromReserveRatio(newFloorSupply)` | fee-burn transition preserving floor invariant after the full floor-supply change | no issue | syntax-only |
| ERC20 balances and external reserve-token transfers | `_mint`, `_burn`, `_transfer`, `safeTransfer` | omitted except aggregate total supply | proof-gap-only | outside selected reserve-ratio invariant |

## Draft Simplifications

- PRB/ABDK exponentiation and decimal fixed-point rounding are represented by `curveBalance : Uint256 -> Uint256`. This is necessary because Verity has no faithful Solidity fixed-point pow surface for PRB/ABDK in this benchmark. The invariant being proven is that all state transitions write the exact result of that reserve-function helper, so no drift is introduced by operation sequencing, fee minting, sell-fee transfer, or fee-router burns. The sell/floor-burn specs now name fee, net burn, post-sell virtual supply, and post-floor-burn supply directly; reserve equality after those supply changes is a theorem conclusion, not a premise.
- ERC20 per-account balances, allowances, `permit`, external token transfers, and access-control addresses are omitted. Aggregate `totalSupply` is kept because it determines `virtualSupply`.
- Solidity checked arithmetic is represented by successful-path hypotheses in the proof where needed.

## Proposed Verity Issues

None opened. The relevant limitation is already handled as a model simplification: fixed-point exponentiation over PRB/ABDK is outside the current practical Verity proof surface for this case.

## Supersession Note - Helper Modeling Pass

The earlier `curveBalance` helper-output abstraction has been narrowed. Current
files model `_getBalanceFromReserveRatio` through its outer arithmetic:
`(A * pow(supply, B_PLUS_1) + DECIMAL_PRECISION - 1) / B_PLUS_1`. The remaining
residual is only the raw PRB/ABDK fixed-point `pow` result, represented by
`trustedCurvePowOutput`.
