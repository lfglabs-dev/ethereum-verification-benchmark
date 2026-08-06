# Code4rena data refresh, August 2026

## Window

This refresh preserves the benchmark's existing structure, proof-only track, scoring, harness, and verification policy. It only adds new cases and tasks.

The initial collection window is the three months ending 2026-08-06, inclusive: 2026-05-06 through 2026-08-06. Code4rena published four final reports in that window:

| Report | Published | Scope | Decision |
|---|---:|---|---|
| [Jupiter Lend](https://code4rena.com/reports/2026-02-jupiter-lend) | 2026-07-11 | Solana program | Excluded: outside the Ethereum/Solidity benchmark scope |
| [Monetrix](https://code4rena.com/reports/2026-04-monetrix) | 2026-05-26 | Solidity, HyperEVM | Included |
| [Olas](https://code4rena.com/reports/2026-01-olas) | 2026-05-18 | Solidity, EVM | Included |
| [LayerZero Stellar Endpoint](https://code4rena.com/reports/2026-04-layerzero-stellar-endpoint) | 2026-05-06 | Rust, Stellar | Excluded: outside the Ethereum/Solidity benchmark scope |

The two eligible reports contain 24 accepted High/Medium findings in total, so the collection did not need to extend to six months.

## Added benchmark data

### Monetrix M-01: PM borrow accounting

Pinned contest source: [`code-423n4/2026-04-monetrix@3d94be1`](https://github.com/code-423n4/2026-04-monetrix/tree/3d94be1361ca01d959f9165a78f0d75c5657fe3e)

Affected source:

- `src/core/PrecompileReader.sol::suppliedBalance`
- `src/core/MonetrixAccountant.sol::_readL1Backing`
- `surplus`, `distributableSurplus`, and settlement Gate 3

Added case: `monetrix/pm_borrow_accounting`

Added tasks:

1. `supplied_balance_returns_supply`
2. `reported_surplus_overstates_by_borrow`
3. `phantom_surplus_gate_witness`

The model captures the accepted finding's root cause: the decoded PM state exposes supply while the accountant omits borrow liabilities, allowing reported surplus to exceed net surplus.

### Olas H-11: rejected TWAP update corruption

Pinned source: [`autonolas-tokenomics@bbec5ac`](https://github.com/valory-xyz/autonolas-tokenomics/tree/bbec5ac12721a62672fb7a5ffba5c40f5a46d8cb)

Affected source: `contracts/oracles/BalancerPriceOracle.sol::updatePrice`

Added case: `olas/balancer_rejected_update`

Added tasks:

1. `rejected_update_preserves_metadata`
2. `rejected_update_mutates_cumulative`
3. `repeated_rejection_double_counts`
4. `rejected_update_corruption_witness`

The model captures the source write ordering: a rejected update persists `cumulativePrice`, leaves `lastUpdated` unchanged, and causes a later call to count the earlier elapsed interval again.

### Olas H-02: dead V3 deviation guard

Pinned source: [`autonolas-tokenomics@bbec5ac`](https://github.com/valory-xyz/autonolas-tokenomics/tree/bbec5ac12721a62672fb7a5ffba5c40f5a46d8cb)

Affected source:

- `contracts/pol/LiquidityManagerCore.sol::getTwapFromOracle`
- `contracts/pol/LiquidityManagerCore.sol::checkPoolAndGetCenterPrice`

Added case: `olas/v3_dead_deviation_guard`

Added tasks:

1. `normal_path_deviation_is_zero`
2. `normal_path_returns_twap_center`
3. `normal_path_ignores_spot`
4. `dead_deviation_guard_accepts`

The model captures the successful-oracle path where the named return variable containing spot sqrt price is overwritten by TWAP sqrt price. The function consequently compares TWAP-derived price with itself, making deviation zero and the guard independent of spot price.

## Net change

- 2 new protocol families
- 2 pinned Code4rena source snapshots
- 3 active benchmark cases
- 11 proof-only tasks
- No scoring, harness, schema, or existing-case changes
