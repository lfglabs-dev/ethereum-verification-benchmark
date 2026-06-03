Model layout:
- `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Contract.lean`
- `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Specs.lean`
- `Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Proofs.lean`
- generated tasks under `Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks`
- metadata under `cases/ipor/plasma_vault_redeem_split`

The model is intentionally small. It preserves the accounting that matters for
the theorem:
- `assets`
- `shares`
- virtual offset `m`
- fee shares
- `convertToAssets`
- `redeemPayout`
- post-redeem assets and supply

Removed from the benchmark task surface:
- old split-bound theorem
- bounded split-advantage assumption
- generated old-bound task

Reason: those artifacts describe a rejected fairness target, not the final
security theorem.
