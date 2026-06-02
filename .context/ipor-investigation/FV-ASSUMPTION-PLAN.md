# IPOR PlasmaVault FV continuation: assumption strategy

The original invariant `splitPayout <= combinedPayout + 1` is false for the real
PlasmaVault redeem transition. Do not try to prove it unconditionally.

## What assumption can finish the old proof?

Use an explicit assumption named:

```lean
boundedSplitAdvantageAssumption s1 s2 feeRate roundingSlack s m
```

Meaning:

```text
splitAdvantage(s1,s2) <= roundingSlack
```

This is the explicit boundary marker: it records that the old theorem is
conditional on externally bounding the whole split advantage, including
retained-fee PPS recapture.

This assumption is **not true for real PlasmaVault with roundingSlack = 1**. It
can be justified only if the verification target is narrowed to one of these:

1. `assets` and `shares` are frozen between tranches, so the model studies only
   fee-share floor rounding.
2. The protocol imposes a minimum redeem / fee policy that makes retained-fee
   recapture bounded by the chosen slack.
3. The theorem is intentionally a conditional fairness theorem, not a statement
   about deployed PlasmaVault.

## What should be proved instead?

Prove `redeem_preserves_pps_spec`:

```text
(A' + 1) * (T + m) >= (A + 1) * (T' + m)
```

where:

```text
payout = floor((sharesToRedeem - feeShares) * (A + 1) / (T + m))
A' = A - payout
T' = T - sharesToRedeem
m = 100
```

This is the correct safety claim: redeem cannot reduce PPS, so remaining holders'
principal is not diluted by the split-redemption behavior.

## Files added

```text
Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Contract.lean
Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Specs.lean
Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Proofs.lean
Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Compile.lean
Benchmark/Cases/IPOR.lean
Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks/FeePayoutBoundedByFeeFree.lean
Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks/RedeemPreservesPps.lean
Benchmark/Generated/IPOR/PlasmaVaultRedeemSplit/Tasks/OldSplitBoundUnderBoundedAdvantage.lean
cases/ipor/plasma_vault_redeem_split/case.yaml
cases/ipor/plasma_vault_redeem_split/tasks/fee_payout_bounded_by_fee_free.yaml
cases/ipor/plasma_vault_redeem_split/tasks/redeem_preserves_pps.yaml
cases/ipor/plasma_vault_redeem_split/tasks/old_split_bound_under_bounded_advantage.yaml
families/ipor/family.yaml
families/ipor/implementations/ipor_fusion/implementation.yaml
```

## Build status

Checked locally:

```bash
lake build Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Compile
```

Result:

```text
Build completed successfully.
warning: Benchmark/Cases/IPOR/PlasmaVaultRedeemSplit/Proofs.lean:47:8: declaration uses 'sorry'
```

The reference proof now discharges:

```text
old_split_bound_under_bounded_advantage
fee_payout_bounded_by_fee_free
```

The proof file intentionally contains one remaining `sorry` stub for:

```text
redeem_preserves_pps
```

The remaining work is arithmetic proof repair around Nat subtraction and the
cross-multiplied PPS inequality.
