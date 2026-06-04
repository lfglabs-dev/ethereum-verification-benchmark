Terminal condition: PROOF.

Reference proof module:
`Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Proofs`

Proved theorem:
- `redeem_preserves_pps`
- `fee_payout_bounded_by_fee_free`

Main theorem statement:
For a successful modeled public redeem, post-redeem virtualized conversion PPS
is non-decreasing:

```text
(A' + 1) * (T + m) >= (A + 1) * (T' + m)
```

The proof uses the floor-division bound:

```text
payout * (T + m) <= sharesToRedeem * (A + 1)
```

and normalizes the natural-number subtractions from:

```text
A' = A - payout
T' = T - sharesToRedeem
```

Validation:

```text
lake build Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Contract Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Specs Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Proofs
```

Result: passed.

No `sorry` or custom `axiom` appears in the IPOR case files.
