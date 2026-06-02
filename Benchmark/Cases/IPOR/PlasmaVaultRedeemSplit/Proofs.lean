import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Specs

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

theorem old_split_bound_under_no_recapture
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) :
    old_split_bound_under_no_recapture_spec s1 s2 feeRate roundingSlack s m := by
  intro h
  exact h

/-!
This is the non-tautological form we want to discharge in a Lean-enabled
environment. It replaces the old unconditional target with an explicit
`splitAdvantage <= roundingSlack` assumption. For deployed PlasmaVault, that
assumption is false for `roundingSlack = 1` in the handoff counterexample.
-/
theorem old_split_bound_under_bounded_advantage
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) :
    old_split_bound_under_bounded_advantage_spec s1 s2 feeRate roundingSlack s m := by
  intro h
  unfold boundedSplitAdvantageAssumption oldBound splitAdvantage at *
  exact (Nat.le_add_of_sub_le h).trans_eq (Nat.add_comm roundingSlack (combinedPayout s1 s2 feeRate s m))

theorem fee_payout_bounded_by_fee_free
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) :
    fee_payout_bounded_by_fee_free_spec amountShares feeRate s m := by
  intro _hFee
  unfold redeemPayout feeFreePayout convertToAssets
  exact Nat.div_le_div_right
    (Nat.mul_le_mul_right (s.assets + 1) (Nat.sub_le amountShares (feeShares amountShares feeRate)))

/-!
`redeem_preserves_pps` is the main arithmetic proof obligation:

  payout = floor((amountShares - feeShares) * (A + 1) / (T + m))
  A'     = A - payout
  T'     = T - amountShares

prove:

  (A' + 1) * (T + m) >= (A + 1) * (T' + m)

The proof follows from `payout * (T + m) <= amountShares * (A + 1)`.
It is left as the next theorem-prover task because the remaining work is the
natural-number subtraction algebra around the post-redeem state.
-/
theorem redeem_preserves_pps
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) :
    redeem_preserves_pps_spec amountShares feeRate s m := by
  sorry

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
