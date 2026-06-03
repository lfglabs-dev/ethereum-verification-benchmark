import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Specs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

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

The proof follows from `payout * (T + m) <= amountShares * (A + 1)`,
then normalizes the natural-number subtractions introduced by the post-redeem
state update.
-/
theorem redeem_preserves_pps
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) :
    redeem_preserves_pps_spec amountShares feeRate s m := by
  intro hValid
  rcases hValid with ⟨hm, hAmountLe, _hFeeRate, _hFeeSharesLe, hPayoutLe⟩
  unfold ppsCrossNondecreasing redeem redeemPayout convertToAssets
  dsimp
  set payout :=
    (amountShares - feeShares amountShares feeRate) * (s.assets + 1) /
      (s.shares + m)
  set denominator := s.shares + m
  set numerator := s.assets + 1
  have hPayoutMul :
      payout * denominator <=
        (amountShares - feeShares amountShares feeRate) * numerator := by
    subst payout
    subst denominator
    subst numerator
    exact Nat.div_mul_le_self
      ((amountShares - feeShares amountShares feeRate) * (s.assets + 1))
      (s.shares + m)
  have hNetLe : amountShares - feeShares amountShares feeRate <= amountShares :=
    Nat.sub_le amountShares (feeShares amountShares feeRate)
  have hPayoutMulAmount : payout * denominator <= amountShares * numerator := by
    exact hPayoutMul.trans (Nat.mul_le_mul_right numerator hNetLe)
  have hPayoutLeAssets : payout <= s.assets := by
    subst payout
    exact hPayoutLe
  subst denominator
  subst numerator
  nlinarith [Nat.sub_add_cancel hPayoutLeAssets, Nat.sub_add_cancel hAmountLe,
    hPayoutMulAmount]

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
