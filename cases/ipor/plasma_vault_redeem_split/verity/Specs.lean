import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Contract

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

/-!
The original split-payout fairness target was too strong for the real redeem
transition because fee value is retained in assets while the redeemer may still
hold shares for later tranches. This case therefore proves the safety statement
that remains true for the modeled code: redeem does not decrease virtualized
conversion PPS. It also proves the one-step fee sanity bound against the
fee-free path.
-/

def validRedeemInput
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  0 < m ∧
  amountShares <= s.shares ∧
  feeRate <= WAD ∧
  feeShares amountShares feeRate <= amountShares ∧
  redeemPayout amountShares feeRate s m <= s.assets

def redeem_preserves_pps_spec
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  validRedeemInput amountShares feeRate s m →
    ppsCrossNondecreasing s (redeem amountShares feeRate s m) m

def fee_payout_bounded_by_fee_free_spec
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  feeRate <= WAD →
    redeemPayout amountShares feeRate s m <= feeFreePayout amountShares s m

def final_security_claim
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  redeem_preserves_pps_spec amountShares feeRate s m

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
