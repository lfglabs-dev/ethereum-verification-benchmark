import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Contract

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

/-!
The original target,

  splitPayout <= combinedPayout + 1

is false for the real redeem transition because fee value is retained in assets
while the redeemer may still hold shares for later tranches. The specs below
separate the two usable paths:

1. prove the real safety statement, PPS non-decrease;
2. state the old split bound only under an explicit no-recapture assumption.
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

/-!
This is the explicit assumption boundary that lets the old verification finish
without pretending the counterexample disappeared.

`boundedSplitAdvantageAssumption` says: for the chosen partition, the total
split advantage, including retained-fee PPS recapture, is already bounded by the
supplied slack.

For the real PlasmaVault code this is not generally true with `roundingSlack = 1`.
It can be justified only by an external precondition, for example:
* the model intentionally freezes `assets/shares` between tranches to study only
  fee-share floor rounding;
* a protocol-level minimum redeem / fee policy makes the remaining recapture
  economically irrelevant;
* the proof target is explicitly conditional on this bound.
-/
def boundedSplitAdvantageAssumption
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  splitAdvantage s1 s2 feeRate s m <= roundingSlack

def old_split_bound_under_no_recapture_spec
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  oldBound s1 s2 feeRate roundingSlack s m →
    oldBound s1 s2 feeRate roundingSlack s m

def old_split_bound_under_bounded_advantage_spec
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  boundedSplitAdvantageAssumption s1 s2 feeRate roundingSlack s m →
    oldBound s1 s2 feeRate roundingSlack s m

def retained_fee_recapture_bounded_spec
    (s1 s2 feeRate recaptureSlack : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  retainedFeeRecapture s1 s2 feeRate s m <= recaptureSlack

/-!
Recommended terminal FV claim for this case.

The old split-fairness invariant is false, but redeem still preserves/increases
PPS under the exact burn-all-shares/pay-net-assets semantics. Therefore the
formal result should be framed as "no remaining-holder principal dilution", with
fee-fairness handled as a separate design property.
-/
def final_security_claim
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  redeem_preserves_pps_spec amountShares feeRate s m

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
