import Mathlib

/-!
Minimal arithmetic model of IPOR PlasmaVault redeem fee behavior.

Simplifications:
* This model keeps only `totalAssets`, `totalSupply`, virtual-share offset, and
  the redeem transition. Token transfers, access control, release queues, and
  market accounting are intentionally outside this case.
* Arithmetic is modeled over `Nat`, not `Uint256`. Overflow is excluded by the
  intended theorem preconditions in `Specs.lean`.
* The model preserves the load-bearing PlasmaVault behavior: redeem burns all
  requested shares, pays assets for `shares - feeShares`, and keeps the fee value
  inside vault assets. That retained value is what makes the old split-payout
  bound false.
* `m = 100` matches `DECIMALS_OFFSET = 2`.
-/

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

def WAD : Nat := 10 ^ 18

def virtualShares : Nat := 100

structure VaultState where
  assets : Nat
  shares : Nat
  deriving Repr, DecidableEq

def convertToAssets (amountShares : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  amountShares * (s.assets + 1) / (s.shares + m)

def feeShares (amountShares feeRate : Nat) : Nat :=
  amountShares * feeRate / WAD

def redeemPayout (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  convertToAssets (amountShares - feeShares amountShares feeRate) s m

def redeem (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : VaultState :=
  let payout := redeemPayout amountShares feeRate s m
  { assets := s.assets - payout
    shares := s.shares - amountShares }

def feeFreePayout (amountShares : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  convertToAssets amountShares s m

def ppsCrossNondecreasing (before after : VaultState) (m : Nat := virtualShares) : Prop :=
  (after.assets + 1) * (before.shares + m) >=
    (before.assets + 1) * (after.shares + m)

def twoStepSplitPayout
    (s1 s2 feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  let p1 := redeemPayout s1 feeRate s m
  let s' := redeem s1 feeRate s m
  p1 + redeemPayout s2 feeRate s' m

def twoStepFrozenPayout
    (s1 s2 feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  redeemPayout s1 feeRate s m + redeemPayout s2 feeRate s m

def combinedPayout
    (s1 s2 feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  redeemPayout (s1 + s2) feeRate s m

def splitAdvantage
    (s1 s2 feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  twoStepSplitPayout s1 s2 feeRate s m -
    combinedPayout s1 s2 feeRate s m

def retainedFeeRecapture
    (s1 s2 feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) : Nat :=
  twoStepSplitPayout s1 s2 feeRate s m -
    twoStepFrozenPayout s1 s2 feeRate s m

def oldBound
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) : Prop :=
  twoStepSplitPayout s1 s2 feeRate s m <=
    combinedPayout s1 s2 feeRate s m + roundingSlack

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
