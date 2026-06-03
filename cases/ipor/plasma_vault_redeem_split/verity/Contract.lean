import Mathlib.Data.Nat.Basic

/-!
Minimal arithmetic model of IPOR PlasmaVault redeem fee behavior.

Simplifications:
* This model keeps only `totalAssets`, `totalSupply`, virtual-share offset, and
  the public fee-charging redeem transition. Token transfers, access control,
  release queues, withdraw, request redemption, and market accounting are
  intentionally outside this case.
* Arithmetic is modeled over `Nat`, not `Uint256`. Overflow is excluded by the
  intended theorem preconditions in `Specs.lean`.
* The model uses the nonzero-supply conversion branch because a successful
  public redeem with existing shares is the modeled path.
* The Solidity zero-share revert is abstracted into the successful-path boundary;
  allowing a zero-share no-op does not affect the virtualized-PPS theorem.
* The model preserves the load-bearing PlasmaVault behavior: redeem burns all
  requested shares, pays assets for `shares - feeShares`, and keeps the fee value
  inside vault assets.
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

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
