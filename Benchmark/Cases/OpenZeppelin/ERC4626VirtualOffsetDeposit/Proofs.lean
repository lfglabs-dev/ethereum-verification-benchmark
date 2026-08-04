import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Specs
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Math

private theorem deposit_slot_writes
    (assets : Uint256) (s : ContractState) :
    let s' := ((ERC4626VirtualOffsetDeposit.deposit assets).run s).snd
    s'.storage 0 = add (s.storage 0) assets ∧
    s'.storage 1 = add (s.storage 1) (previewDeposit assets s) := by
  constructor
  · simp [ERC4626VirtualOffsetDeposit.deposit,
      ERC4626VirtualOffsetDeposit.totalAssets, ERC4626VirtualOffsetDeposit.totalShares,
      getStorage, setStorage, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
      ContractResult.snd]
  · simp [ERC4626VirtualOffsetDeposit.deposit, previewDeposit, previewDepositAmount,
      virtualAssets, virtualShares, ERC4626VirtualOffsetDeposit.totalAssets,
      ERC4626VirtualOffsetDeposit.totalShares, getStorage, setStorage, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

theorem deposit_sets_totalAssets
    (assets : Uint256) (s : ContractState) :
    let s' := ((ERC4626VirtualOffsetDeposit.deposit assets).run s).snd
    deposit_sets_totalAssets_spec assets s s' := by
  unfold deposit_sets_totalAssets_spec
  exact (deposit_slot_writes assets s).1

theorem deposit_sets_totalShares
    (assets : Uint256) (s : ContractState) :
    let s' := ((ERC4626VirtualOffsetDeposit.deposit assets).run s).snd
    deposit_sets_totalShares_spec assets s s' := by
  unfold deposit_sets_totalShares_spec
  exact (deposit_slot_writes assets s).2

theorem previewDeposit_rounds_down
    (assets : Uint256) (s : ContractState)
    (hMul : (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat) <= MAX_UINT256) :
    previewDeposit_rounds_down_spec assets s := by
  unfold previewDeposit_rounds_down_spec previewDeposit previewDepositAmount
  change ((assets * add (s.storage 1) virtualShares / add (s.storage 0) virtualAssets).val *
    (add (s.storage 0) virtualAssets).val) ≤
    assets.val * (add (s.storage 1) virtualShares).val
  exact mulDivDown_mul_le assets (add (s.storage 1) virtualShares)
    (add (s.storage 0) virtualAssets) hMul

theorem positive_deposit_mints_positive_shares_under_rate_bound
    (assets : Uint256) (s : ContractState)
    (_hAssets : assets ≠ 0)
    (hDenom : add (s.storage 0) virtualAssets ≠ 0)
    (hRate : ((add (s.storage 0) virtualAssets : Uint256) : Nat)
      <= (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat))
    (hMul : (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat) <= MAX_UINT256) :
    positive_deposit_mints_positive_shares_under_rate_bound_spec assets s := by
  unfold positive_deposit_mints_positive_shares_under_rate_bound_spec previewDeposit previewDepositAmount
  change 0 < (assets * add (s.storage 1) virtualShares / add (s.storage 0) virtualAssets).val
  exact mulDivDown_pos assets (add (s.storage 1) virtualShares)
    (add (s.storage 0) virtualAssets) hDenom hRate hMul

/--
Pure natural-number rounding sandwich for the deposit→redeem round trip.

With assets-per-share denominator `An` and shares-per-asset numerator `Sn`,
depositing `a` mints `a * Sn / An` shares (floor) and redeeming them returns
`a * Sn / An * An / Sn` assets (floor). The floor/ceil sandwich shows the
round trip never overshoots and loses at most one share's worth of assets,
rounded up: `(An + Sn - 1) / Sn`.
-/
private theorem roundTrip_nat_bound (a An Sn : Nat) (hAn : 0 < An) (hSn : 0 < Sn) :
    a * Sn / An * An / Sn ≤ a ∧
    a - a * Sn / An * An / Sn ≤ (An + Sn - 1) / Sn := by
  -- floor lemma, deposit leg: (a*Sn/An) * An ≤ a*Sn
  have hFloor1 : a * Sn / An * An ≤ a * Sn := Nat.div_mul_le_self (a * Sn) An
  -- floor lemma, redeem leg: (q1*An/Sn) * Sn ≤ q1*An
  have hFloor2 : a * Sn / An * An / Sn * Sn ≤ a * Sn / An * An :=
    Nat.div_mul_le_self (a * Sn / An * An) Sn
  have hClaim1 : a * Sn / An * An / Sn ≤ a :=
    Nat.le_of_mul_le_mul_right (Nat.le_trans hFloor2 hFloor1) hSn
  refine ⟨hClaim1, ?_⟩
  -- Euclidean equations for the three divisions
  have e1 := Nat.div_add_mod (a * Sn) An
  have r1lt : a * Sn % An < An := Nat.mod_lt _ hAn
  have e2 := Nat.div_add_mod (a * Sn / An * An) Sn
  have r2lt : a * Sn / An * An % Sn < Sn := Nat.mod_lt _ hSn
  have e3 := Nat.div_add_mod (An + Sn - 1) Sn
  have r3lt : (An + Sn - 1) % Sn < Sn := Nat.mod_lt _ hSn
  -- ceil covers one full share: An ≤ Sn * q3
  have hAnLe : An ≤ Sn * ((An + Sn - 1) / Sn) := by omega
  -- orientation bridges so omega can chain the product atoms
  have hBridge : An * (a * Sn / An) = a * Sn / An * An := Nat.mul_comm _ _
  have hComm : a * Sn = Sn * a := Nat.mul_comm _ _
  have hExpand : Sn * (a * Sn / An * An / Sn + (An + Sn - 1) / Sn + 1)
      = Sn * (a * Sn / An * An / Sn) + Sn * ((An + Sn - 1) / Sn) + Sn := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  -- a*Sn = An*q1 + r1 = Sn*q2 + r2 + r1 < Sn*q2 + Sn + An ≤ Sn*(q2 + q3 + 1)
  have hLt : Sn * a < Sn * (a * Sn / An * An / Sn + (An + Sn - 1) / Sn + 1) := by
    omega
  have hFin : a < a * Sn / An * An / Sn + (An + Sn - 1) / Sn + 1 :=
    Nat.lt_of_mul_lt_mul_left hLt
  omega

theorem deposit_redeem_round_trip_bound
    (assets : Uint256) (s : ContractState)
    (hAssetsDenom : add (s.storage 0) virtualAssets ≠ 0)
    (hSharesDenom : add (s.storage 1) virtualShares ≠ 0)
    (hMul : (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat)
      <= MAX_UINT256) :
    deposit_redeem_round_trip_bound_spec assets s := by
  have hAnNe : ((add (s.storage 0) virtualAssets : Uint256) : Nat) ≠ 0 := by
    intro h
    exact hAssetsDenom (Verity.Core.Uint256.ext (by simpa using h))
  have hSnNe : ((add (s.storage 1) virtualShares : Uint256) : Nat) ≠ 0 := by
    intro h
    exact hSharesDenom (Verity.Core.Uint256.ext (by simpa using h))
  have hq1 : ((mulDivDown assets (add (s.storage 1) virtualShares)
        (add (s.storage 0) virtualAssets) : Uint256) : Nat)
      = (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat)
        / ((add (s.storage 0) virtualAssets : Uint256) : Nat) := by
    rw [mulDivDown_nat_eq _ _ _ hMul, if_neg hAnNe]
  have hMul2 : ((mulDivDown assets (add (s.storage 1) virtualShares)
        (add (s.storage 0) virtualAssets) : Uint256) : Nat)
      * ((add (s.storage 0) virtualAssets : Uint256) : Nat) <= MAX_UINT256 := by
    rw [hq1]
    exact Nat.le_trans (Nat.div_mul_le_self _ _) hMul
  have hq2 : ((mulDivDown
        (mulDivDown assets (add (s.storage 1) virtualShares) (add (s.storage 0) virtualAssets))
        (add (s.storage 0) virtualAssets) (add (s.storage 1) virtualShares) : Uint256) : Nat)
      = (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat)
          / ((add (s.storage 0) virtualAssets : Uint256) : Nat)
          * ((add (s.storage 0) virtualAssets : Uint256) : Nat)
          / ((add (s.storage 1) virtualShares : Uint256) : Nat) := by
    rw [mulDivDown_nat_eq _ _ _ hMul2, if_neg hSnNe, hq1]
  have hq3 : ((ceilDiv (add (s.storage 0) virtualAssets)
        (add (s.storage 1) virtualShares) : Uint256) : Nat)
      = (((add (s.storage 0) virtualAssets : Uint256) : Nat)
          + ((add (s.storage 1) virtualShares : Uint256) : Nat) - 1)
        / ((add (s.storage 1) virtualShares : Uint256) : Nat) :=
    ceilDiv_nat_eq _ _ hSharesDenom
  have hbound := roundTrip_nat_bound (assets : Nat)
    ((add (s.storage 0) virtualAssets : Uint256) : Nat)
    ((add (s.storage 1) virtualShares : Uint256) : Nat)
    (Nat.pos_of_ne_zero hAnNe) (Nat.pos_of_ne_zero hSnNe)
  unfold deposit_redeem_round_trip_bound_spec
  show ((mulDivDown
      (mulDivDown assets (add (s.storage 1) virtualShares) (add (s.storage 0) virtualAssets))
      (add (s.storage 0) virtualAssets) (add (s.storage 1) virtualShares) : Uint256) : Nat)
      <= (assets : Nat) ∧
    (assets : Nat) - ((mulDivDown
      (mulDivDown assets (add (s.storage 1) virtualShares) (add (s.storage 0) virtualAssets))
      (add (s.storage 0) virtualAssets) (add (s.storage 1) virtualShares) : Uint256) : Nat)
      <= ((ceilDiv (add (s.storage 0) virtualAssets)
        (add (s.storage 1) virtualShares) : Uint256) : Nat)
  rw [hq2, hq3]
  exact hbound

theorem share_price_monotone_under_donation
    (shares donation : Uint256) (s : ContractState)
    (_hOffsetShares : ((s.storage 1 : Uint256) : Nat) + (virtualShares : Nat)
      <= MAX_UINT256)
    (hDonation : ((s.storage 0 : Uint256) : Nat) + (donation : Nat) + (virtualAssets : Nat)
      <= MAX_UINT256)
    (hMul : (shares : Nat)
      * (((s.storage 0 : Uint256) : Nat) + (donation : Nat) + (virtualAssets : Nat))
      <= MAX_UINT256) :
    share_price_monotone_under_donation_spec shares donation s := by
  have hVA : (virtualAssets : Nat) = 1 := rfl
  have hMax : MAX_UINT256 = 2 ^ 256 - 1 := rfl
  rw [hVA] at hDonation hMul
  rw [hMax] at hDonation
  have hInner : ((add (s.storage 0) donation : Uint256) : Nat)
      = ((s.storage 0 : Uint256) : Nat) + (donation : Nat) :=
    add_eq_of_lt (by omega)
  have hA' : ((add (add (s.storage 0) donation) virtualAssets : Uint256) : Nat)
      = ((s.storage 0 : Uint256) : Nat) + (donation : Nat) + 1 := by
    rw [add_eq_of_lt (by rw [hInner, hVA]; omega), hInner, hVA]
  have hA : ((add (s.storage 0) virtualAssets : Uint256) : Nat)
      = ((s.storage 0 : Uint256) : Nat) + 1 := by
    rw [add_eq_of_lt (by rw [hVA]; omega), hVA]
  have hLe : ((add (s.storage 0) virtualAssets : Uint256) : Nat)
      <= ((add (add (s.storage 0) donation) virtualAssets : Uint256) : Nat) := by
    rw [hA, hA']
    omega
  have hMul' : (shares : Nat)
      * ((add (add (s.storage 0) donation) virtualAssets : Uint256) : Nat)
      <= MAX_UINT256 := by
    rw [hA']
    exact hMul
  have hs0 : (donate donation s).storage 0 = add (s.storage 0) donation := by
    simp [donate]
  have hs1 : (donate donation s).storage 1 = s.storage 1 := by
    simp [donate]
  unfold share_price_monotone_under_donation_spec previewRedeem previewRedeemAmount
  rw [hs0, hs1]
  change (shares * add (s.storage 0) virtualAssets / add (s.storage 1) virtualShares).val ≤
    (shares * add (add (s.storage 0) donation) virtualAssets /
      add (s.storage 1) virtualShares).val
  exact mulDivDown_monotone_right shares
    (add (s.storage 0) virtualAssets)
    (add (add (s.storage 0) donation) virtualAssets)
    (add (s.storage 1) virtualShares) hLe hMul'

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit
