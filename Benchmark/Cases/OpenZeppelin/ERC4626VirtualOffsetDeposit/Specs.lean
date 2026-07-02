import Verity.Specs.Common
import Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit.Contract

namespace Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def previewDeposit (assets : Uint256) (s : ContractState) : Uint256 :=
  previewDepositAmount assets (s.storage 0) (s.storage 1)

def previewRedeem (shares : Uint256) (s : ContractState) : Uint256 :=
  previewRedeemAmount shares (s.storage 0) (s.storage 1)

/-- Ceiling of the assets backing a single share at the current exchange rate. -/
def oneShareAssetsUp (s : ContractState) : Uint256 :=
  ceilDiv (add (s.storage 0) virtualAssets) (add (s.storage 1) virtualShares)

/-- Direct asset donation to the vault: raises `totalAssets` without minting shares. -/
def donate (donation : Uint256) (s : ContractState) : ContractState :=
  s.writeSlot 0 (add (s.storage 0) donation)

def deposit_sets_totalAssets_spec
    (assets : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 0 = add (s.storage 0) assets

def deposit_sets_totalShares_spec
    (assets : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 1 = add (s.storage 1) (previewDeposit assets s)

def previewDeposit_rounds_down_spec
    (assets : Uint256) (s : ContractState) : Prop :=
  (previewDeposit assets s : Nat) * ((add (s.storage 0) virtualAssets : Uint256) : Nat)
    <= (assets : Nat) * ((add (s.storage 1) virtualShares : Uint256) : Nat)

def positive_deposit_mints_positive_shares_under_rate_bound_spec
    (assets : Uint256) (s : ContractState) : Prop :=
  0 < (previewDeposit assets s : Nat)

def deposit_redeem_round_trip_bound_spec
    (assets : Uint256) (s : ContractState) : Prop :=
  (previewRedeem (previewDeposit assets s) s : Nat) <= (assets : Nat) ∧
  (assets : Nat) - (previewRedeem (previewDeposit assets s) s : Nat)
    <= (oneShareAssetsUp s : Nat)

def share_price_monotone_under_donation_spec
    (shares donation : Uint256) (s : ContractState) : Prop :=
  (previewRedeem shares s : Nat) <= (previewRedeem shares (donate donation s) : Nat)

end Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit
