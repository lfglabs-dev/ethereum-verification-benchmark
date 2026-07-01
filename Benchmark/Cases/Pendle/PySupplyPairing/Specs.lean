import Verity.Specs.Common
import Benchmark.Cases.Pendle.PySupplyPairing.Contract

namespace Benchmark.Cases.Pendle.PySupplyPairing

open Verity
open Verity.EVM.Uint256

def ytSupply (s : ContractState) : Uint256 :=
  s.storage 0

def ptSupply (s : ContractState) : Uint256 :=
  s.storage 1

def ytBalanceOf (s : ContractState) (account : Address) : Uint256 :=
  s.storageMap 2 account

def ptBalanceOf (s : ContractState) (account : Address) : Uint256 :=
  s.storageMap 3 account

def syReserveOf (s : ContractState) : Uint256 :=
  s.storage 4

def syBalanceOf (s : ContractState) : Uint256 :=
  s.storage 5

def pyIndexStoredOf (s : ContractState) : Uint256 :=
  s.storage 6

def exchangeRateOf (s : ContractState) : Uint256 :=
  s.storage 7

def expiredFlagOf (s : ContractState) : Uint256 :=
  s.storage 8

def currentIndexOf (s : ContractState) : Uint256 :=
  maxUint (exchangeRateOf s) (pyIndexStoredOf s)

def floatingSyOf (s : ContractState) : Uint256 :=
  sub (syBalanceOf s) (syReserveOf s)

def mintPYAmountOf (s : ContractState) : Uint256 :=
  syToAsset (currentIndexOf s) (floatingSyOf s)

def redeemPYAmountOf (s : ContractState) : Uint256 :=
  pyToRedeem (expiredFlagOf s) (ptBalanceOf s s.thisAddress) (ytBalanceOf s s.thisAddress)

def redeemPYSyOutOf (s : ContractState) : Uint256 :=
  assetToSy (currentIndexOf s) (redeemPYAmountOf s)

def supplyPairing (s : ContractState) : Prop :=
  ytSupply s = ptSupply s

/--
Successful `mintPY` increments YT and PT supply, and the two receiver balances,
by the exact `amountPYOut` computed from floating SY and the current PY index.
-/
def mint_py_mints_equal_amount_spec
    (receiverPT receiverYT : Address) (s s' : ContractState) : Prop :=
  let amountPYOut := mintPYAmountOf s
  ytSupply s' = add (ytSupply s) amountPYOut ∧
  ptSupply s' = add (ptSupply s) amountPYOut ∧
  ytBalanceOf s' receiverYT = add (ytBalanceOf s receiverYT) amountPYOut ∧
  ptBalanceOf s' receiverPT = add (ptBalanceOf s receiverPT) amountPYOut

/--
Successful `mintPY` preserves PT/YT total-supply pairing.

If the paired token supplies were equal before a successful mint, they remain
equal afterward because `_mintPY` mints the same `amountPYOut` to YT and PT.
-/
def mint_py_preserves_supply_pairing_spec (s s' : ContractState) : Prop :=
  supplyPairing s → supplyPairing s'

/--
Successful pre-expiry `redeemPY` burns the exact `amountPYToRedeem` from both
the PT and YT supplies and from the contract's own PT/YT balances.
-/
def redeem_py_pre_expiry_burns_equal_amount_spec (s s' : ContractState) : Prop :=
  expiredFlagOf s = 0 →
  let amountPYToRedeem := redeemPYAmountOf s
  ytSupply s' = sub (ytSupply s) amountPYToRedeem ∧
  ptSupply s' = sub (ptSupply s) amountPYToRedeem ∧
  ytBalanceOf s' s.thisAddress = sub (ytBalanceOf s s.thisAddress) amountPYToRedeem ∧
  ptBalanceOf s' s.thisAddress = sub (ptBalanceOf s s.thisAddress) amountPYToRedeem

/--
Successful pre-expiry `redeemPY` preserves PT/YT total-supply pairing.

The pre-expiry branch burns the same `amountPYToRedeem` from PT and YT. This
spec intentionally excludes post-expiry because Pendle stops burning YT after
maturity.
-/
def redeem_py_pre_expiry_preserves_supply_pairing_spec (s s' : ContractState) : Prop :=
  expiredFlagOf s = 0 → supplyPairing s → supplyPairing s'

end Benchmark.Cases.Pendle.PySupplyPairing
